/* __builtin_dynamic_object_size (ptr, object_size_type) computation
   Copyright (C) 2021 Siddhesh Poyarekar <siddhesh@gotplt.org>

This file is part of GCC.

GCC is free software; you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation; either version 3, or (at your option)
any later version.

GCC is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with GCC; see the file COPYING3.  If not see
<http://www.gnu.org/licenses/>.  */

/* __builtin_dynamic_object_size returns richer object size information with
   the intent of improving precision of checks that depend on object sizes.  It
   is a drop-in replacement for __builtin_object_size due to having the
   following common semantics:

   * Both take the same arguments.
   * Like __builtin_object_size, __builtin_dynamic_object_size also provides an
     estimate (either lower or higher, based on the second argument) of the
     object size and not the precise object size.
   * On failure, both return either (size_t)-1 or (size_t)0 depending on the
     second byte of the TYPE argument.

   There are minor semantic differences in both builtins:

   * On success, __builtin_dynamic_object_size is more likely to return the
     closest object size, since it may return one of the following:
     - An expression that evaluates to the exact object size
     - When the exact size is not available, an expression that evaluates to
       the maximum or minimum estimate of the size of the object.  Currently
       this is a constant since the pass simplifies
       __builtin_dynamic_object_size to __builtin_object_size if it cannot
       determine a size expression.  However in future it could be a
       non-constant expression.

   See definition of collect_object_sizes_for to know what patterns are
   currently recognized.  */

#include "config.h"
#include "system.h"
#include "coretypes.h"
#include "backend.h"
#include "tree.h"
#include "gimple.h"
#include "tree-pass.h"
#include "ssa.h"
#include "gimple-pretty-print.h"
#include "fold-const.h"
#include "tree-object-size.h"
#include "gimple-fold.h"
#include "gimple-iterator.h"
#include "tree-cfg.h"
#include "stringpool.h"
#include "attribs.h"
#include "builtins.h"
#include "print-tree.h"
#include "gimplify-me.h"

struct object_size_info
{
  struct function *fun;
  int object_size_type;
  bitmap visited;
  unsigned deploop;
};

static tree alloc_object_size (const gcall *);
static tree pass_through_call (const gcall *);
static void collect_object_sizes_for (struct object_size_info *, tree);

/* object_sizes[0] is upper bound for number of bytes till the end of
   the object.
   object_sizes[1] is upper bound for number of bytes till the end of
   the subobject (innermost array or field with address taken).
   object_sizes[2] is lower bound for number of bytes till the end of
   the object and object_sizes[3] lower bound for subobject.

   These are merely SSA names of the sizes.  The actual size expressions are in
   object_size_exprs and they need not be SSA.  */
static vec<tree> object_sizes[4];

/* The actual size expressions, indexed by the object SSA names.  */
static vec<tree *>object_size_exprs[4];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[4];

/* Compute __builtin_dynamic_object_size for CALL, which is a GIMPLE_CALL.
   Handles calls to functions declared with attribute alloc_size.
   OBJECT_SIZE_TYPE is the second argument from __builtin_dynamic_object_size.
   If unknown, return NULL_TREE.  */

static tree
alloc_object_size (const gcall *call)
{
  gcc_assert (is_gimple_call (call));

  tree calltype;
  tree callfn = gimple_call_fndecl (call);

  if (callfn)
    calltype = TREE_TYPE (callfn);
  else
    calltype = gimple_call_fntype (call);

  if (!calltype)
    return NULL_TREE;

  /* Set to positions of alloc_size arguments.  */
  int arg1 = -1, arg2 = -1;
  tree alloc_size = lookup_attribute ("alloc_size",
				      TYPE_ATTRIBUTES (calltype));
  if (alloc_size && TREE_VALUE (alloc_size))
    {
      tree p = TREE_VALUE (alloc_size);

      arg1 = TREE_INT_CST_LOW (TREE_VALUE (p))-1;
      if (TREE_CHAIN (p))
	arg2 = TREE_INT_CST_LOW (TREE_VALUE (TREE_CHAIN (p)))-1;
    }
  else if (gimple_call_builtin_p (call, BUILT_IN_NORMAL)
	   && callfn && ALLOCA_FUNCTION_CODE_P (DECL_FUNCTION_CODE (callfn)))
    arg1 = 0;

  if (arg1 < 0 || arg1 >= (int)gimple_call_num_args (call)
      || arg2 >= (int)gimple_call_num_args (call))
    return NULL_TREE;

  if (arg2 >= 0)
    {
      tree ret = fold_build2 (MULT_EXPR, sizetype,
			      fold_convert (sizetype, gimple_call_arg (call,
								       arg1)),
			      fold_convert (sizetype, gimple_call_arg (call,
								       arg2)));
      return STRIP_NOPS (ret);
    }
  else if (arg1 >= 0)
    {
      tree ret = fold_convert (sizetype, gimple_call_arg (call, arg1));
      return STRIP_NOPS (ret);
    }

  return NULL_TREE;
}


/* If object size is propagated from one of function's arguments directly
   to its return value, return that argument for GIMPLE_CALL statement CALL.
   Otherwise return NULL.  */

static tree
pass_through_call (const gcall *call)
{
  unsigned rf = gimple_call_return_flags (call);
  if (rf & ERF_RETURNS_ARG)
    {
      unsigned argnum = rf & ERF_RETURN_ARG_MASK;
      if (argnum < gimple_call_num_args (call))
	return gimple_call_arg (call, argnum);
    }

  /* __builtin_assume_aligned is intentionally not marked RET1.  */
  if (gimple_call_builtin_p (call, BUILT_IN_ASSUME_ALIGNED))
    return gimple_call_arg (call, 0);

  return NULL_TREE;
}

static void
emit_size_stmts (gimple *stmt, tree size_ssa, tree size_expr)
{
  gimple_seq seq = NULL;

  if (!is_gimple_variable (size_expr))
    size_expr = force_gimple_operand (size_expr, &seq, true, NULL);

  gassign *assign = gimple_build_assign (size_ssa, size_expr);
  gimple_seq_add_stmt (&seq, assign);

  /* Define object size right after the object is defined.  */
  gimple_stmt_iterator i = gsi_for_stmt (stmt);
  gsi_insert_seq_after (&i, seq, GSI_CONTINUE_LINKING);
}

static void
emit_size_phi_stmts (gimple *stmt, tree size_ssa, tree *sizes)
{
  gphi *newphi = create_phi_node (size_ssa, gimple_bb (stmt));
  gphi *obj_phi =  as_a <gphi *> (stmt);

  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      if (!is_gimple_variable (sizes[i]))
	{
	  gimple_seq seq;
	  edge e = gimple_phi_arg_edge (obj_phi, i);
	  sizes[i] = force_gimple_operand (sizes[i], &seq, true, NULL);

	  /* Put the size definition before the last statement of the source
	     block of the PHI edge.  This ensures that any branches at the end
	     of the source block remain the last statement.  We are OK even if
	     the last statement is the definition of the object since it will
	     succeed any definitions that contribute to its size and the size
	     expression will succeed them too.  */
	  gimple_stmt_iterator gsi = gsi_last_bb (e->src);
	  gsi_insert_seq_before (&gsi, seq, GSI_CONTINUE_LINKING);
	}

      add_phi_arg (newphi, sizes[i],
		   gimple_phi_arg_edge (obj_phi, i),
		   gimple_phi_arg_location (obj_phi, i));
    }
}

static void
eval_size_expr (tree var, tree size, tree *size_expr)
{
  if (size_expr != NULL)
    {
      gcc_assert (*size_expr != error_mark_node);

      gimple *stmt = SSA_NAME_DEF_STMT (var);

      if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  emit_size_phi_stmts (stmt, size, size_expr);
	  delete[] size_expr;
	}
      else
	{
	  emit_size_stmts (stmt, size, *size_expr);
	  delete size_expr;
	}
    }
}

static void
gimplify_size_exprs (object_size_info *osi, tree ptr)
{
  bitmap_iterator bi;
  unsigned i;

  /* If the size lookup was not successful and we were left with unresolved
     loop dependencies, then invalidate all size computations.  This is
     suboptimal and should eventually try to remove only size expressions that
     depend on the unresolved dependencies, but it's unclear whether
     maintaining the extra state to manage that is worthwhile.  */
  if (object_sizes[osi->object_size_type][SSA_NAME_VERSION (ptr)] == NULL_TREE
      && osi->deploop)
    {
      for (int object_size_type = 0; object_size_type <= 3; object_size_type++)
	{
	  EXECUTE_IF_SET_IN_BITMAP (computed[object_size_type], 0, i, bi)
	    {
	      release_ssa_name (object_sizes[object_size_type][i]);
	      if (gimple_code (SSA_NAME_DEF_STMT (ssa_name (i))) == GIMPLE_PHI
		  && object_size_exprs[object_size_type][i])
		delete [] object_size_exprs[object_size_type][i];
	      else
		delete object_size_exprs[object_size_type][i];
	      object_size_exprs[object_size_type][i] = NULL;
	    }
	  bitmap_clear (computed[object_size_type]);
	}
      return;
    }

  /* Gimplify and emit code for all computed size expressions.  */
  for (int object_size_type = 0; object_size_type <= 3; object_size_type++)
    EXECUTE_IF_SET_IN_BITMAP (computed[object_size_type], 0, i, bi)
      {
	eval_size_expr (ssa_name (i), object_sizes[object_size_type][i],
			object_size_exprs[object_size_type][i]);
	object_size_exprs[object_size_type][i] = NULL;
      }
}

/* Compute object size estimate for PTR and set *PSIZE to the resulting value.
   OBJECT_SIZE_TYPE is the second argument to __builtin_dynamic_object_size.
   Returns true on success and false when the object size could not be
   determined.  */

bool
compute_builtin_dyn_object_size (tree ptr, int object_size_type, tree *psize,
				 struct function *fun)
{
  gcc_assert (object_size_type >= 0 && object_size_type <= 3);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = NULL_TREE;

  if (TREE_CODE (ptr) != SSA_NAME
      || !POINTER_TYPE_P (TREE_TYPE (ptr)))
      return false;

  if (computed[object_size_type] == NULL)
    return false;

  if (bitmap_bit_p (computed[object_size_type], SSA_NAME_VERSION (ptr)))
    goto out;

  struct object_size_info osi;
  bitmap_iterator bi;
  unsigned int i;

  if (num_ssa_names > object_sizes[object_size_type].length ())
    {
      object_sizes[object_size_type].safe_grow (num_ssa_names, true);
      object_size_exprs[object_size_type].safe_grow (num_ssa_names, true);
    }
  if (dump_file)
    {
      fprintf (dump_file, "Computing %s dynamic %sobject size for ",
	       (object_size_type & 2) ? "minimum" : "maximum",
	       (object_size_type & 1) ? "sub" : "");
      print_generic_expr (dump_file, ptr, dump_flags);
      fprintf (dump_file, ":\n");
    }

  osi.visited = BITMAP_ALLOC (NULL);
  osi.deploop = 0;
  osi.object_size_type = object_size_type;
  osi.fun = fun != NULL ? fun : cfun;

  collect_object_sizes_for (&osi, ptr);
  gimplify_size_exprs (&osi, ptr);

  /* Debugging dumps.  */
  if (dump_file)
    {
      EXECUTE_IF_SET_IN_BITMAP (osi.visited, 0, i, bi)
	if (object_sizes[object_size_type][i] != NULL_TREE)
	  {
	    print_generic_expr (dump_file, ssa_name (i),
				dump_flags);
	    fprintf (dump_file, ": %s dynamic %sobject size ",
		     (object_size_type & 2) ? "minimum" : "maximum",
		     (object_size_type & 1) ? "sub" : "");
	    print_generic_expr (dump_file, object_sizes[object_size_type][i],
				dump_flags);
	    fprintf (dump_file, ":\n");
	  }
    }

  BITMAP_FREE (osi.visited);

out:
  *psize = object_sizes[object_size_type][SSA_NAME_VERSION (ptr)];
  return *psize != NULL_TREE;
}

static void
maybe_update_dependency_loop (struct object_size_info *osi, unsigned name,
			      tree sz)
{
  if (sz == error_mark_node)
    osi->deploop++;
  else if (object_sizes[osi->object_size_type][name]
	   && (*object_size_exprs[osi->object_size_type][name]
	       == error_mark_node))
    osi->deploop--;
}

/* Add object size to the cache so that it can be reused.  */

static void
cache_object_size (struct object_size_info *osi, unsigned name, tree *sz)
{
  int object_size_type = osi->object_size_type;
  struct function *fun = osi->fun;

  gcc_assert (sz);

  maybe_update_dependency_loop (osi, name, *sz);

  /* Reuse SSA name if it was created for a dependency loop.  */
  if (object_sizes[object_size_type][name] != NULL_TREE)
    gcc_assert (*object_size_exprs[object_size_type][name] == error_mark_node);
  else
    object_sizes[object_size_type][name] = make_ssa_name_fn (fun, sizetype, 0);
  object_size_exprs[object_size_type][name] = sz;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Caching size for ");
      print_generic_expr (dump_file, ssa_name (name), dump_flags);
      fprintf (dump_file, ":: Object size: ");
      print_generic_expr (dump_file, object_sizes[object_size_type][name],
			  dump_flags);
      fprintf (dump_file, " = ");
      print_generic_expr (dump_file,
			  *object_size_exprs[object_size_type][name],
			  dump_flags);
      fprintf (dump_file, "\n");
    }

  bitmap_set_bit (computed[object_size_type], name);
}

/* Copy SZ and then call cache_object_size above.  */

static void
cache_object_size_copy (struct object_size_info *osi, unsigned name, tree sz)
{
  int object_size_type = osi->object_size_type;

  if (sz == NULL_TREE)
    {
      if (object_sizes[object_size_type][name] != NULL_TREE)
	release_ssa_name (object_sizes[object_size_type][name]);
      object_sizes[object_size_type][name] = NULL_TREE;
      object_size_exprs[object_size_type][name] = NULL;
      bitmap_set_bit (computed[object_size_type], name);
      return;
    }

  cache_object_size (osi, name, new tree (sz));
}

/* Use size of ORIG for DEST and return it.  */

static void
set_object_size_ssa (struct object_size_info *osi, tree dest, tree orig)
{
  collect_object_sizes_for (osi, orig);

  tree sz = object_sizes[osi->object_size_type][SSA_NAME_VERSION (orig)];
  cache_object_size_copy (osi, SSA_NAME_VERSION (dest), sz);
}


/* Compute object_sizes for PTR, defined to the result of a call.  */

static void
call_object_size (struct object_size_info *osi, tree ptr, gcall *call)
{
  gcc_assert (is_gimple_call (call));

  cache_object_size_copy (osi, SSA_NAME_VERSION (ptr),
			  alloc_object_size (call));
}


/* Compute object sizes for VAR.

   - For allocation GIMPLE_CALL like malloc or calloc object size is the size
     of the allocation.
   - For a memcpy like GIMPLE_CALL that always returns one of its arguments,
     the object size is object size of that argument.
   - For GIMPLE_PHI, compute a PHI node with sizes of all branches in the PHI
     node of the object.  */

static void
collect_object_sizes_for (struct object_size_info *osi, tree var)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  gimple *stmt;

  if (bitmap_bit_p (computed[object_size_type], varno))
    return;

  if (bitmap_set_bit (osi->visited, varno))
    object_sizes[object_size_type][varno] = NULL_TREE;
  else
    {
      /* Add an SSA name but mark the expression as being an error_mark_node.
	 When we go back up the stack, the error_mark_node should get
	 overwritten by a proper expression.  */
      cache_object_size (osi, varno, &error_mark_node);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Found a dependency loop at ");
	  print_generic_expr (dump_file, var, dump_flags);
	  fprintf (dump_file, "\n");
	}
      return;
    }

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Visiting use-def links for ");
      print_generic_expr (dump_file, var, dump_flags);
      fprintf (dump_file, "\n");
    }

  stmt = SSA_NAME_DEF_STMT (var);

  switch (gimple_code (stmt))
    {
    case GIMPLE_CALL:
      {
	gcall *call_stmt = as_a <gcall *> (stmt);
	tree arg = pass_through_call (call_stmt);
	if (arg)
	  {
	    if (TREE_CODE (arg) == SSA_NAME)
	      set_object_size_ssa (osi, var, arg);
	  }
	else
	  call_object_size (osi, var, call_stmt);
	break;
      }

    case GIMPLE_PHI:
      {
	unsigned i, num_args = gimple_phi_num_args (stmt);
	tree *sizes = new tree[num_args] ();

	/* Bail out if any of the PHI arguments are non-SSA expressions or
	   if size of an argument cannot be determined.  */
	for (i = 0; i < gimple_phi_num_args (stmt); i++)
	  {
	    tree rhs = gimple_phi_arg_def (stmt, i);

	    if (TREE_CODE (rhs) != SSA_NAME)
	      break;

	    collect_object_sizes_for (osi, rhs);
	    tree sz = object_sizes[object_size_type][SSA_NAME_VERSION (rhs)];

	    if (sz == NULL_TREE)
	      break;

	    sizes[i] = sz;
	  }

	/* Record all possible sizes to build our PHI node later.  */
	if (i == gimple_phi_num_args (stmt))
	  {
	    cache_object_size (osi, varno, sizes);
	    break;
	  }
	else
	  delete[] sizes;
      }
    /* FALLTHROUGH */

    /* Bail out for all other cases.  */
    case GIMPLE_NOP:
    case GIMPLE_ASSIGN:
    case GIMPLE_ASM:
      cache_object_size_copy (osi, varno, NULL_TREE);
      break;

    default:
      gcc_unreachable ();
    }
  gcc_assert (bitmap_bit_p (computed[object_size_type], varno));
}


/* Initialize data structures for the object size computation.  */

void
init_dynamic_object_sizes (void)
{
  int object_size_type;

  if (computed[0])
    return;

  for (object_size_type = 0; object_size_type <= 3; object_size_type++)
    {
      object_sizes[object_size_type].safe_grow (num_ssa_names, true);
      object_size_exprs[object_size_type].safe_grow (num_ssa_names, true);
      computed[object_size_type] = BITMAP_ALLOC (NULL);
    }
}


/* Destroy data structures after the object size computation.  */

void
fini_dynamic_object_sizes (void)
{
  int object_size_type;

  for (object_size_type = 0; object_size_type <= 3; object_size_type++)
    {
      object_sizes[object_size_type].release ();
      object_size_exprs[object_size_type].release ();
      BITMAP_FREE (computed[object_size_type]);
    }
}

unsigned int
dynamic_object_sizes_execute (function *fun, bool lower_to_bos)
{
  basic_block bb;

  init_dynamic_object_sizes ();

  FOR_EACH_BB_FN (bb, fun)
    {
      gimple_stmt_iterator i;
      for (i = gsi_start_bb (bb); !gsi_end_p (i); gsi_next (&i))
	{
	  gimple *call = gsi_stmt (i);

	  if (!gimple_call_builtin_p (call, BUILT_IN_DYN_OBJECT_SIZE))
	    continue;

	  tree lhs = gimple_call_lhs (call);
	  if (!lhs)
	    continue;

	  unsigned numargs = gimple_call_num_args (call);
	  tree *args = XALLOCAVEC (tree, numargs);
	  args[0] = gimple_call_arg (call, 0);
	  args[1] = gimple_call_arg (call, 1);

	  location_t loc = EXPR_LOC_OR_LOC (args[0], input_location);
	  tree result_type = gimple_call_return_type (as_a <gcall *> (call));
	  tree result = fold_builtin_call_array (loc, result_type,
						 gimple_call_fn (call),
						 numargs, args);

	  if (result)
	    {
	      /* fold_builtin_call_array may wrap the result inside a
		 NOP_EXPR.  */
	      STRIP_NOPS (result);
	      gimplify_and_update_call_from_tree (&i, result);

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  fprintf (dump_file, "Simplified builtin in\n  ");
		  print_gimple_stmt (dump_file, call, 0, dump_flags);
		  fprintf (dump_file, " to ");
		  print_generic_expr (dump_file, result);
		  fprintf (dump_file, "\n");
		}
	    }
	  else if (lower_to_bos)
	    {
	      /* If we could not find a suitable size expression, lower to
		 __builtin_object_size so that we may at least get a constant
		 lower or higher estimate.  */
	      tree bosfn = builtin_decl_implicit (BUILT_IN_OBJECT_SIZE);
	      gimple_call_set_fndecl (call, bosfn);
	      gimple_call_set_arg (call, 0, args[0]);
	      gimple_call_set_arg (call, 1, args[1]);
	      update_stmt (call);

	      if (dump_file && (dump_flags & TDF_DETAILS))
		{
		  print_generic_expr (dump_file, args[0], dump_flags);
		  fprintf (dump_file,
			   ": Simplified to __builtin_object_size\n");
		}
	    }
	}
    }

  fini_dynamic_object_sizes ();
  return 0;
}

/* Evaluate __builtin_dynamic_object_size () builtins early.  */

namespace {

const pass_data pass_data_early_dynamic_object_sizes =
{
  GIMPLE_PASS, /* type */
  "early_dynobjsz", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  ( PROP_cfg | PROP_ssa ), /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_early_dynamic_object_sizes : public gimple_opt_pass
{
public:
  pass_early_dynamic_object_sizes (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_early_dynamic_object_sizes, ctxt)
  {}

  /* opt_pass methods: */
  opt_pass * clone () { return new pass_early_dynamic_object_sizes (m_ctxt); }
  virtual unsigned int execute (function *fun)
  {
    return dynamic_object_sizes_execute (fun, false);
  }
}; // class pass_early_dynamic_object_sizes

} // anon namespace

gimple_opt_pass *
make_pass_early_dynamic_object_sizes (gcc::context *ctxt)
{
  return new pass_early_dynamic_object_sizes (ctxt);
}

/* Evaluate __builtin_dynamic_object_size () builtins, simplifying to
   __builtin_object_size () if a size expression cannot be produced.  */

namespace {

const pass_data pass_data_dynamic_object_sizes =
{
  GIMPLE_PASS, /* type */
  "dynobjsz", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  ( PROP_cfg | PROP_ssa ), /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_dynamic_object_sizes : public gimple_opt_pass
{
public:
  pass_dynamic_object_sizes (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_dynamic_object_sizes, ctxt)
  {}

  /* opt_pass methods: */
  opt_pass * clone () { return new pass_dynamic_object_sizes (m_ctxt); }
  virtual unsigned int execute (function *fun)
  {
    return dynamic_object_sizes_execute (fun, true);
  }
}; // class pass_dynamic_object_sizes

} // anon namespace

gimple_opt_pass *
make_pass_dynamic_object_sizes (gcc::context *ctxt)
{
  return new pass_dynamic_object_sizes (ctxt);
}
