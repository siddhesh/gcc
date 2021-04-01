/* __builtin_dynamic_object_size (ptr, object_size_type) computation
   Copyright (C) 2021 Free Software Foundation, Inc.
   Contributed by Siddhesh Poyarekar <siddhesh@redhat.com>

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
       the maximum or minimum estimate of the size of the object when it is
       infeasible to find the exact object size.  The expression may be (and in
       fact currently is, since it simplifies to __builtin_object_size on
       failure) a constant like in the case of __builtin_object_size, but is
       not required to be so.

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
  int object_size_type;
  bitmap visited, deploop;
};

static tree alloc_object_size (const gcall *);
static tree pass_through_call (const gcall *);
static void collect_object_sizes_for (struct object_size_info *, tree);

/* object_sizes[0] is the number of bytes till the end of the object.
   object_sizes[1] is the number of bytes till the end of the subobject
   (innermost array or field with address taken).  */
static vec<tree> object_sizes[2];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[2];

bool compute_builtin_dyn_object_size (tree, int, tree *);

/* Compute offset of EXPR within VAR.  Return error_mark_node
   if unknown.  */

static tree
compute_object_offset (const_tree expr, const_tree var)
{
  enum tree_code code = PLUS_EXPR;
  tree base, off, t;

  if (expr == var)
    return size_zero_node;

  switch (TREE_CODE (expr))
    {
    case COMPONENT_REF:
      base = compute_object_offset (TREE_OPERAND (expr, 0), var);
      if (base == error_mark_node)
	return base;

      t = TREE_OPERAND (expr, 1);
      off = fold_build2 (PLUS_EXPR, sizetype, DECL_FIELD_OFFSET (t),
			size_int (tree_to_uhwi (DECL_FIELD_BIT_OFFSET (t))
				  / BITS_PER_UNIT));
      break;

    case REALPART_EXPR:
    CASE_CONVERT:
    case VIEW_CONVERT_EXPR:
    case NON_LVALUE_EXPR:
      return compute_object_offset (TREE_OPERAND (expr, 0), var);

    case IMAGPART_EXPR:
      base = compute_object_offset (TREE_OPERAND (expr, 0), var);
      if (base == error_mark_node)
	return base;

      off = TYPE_SIZE_UNIT (TREE_TYPE (expr));
      break;

    case ARRAY_REF:
      base = compute_object_offset (TREE_OPERAND (expr, 0), var);
      if (base == error_mark_node)
	return base;

      t = TREE_OPERAND (expr, 1);
      tree low_bound, unit_size;
      low_bound = array_ref_low_bound (CONST_CAST_TREE (expr));
      unit_size = array_ref_element_size (CONST_CAST_TREE (expr));
      if (! integer_zerop (low_bound))
	t = fold_build2 (MINUS_EXPR, TREE_TYPE (t), t, low_bound);
      if (TREE_CODE (t) == INTEGER_CST && tree_int_cst_sgn (t) < 0)
	{
	  code = MINUS_EXPR;
	  t = fold_build1 (NEGATE_EXPR, TREE_TYPE (t), t);
	}
      t = fold_convert (sizetype, t);
      off = fold_build2 (MULT_EXPR, sizetype, unit_size, t);
      break;

    case MEM_REF:
      gcc_assert (TREE_CODE (TREE_OPERAND (expr, 0)) == ADDR_EXPR);
      return wide_int_to_tree (sizetype, mem_ref_offset (expr));

    default:
      return error_mark_node;
    }

  return fold_build2 (code, sizetype, base, off);
}

/* Return an expression that evaluates to the saturated sum of SZ and OFF.  The
   expression is of the form SZ + MIN((SIZE_MAX - SZ), OFF).  */

static tree
saturated_sub_expr (tree sz, tree off)
{
  /* A MEM_REF offset may be a pointer, where we need to figure out the
     multiplier based on the base type.  */
  if (POINTER_TYPE_P (TREE_TYPE (off)))
    {
      tree typesize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (off)));

      if (typesize)
	off = fold_build2 (MULT_EXPR, sizetype, off, typesize);
      else
	off = fold_convert (sizetype, off);
    }

  tree max_off = fold_build2 (RSHIFT_EXPR, sizetype, TYPE_MAX_VALUE (sizetype),
			      size_one_node);

  /* Consider offsets larger than SIZE_MAX / 2 to be negative to emulate
     ssize_t.  Allow integer underflow here because it is still a more
     restrictive result than returning unknown size.  This relevant only for
     modes 0 and 1 since we want to try and avoid undefined behaviour for the
     sake of _FORTIFY_SOURCE.  For modes 2 and 3 we assume valid user code.  */
  tree cond = fold_build2 (GT_EXPR, sizetype, off, max_off);
  tree neg_off = fold_build1 (NEGATE_EXPR, sizetype, off);

  off = fold_build3 (COND_EXPR, sizetype, cond, neg_off, off);

  tree res = fold_build2 (MIN_EXPR, sizetype, sz, off);
  return fold_build2 (MINUS_EXPR, sizetype, sz, res);
}

/* Peek through ADDR_EXPR operands to get the definition of the whole variable
   PTR points in.  Write the result expression into PT_VARP and its size into
   PT_VAR_SIZEP.  Return true if the object is found.  */

static tree
get_whole_var (const_tree ptr)
{
  tree pt_var;

  pt_var = TREE_OPERAND (ptr, 0);
  while (handled_component_p (pt_var))
    pt_var = TREE_OPERAND (pt_var, 0);

  return pt_var;
}

static bool
whole_var_size (struct object_size_info *osi, tree pt_var,
		int object_size_type, tree *pt_var_sizep)
{
  tree pt_var_size = NULL_TREE;
  int subobject = object_size_type & 1;
  int min = object_size_type & 2;

  if (TREE_CODE (pt_var) == MEM_REF)
    {
      if (!osi || subobject
	  || TREE_CODE (TREE_OPERAND (pt_var, 0)) != SSA_NAME)
	{
	  compute_builtin_dyn_object_size (TREE_OPERAND (pt_var, 0), min,
					   &pt_var_size);
	}
      else
	{
	  tree var = TREE_OPERAND (pt_var, 0);
	  collect_object_sizes_for (osi, var);
	  if (bitmap_bit_p (computed[subobject],
			    SSA_NAME_VERSION (var)))
	    pt_var_size = object_sizes[subobject][SSA_NAME_VERSION (var)];
	}

      if (pt_var_size != NULL_TREE)
	{
	  tree offset = wide_int_to_tree (size_type_node,
					  mem_ref_offset (pt_var));

	  pt_var_size = saturated_sub_expr (pt_var_size, offset);
	}
    }
  else if (DECL_P (pt_var))
    {
      pt_var_size = decl_init_size (pt_var, min);
      if (!pt_var_size)
	return false;
    }
  else if (TREE_CODE (pt_var) == STRING_CST)
    pt_var_size = TYPE_SIZE_UNIT (TREE_TYPE (pt_var));
  else
    return false;

  *pt_var_sizep = pt_var_size;
  return true;
}

/* Compute __builtin_object_size for PTR, which is a ADDR_EXPR.
   OBJECT_SIZE_TYPE is the second argument from __builtin_object_size.
   If unknown, return unknown[object_size_type].  */

bool
__attribute__ ((noinline))
addr_dyn_object_size (struct object_size_info *osi, const_tree ptr,
		      int object_size_type, tree *psize)
{
  tree pt_var, pt_var_size = NULL_TREE, bytes;

  gcc_assert (TREE_CODE (ptr) == ADDR_EXPR);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = NULL_TREE;

  pt_var = get_whole_var (ptr);

  if (!pt_var)
    return false;

  if (!whole_var_size (osi, pt_var, object_size_type, &pt_var_size))
    return false;

  if (!pt_var_size)
    return false;

  /* PTR points to a subobject of whole variable PT_VAR.  */
  if (pt_var != TREE_OPERAND (ptr, 0))
    {
      bytes = compute_object_offset (TREE_OPERAND (ptr, 0), pt_var);
      if (bytes != error_mark_node)
	bytes = saturated_sub_expr (pt_var_size, bytes);
    }
  else
    bytes = pt_var_size;

  *psize = bytes;
  return true;
}


/* Compute __builtin_object_size for CALL, which is a GIMPLE_CALL.
   Handles calls to functions declared with attribute alloc_size.
   OBJECT_SIZE_TYPE is the second argument from __builtin_object_size.
   If unknown, return unknown[object_size_type].  */

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

/* Compute __builtin_object_size value for PTR and set *PSIZE to
   the resulting value.  If the declared object is known and PDECL
   is nonnull, sets *PDECL to the object's DECL.  OBJECT_SIZE_TYPE
   is the second argument   to __builtin_object_size.
   Returns true on success and false when the object size could not
   be determined.  */

bool
compute_builtin_dyn_object_size (tree ptr, int object_size_type, tree *psize)
{
  gcc_assert (object_size_type >= 0 && object_size_type <= 3);
  int subobject = object_size_type & 1;

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = NULL_TREE;

  if (TREE_CODE (ptr) == ADDR_EXPR)
    return addr_dyn_object_size (NULL, ptr, object_size_type, psize);

  if (TREE_CODE (ptr) != SSA_NAME
      || !POINTER_TYPE_P (TREE_TYPE (ptr)))
      return false;

  if (computed[object_size_type] == NULL)
    return false;

  if (!bitmap_bit_p (computed[subobject], SSA_NAME_VERSION (ptr)))
    {
      struct object_size_info osi;
      bitmap_iterator bi;
      unsigned int i;

      if (num_ssa_names > object_sizes[subobject].length ())
	object_sizes[subobject].safe_grow (num_ssa_names, true);
      if (dump_file)
	{
	  fprintf (dump_file, "Computing %s dynamic %sobject size for ",
		   (object_size_type & 2) ? "minimum" : "maximum",
		   subobject ? "sub" : "");
	  print_generic_expr (dump_file, ptr, dump_flags);
	  fprintf (dump_file, ":\n");
	}

      osi.visited = BITMAP_ALLOC (NULL);
      osi.deploop = BITMAP_ALLOC (NULL);
      osi.object_size_type = object_size_type;

      collect_object_sizes_for (&osi, ptr);

      /* Objects that could not be evaluated because of dependency loops.  Do
	 nothing with them for now.  */
      EXECUTE_IF_SET_IN_BITMAP (osi.deploop, 0, i, bi)
	bitmap_set_bit (computed[subobject], i);

      /* Debugging dumps.  */
      if (dump_file)
	{
	  EXECUTE_IF_SET_IN_BITMAP (osi.visited, 0, i, bi)
	    if (object_sizes[subobject][i] != NULL_TREE)
	      {
		print_generic_expr (dump_file, ssa_name (i),
				    dump_flags);
		fprintf (dump_file,
			 ": %s dynamic %sobject size ",
			 (object_size_type & 2) ? "minimum" : "maximum",
			 subobject ? "sub" : "");
		print_generic_expr (dump_file, object_sizes[subobject][i],
				    dump_flags);
		fprintf (dump_file, ":\n");
	      }
	}

      BITMAP_FREE (osi.deploop);
      BITMAP_FREE (osi.visited);
    }

  *psize = object_sizes[subobject][SSA_NAME_VERSION (ptr)];

  return *psize != NULL_TREE;
}

/* Compute object_sizes for PTR, defined to VALUE, which is not an SSA_NAME.  */

static tree
expr_object_size (struct object_size_info *osi, tree value)
{
  tree bytes = NULL_TREE;

  if (TREE_CODE (value) == WITH_SIZE_EXPR)
    value = TREE_OPERAND (value, 0);

  if (TREE_CODE (value) == ADDR_EXPR)
    addr_dyn_object_size (osi, value, osi->object_size_type, &bytes);

  if (bytes)
    STRIP_NOPS (bytes);

  return bytes;
}

/* Use size of ORIG for DEST.  Return true if
   the object size might need reexamination later.  */

static void
set_object_size_ssa (struct object_size_info *osi, tree dest, tree orig)
{
  int subobject = osi->object_size_type & 1;

  collect_object_sizes_for (osi, orig);

  object_sizes[subobject][SSA_NAME_VERSION (dest)] =
    object_sizes[subobject][SSA_NAME_VERSION (orig)];
}


/* Compute object_sizes for PTR, defined to the result of a call.  */

static void
call_object_size (struct object_size_info *osi, tree ptr, gcall *call)
{
  int subobject = osi->object_size_type & 1;
  unsigned int varno = SSA_NAME_VERSION (ptr);

  gcc_assert (is_gimple_call (call));

  object_sizes[subobject][varno] = alloc_object_size (call);
}


/* Compute object sizes for VAR.
   For allocation GIMPLE_CALL like malloc or calloc object size is the size
   of the allocation.
   For a memcpy like GIMPLE_CALL that always returns one of its arguments, the
   object size is object size of that argument.  */

static void
collect_object_sizes_for (struct object_size_info *osi, tree var)
{
  int subobject = osi->object_size_type & 1;
  unsigned int varno = SSA_NAME_VERSION (var);
  gimple *stmt;

  if (bitmap_bit_p (computed[subobject], varno))
    return;

  if (bitmap_set_bit (osi->visited, varno))
    object_sizes[subobject][varno] = NULL_TREE;
  else
    {
      /* Found a dependency loop.  Mark the variable for later
	 re-examination.  */
      bitmap_set_bit (osi->deploop, varno);
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
	    else
	      object_sizes[subobject][varno] = expr_object_size (osi, arg);
	  }
	else
	  call_object_size (osi, var, call_stmt);
	break;
      }

    case GIMPLE_PHI:
      {
	unsigned i;
	auto_vec<tree> sizes;

	/* Bail out if any of the PHI arguments are non-SSA expressions or
	   if size of an argument cannot be determined.  */
	for (i = 0; i < gimple_phi_num_args (stmt); i++)
	  {
	    tree rhs = gimple_phi_arg_def (stmt, i);
	    tree sz;

	    if (TREE_CODE (rhs) != SSA_NAME)
	      sz = expr_object_size (osi, rhs);
	    else
	      {
		collect_object_sizes_for (osi, rhs);
		sz = object_sizes[subobject][SSA_NAME_VERSION (rhs)];
	      }

	    if (sz == NULL_TREE)
	      break;

	    sizes.safe_push (sz);
	  }

	/* We have all the sizes, so build the phi node.  */
	if (i == gimple_phi_num_args (stmt))
	  {
	    tree objsz = make_ssa_name (sizetype);
	    gphi *newphi = create_phi_node (objsz, gimple_bb (stmt));
	    gphi *obj_phi =  as_a <gphi *> (stmt);

	    for (i = 0; i < gimple_phi_num_args (stmt); i++)
	      {
		/* If we built an expression, we will need to build statements
		   and insert them on the edge right away.  */
		if (!is_gimple_variable (sizes[i]))
		  {
		    gimple_seq seq;
		    edge e = gimple_phi_arg_edge (obj_phi, i);
		    sizes[i] = force_gimple_operand (sizes[i], &seq, true,
						     NULL);

		    /* Put the size definition at the very end of the source
		       block of the PHI edge so that it succeeds any
		       definitions it may need in that block.  */
		    gimple_stmt_iterator gsi = gsi_last_bb (e->src);
		    gimple *s = gsi_stmt (gsi);
		    if (s && (is_a <gcond *> (s) || is_a <ggoto *> (s)))
		      gsi_insert_seq_before (&gsi, seq, GSI_CONTINUE_LINKING);
		    else
		      gsi_insert_seq_after (&gsi, seq, GSI_CONTINUE_LINKING);
		  }

		add_phi_arg (newphi, sizes[i],
			     gimple_phi_arg_edge (obj_phi, i),
			     gimple_phi_arg_location (obj_phi, i));
	      }

	    object_sizes[subobject][varno] = PHI_RESULT (newphi);
	  }
	else
	  object_sizes[subobject][varno] = NULL_TREE;

	break;
      }

    case GIMPLE_NOP:
      if (SSA_NAME_VAR (var)
	  && TREE_CODE (SSA_NAME_VAR (var)) == PARM_DECL)
	object_sizes[subobject][varno] = expr_object_size (osi,
							   SSA_NAME_VAR (var));
      else
	/* Uninitialized SSA names point nowhere.  */
	object_sizes[subobject][varno] = NULL_TREE;
      break;

    /* Bail out for all other cases.  */
    case GIMPLE_ASSIGN:
    case GIMPLE_ASM:
      object_sizes[subobject][varno] = NULL_TREE;
      break;

    default:
      gcc_unreachable ();
    }

  bitmap_set_bit (computed[subobject], varno);
  bitmap_clear_bit (osi->deploop, varno);
}


/* Initialize data structures for the object size computation.  */

void
init_dynamic_object_sizes (void)
{
  int subobject;

  if (computed[0])
    return;

  for (subobject = 0; subobject <= 1; subobject++)
    {
      object_sizes[subobject].safe_grow (num_ssa_names, true);
      computed[subobject] = BITMAP_ALLOC (NULL);
    }
}


/* Destroy data structures after the object size computation.  */

void
fini_dynamic_object_sizes (void)
{
  int subobject;

  for (subobject = 0; subobject <= 1; subobject++)
    {
      object_sizes[subobject].release ();
      BITMAP_FREE (computed[subobject]);
    }
}


/* Simple pass to optimize all __builtin_object_size () builtins.  */

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
  virtual unsigned int execute (function *);
}; // class pass_dynamic_object_sizes

unsigned int
pass_dynamic_object_sizes::execute (function *fun)
{
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      gimple_stmt_iterator i;
      for (i = gsi_start_bb (bb); !gsi_end_p (i); gsi_next (&i))
	{
	  gimple *call = gsi_stmt (i);

	  if (!gimple_call_builtin_p (call, BUILT_IN_DYN_OBJECT_SIZE))
	    continue;

	  init_dynamic_object_sizes ();

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
	  else
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

} // anon namespace

gimple_opt_pass *
make_pass_dynamic_object_sizes (gcc::context *ctxt)
{
  return new pass_dynamic_object_sizes (ctxt);
}
