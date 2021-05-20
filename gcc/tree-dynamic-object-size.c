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
static void set_object_size (struct object_size_info *, tree, tree, bool);

/* object_sizes[0] is the number of bytes till the end of the object.
   object_sizes[1] is the number of bytes till the end of the subobject
   (innermost array or field with address taken).  */
static vec<tree> object_sizes[2];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[2];

bool compute_builtin_dyn_object_size (tree, int, tree *);

static tree
build_cond_branch (tree t, tree low_bound, tree unit_size)
{
  tree br = fold_build2 (MINUS_EXPR, TREE_TYPE (t), t, low_bound);
  br = fold_convert (sizetype, br);
  br = fold_build2 (MULT_EXPR, sizetype, unit_size, br);

  return br;
}

/* Compute offset of EXPR within VAR.  Return error_mark_node
   if unknown.  */

static tree
compute_object_offset (const_tree expr, const_tree var)
{
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
	{
	  tree cond = fold_build2 (GE_EXPR, TREE_TYPE (t), t, low_bound);
	  tree then_br = build_cond_branch (t, low_bound, unit_size);
	  tree else_br = build_cond_branch (low_bound, t, unit_size);

	  then_br = fold_build2 (PLUS_EXPR, sizetype, base, then_br);
	  else_br = fold_build2 (MINUS_EXPR, sizetype, base, else_br);
	  return fold_build3 (COND_EXPR, sizetype, cond, then_br, else_br);
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

  return fold_build2 (PLUS_EXPR, sizetype, base, off);
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

/* Get the whole variable encapsulating the pointer PTR, given the whole_var
   object WHOLE_VAR.  */

static tree
get_closest_subobject (const_tree ptr, tree whole_var)
{
  tree var = TREE_OPERAND (ptr, 0);

  while (var != whole_var
	 && TREE_CODE (var) != BIT_FIELD_REF
	 && TREE_CODE (var) != COMPONENT_REF
	 && TREE_CODE (var) != ARRAY_REF
	 && TREE_CODE (var) != ARRAY_RANGE_REF
	 && TREE_CODE (var) != REALPART_EXPR
	 && TREE_CODE (var) != IMAGPART_EXPR)
    var = TREE_OPERAND (var, 0);

  if (var != whole_var && TREE_CODE (var) == ARRAY_REF)
    var = TREE_OPERAND (var, 0);

  if (! TYPE_SIZE_UNIT (TREE_TYPE (var)))
    var = whole_var;
  else if (var != whole_var && TREE_CODE (whole_var) == MEM_REF)
    {
      tree v = var;
      /* For &X->fld, compute object size only if fld isn't the last
	 field, as struct { int i; char c[1]; } is often used instead
	 of flexible array member.  */
      while (v && v != whole_var)
	switch (TREE_CODE (v))
	  {
	  case ARRAY_REF:
	    if (TYPE_SIZE_UNIT (TREE_TYPE (TREE_OPERAND (v, 0)))
		&& TREE_CODE (TREE_OPERAND (v, 1)) == INTEGER_CST)
	      {
		tree domain
		  = TYPE_DOMAIN (TREE_TYPE (TREE_OPERAND (v, 0)));
		if (domain
		    && TYPE_MAX_VALUE (domain)
		    && TREE_CODE (TYPE_MAX_VALUE (domain))
		    == INTEGER_CST
		    && tree_int_cst_lt (TREE_OPERAND (v, 1),
					TYPE_MAX_VALUE (domain)))
		  {
		    v = NULL_TREE;
		    break;
		  }
	      }
	    v = TREE_OPERAND (v, 0);
	    break;
	  case REALPART_EXPR:
	  case IMAGPART_EXPR:
	    v = NULL_TREE;
	    break;
	  case COMPONENT_REF:
	    if (TREE_CODE (TREE_TYPE (v)) != ARRAY_TYPE)
	      {
		v = NULL_TREE;
		break;
	      }
	    while (v != whole_var && TREE_CODE (v) == COMPONENT_REF)
	      if (TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
		  != UNION_TYPE
		  && TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
		  != QUAL_UNION_TYPE)
		break;
	      else
		v = TREE_OPERAND (v, 0);
	    if (TREE_CODE (v) == COMPONENT_REF
		&& TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
		== RECORD_TYPE)
	      {
		tree fld_chain = DECL_CHAIN (TREE_OPERAND (v, 1));
		for (; fld_chain; fld_chain = DECL_CHAIN (fld_chain))
		  if (TREE_CODE (fld_chain) == FIELD_DECL)
		    break;

		if (fld_chain)
		  {
		    v = NULL_TREE;
		    break;
		  }
		v = TREE_OPERAND (v, 0);
	      }
	    while (v != whole_var && TREE_CODE (v) == COMPONENT_REF)
	      if (TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
		  != UNION_TYPE
		  && TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
		  != QUAL_UNION_TYPE)
		break;
	      else
		v = TREE_OPERAND (v, 0);
	    if (v != whole_var)
	      v = NULL_TREE;
	    else
	      v = whole_var;
	    break;
	  default:
	    v = whole_var;
	    break;
	  }
      if (v == whole_var)
	var = whole_var;
    }

  return var;
}

/* Compute __builtin_object_size for PTR, which is a ADDR_EXPR.
   OBJECT_SIZE_TYPE is the second argument from __builtin_object_size.
   If unknown, return unknown[object_size_type].  */

bool
__attribute__ ((noinline))
addr_dyn_object_size (struct object_size_info *osi, const_tree ptr,
		      int object_size_type, tree *psize)
{
  tree pt_var, pt_var_size = NULL_TREE, var_size, bytes;

  gcc_assert (TREE_CODE (ptr) == ADDR_EXPR);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = NULL_TREE;

  pt_var = get_whole_var (ptr);

  if (!pt_var)
    return false;

  if (!whole_var_size (osi, pt_var, object_size_type, &pt_var_size))
    return false;

  /* PTR points to a subobject of whole variable PT_VAR.  */
  if (pt_var != TREE_OPERAND (ptr, 0))
    {
      tree var;

      if (object_size_type & 1)
	var = get_closest_subobject (ptr, pt_var);
      else
	var = pt_var;

      if (var != pt_var)
	{
	  /* Non-constant sizes of VLAs embedded in structs may not always be
	     reliable because the TYPE_SIZE_UNIT does not get updated to the
	     SSA-ized expression during the SSA pass.  Bail out until that is
	     fixed.  */
	  if (TREE_CONSTANT (TYPE_SIZE_UNIT (TREE_TYPE (var))))
	    var_size = TYPE_SIZE_UNIT (TREE_TYPE (var));
	  else
	    return false;
	}
      else if (!pt_var_size)
	return false;
      else
	var_size = pt_var_size;

      bytes = compute_object_offset (TREE_OPERAND (ptr, 0), var);
      if (bytes != error_mark_node)
	bytes = saturated_sub_expr (var_size, bytes);
    }
  else if (!pt_var_size)
    return false;
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

      /* Some dependency loops remain because those objects' sizes are
	 unknown.  Walk through them and update uses.  */
      EXECUTE_IF_SET_IN_BITMAP (osi.deploop, 0, i, bi)
	set_object_size (&osi, ssa_name (i), NULL_TREE, false);

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
  int object_size_type = osi->object_size_type;
  tree bytes = NULL_TREE;

  if (TREE_CODE (value) == WITH_SIZE_EXPR)
    value = TREE_OPERAND (value, 0);

  if (TREE_CODE (value) == ADDR_EXPR)
    addr_dyn_object_size (osi, value, object_size_type, &bytes);

  if (bytes)
    STRIP_NOPS (bytes);

  return bytes;
}

static void
set_object_size (struct object_size_info *osi, tree var, tree sz,
		 bool update = true)
{
  int subobject = osi->object_size_type & 1;
  int varno = SSA_NAME_VERSION (var);
  tree oldsz = object_sizes[subobject][varno];

  if (oldsz == sz)
    return;

  object_sizes[subobject][varno] = sz;

  if (!bitmap_bit_p (osi->deploop, varno))
    return;

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "Replacing placeholder ");
      print_generic_expr (dump_file, oldsz, dump_flags);
      fprintf (dump_file, " with ");
      if (sz)
	print_generic_expr (dump_file, sz, dump_flags);
      else
	fprintf (dump_file, "a NULL_TREE");
      fprintf (dump_file, "\n");
    }

  /* XXX Dependency loops not supported for PHIs with abnormal edges yet.  */
  gcc_assert (!SSA_NAME_OCCURS_IN_ABNORMAL_PHI (oldsz));

  /* We finally couldn't find the size of VAR, so make sure all uses get the
     unknown size.  */
  if (!sz)
    sz = build_int_cst (size_type_node, osi->object_size_type < 2 ? -1 : 0);

  /* Force into a form that PHIs will accept.  */
  else if (!is_gimple_variable (sz))
    {
      gimple_seq seq;

      sz = force_gimple_operand (sz, &seq, true, NULL);
      gimple_stmt_iterator i = gsi_for_stmt (SSA_NAME_DEF_STMT (var));
      gsi_insert_seq_after (&i, seq, GSI_CONTINUE_LINKING);
    }

  replace_uses_by (oldsz, sz);
  release_ssa_name (oldsz);
  if (update)
    bitmap_clear_bit (osi->deploop, varno);
}

/* Use size of ORIG for DEST.  Return true if
   the object size might need reexamination later.  */

static void
set_object_size_ssa (struct object_size_info *osi, tree dest, tree orig,
		     tree offset = NULL_TREE)
{
  int subobject = osi->object_size_type & 1;

  collect_object_sizes_for (osi, orig);

  tree sz = object_sizes[subobject][SSA_NAME_VERSION (orig)];

  if (sz && offset)
    sz = saturated_sub_expr (sz, offset);

  set_object_size (osi, dest, sz);
}

/* Compute object_sizes for VAR, defined to the result of an assignment
   with operator POINTER_PLUS_EXPR.  Return true if the object size might
   need reexamination  later.  */

static void
plus_stmt_object_size (struct object_size_info *osi, tree var, gimple *stmt)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  tree op0, op1, bytes;

  if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR)
    {
      op0 = gimple_assign_rhs1 (stmt);
      op1 = gimple_assign_rhs2 (stmt);
    }
  else if (gimple_assign_rhs_code (stmt) == ADDR_EXPR)
    {
      tree rhs = TREE_OPERAND (gimple_assign_rhs1 (stmt), 0);
      gcc_assert (TREE_CODE (rhs) == MEM_REF);
      op0 = TREE_OPERAND (rhs, 0);
      op1 = TREE_OPERAND (rhs, 1);
    }
  else
    gcc_unreachable ();

  /* Handle PTR + OFFSET here.  */
  if (TREE_CODE (op0) == SSA_NAME)
    {
      set_object_size_ssa (osi, var, op0, op1);
      bytes = object_sizes[object_size_type & 1][varno];
    }
  else if (TREE_CODE (op0) == ADDR_EXPR)
    {
      /* op0 will be ADDR_EXPR here.  */
      addr_dyn_object_size (osi, op0, object_size_type, &bytes);
      bytes = saturated_sub_expr (bytes, op1);
    }
  else
    bytes = NULL_TREE;

  set_object_size (osi, var, bytes);
}

/* Compute object_sizes for PTR, defined to the result of a call.  */

static void
call_object_size (struct object_size_info *osi, tree ptr, gcall *call)
{
  gcc_assert (is_gimple_call (call));

  set_object_size (osi, ptr, alloc_object_size (call));
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
      /* Found a dependency loop.  Mark the variable in the DEPLOOP bitmap and
	 make an SSA name for it so that it can be used directly.  The SSA name
	 is assigned to the final value once we unwind back to the first time
	 the variable is seen.  */
      bitmap_set_bit (osi->deploop, varno);
      if (object_sizes[subobject][varno] == NULL_TREE)
	object_sizes[subobject][varno] = make_ssa_name (size_type_node);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Found a dependency loop at ");
	  print_generic_expr (dump_file, var, dump_flags);
	  fprintf (dump_file, "\n");
	  fprintf (dump_file, "Placeholder SSA ");
	  print_generic_expr (dump_file, object_sizes[subobject][varno],
			      dump_flags);
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
    case GIMPLE_ASSIGN:
      {
	tree rhs = gimple_assign_rhs1 (stmt);
	if (gimple_assign_rhs_code (stmt) == POINTER_PLUS_EXPR
	    || (gimple_assign_rhs_code (stmt) == ADDR_EXPR
		&& TREE_CODE (TREE_OPERAND (rhs, 0)) == MEM_REF))
	  plus_stmt_object_size (osi, var, stmt);
	else if (gimple_assign_single_p (stmt)
		 || gimple_assign_unary_nop_p (stmt))
	  {
	    if (TREE_CODE (rhs) == SSA_NAME
		&& POINTER_TYPE_P (TREE_TYPE (rhs)))
	      set_object_size_ssa (osi, var, rhs);
	    else
	      set_object_size (osi, var, expr_object_size (osi, rhs));
	  }
	break;
      }

    case GIMPLE_CALL:
      {
	gcall *call_stmt = as_a <gcall *> (stmt);
	tree arg = pass_through_call (call_stmt);
	if (arg)
	  {
	    if (TREE_CODE (arg) == SSA_NAME)
	      set_object_size_ssa (osi, var, arg);
	    else
	      set_object_size (osi, var, expr_object_size (osi, arg));
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

		/* XXX Dependency loops not supported for PHIs with abnormal
		   edges yet.  */
		if (bitmap_bit_p (osi->deploop, SSA_NAME_VERSION (rhs))
		    && (gimple_phi_arg_edge (as_a <gphi *> (stmt), i)->flags
			& EDGE_ABNORMAL))
		  {
		    if (dump_file && (dump_flags & TDF_DETAILS))
		      {
			print_generic_expr (dump_file, var, dump_flags);
			fprintf (dump_file,
				 " :BAIL OUT: PHI with abnormal edge ");
			print_gimple_expr (dump_file, stmt, dump_flags);
			fprintf (dump_file, "\n");
		      }

		    break;
		  }
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

	    set_object_size (osi, var, PHI_RESULT (newphi));
	  }

	break;
      }

    case GIMPLE_NOP:
      if (SSA_NAME_VAR (var)
	  && TREE_CODE (SSA_NAME_VAR (var)) == PARM_DECL)
	set_object_size (osi, var,
			 expr_object_size (osi, SSA_NAME_VAR (var)));
      break;

    case GIMPLE_ASM:
      break;

    default:
      gcc_unreachable ();
    }

  bitmap_set_bit (computed[subobject], varno);
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
