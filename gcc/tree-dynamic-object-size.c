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
#include "tree-dfa.h"
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

   object_sizes are SSA names of the sizes.  The actual size expressions are in
   object_size_exprs and they need not be SSA.  */
static vec<tree> object_sizes[4];
static vec<tree *>object_size_exprs[4];

/* Indexed by object_size_type and SSA name versions of the object,
   object_whole_sizes and object_whole_size_exprs have SSA names and
   expressions of the whole objects in which the pointer points.  */
static vec<tree> object_whole_sizes[4];
static vec<tree *>object_whole_size_exprs[4];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[4];

bool compute_builtin_dyn_object_size (tree, int, tree *,
				      struct function *fun = NULL);

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

/* Given an object size SZ and offset OFF into it, compute the usable object
   size.  For cases where the offset breaches object bounds, the expression
   returns 0.

   For positive offset (we asume > SIZE_MAX / 2 as negative to emulate
   ssize_t) we assume that the offset, when scaled by typesize, is within
   bounds of sz.  That is:

   sz > typesize && off <= sz / typesize

   For negative offsets, we ensure that the magnitude of the offset is within
   bounds of the lower part of the object.  This ensures that underflows result
   in zero size.  That is:

   (off > SIZE_MAX / 2 && wholesize - min(wholesize, size) > typesize
    && -off <= (wholesize - min(wholesize, size)) / typesize)

   The whole thing is then capped to wholesize to cater for situations where
   wholesize may have less memory allocated to it than needed, making subobject
   sizes incorrect.  Effectively, the expression we generate is:

   MIN(((sz > typesize && off <= sz / typesize)
	|| (off > SIZE_MAX / 2 && wholesize - min(wholesize, size) > typesize
	    && -off <= (wholesize - min(wholesize, size)) / typesize))
       ? sz - off * typesize : 0, wholesize)

   This is a fairly complex expression that may result in slow code in corner
   cases but in most standard cases, many of those elements would be constant
   (typesize certainly is) and is expected to be folded away.  */

static tree
size_for_offset (tree sz, tree off, tree wholesize, bool neg_offsets = false)
{
  tree typesize = NULL_TREE;
  tree cond = NULL_TREE;
  tree max_off = NULL_TREE;
  tree tmp = NULL_TREE;

  /* A MEM_REF offset may be a pointer, where we need to figure out the
     multiplier based on the base type.  */
  if (POINTER_TYPE_P (TREE_TYPE (off)))
    typesize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (off)));

  /* Expression for positive offset.  */
  if (typesize)
    {
      cond = fold_build2 (GT_EXPR, sizetype, sz, typesize);
      max_off = fold_build2 (EXACT_DIV_EXPR, sizetype, sz, typesize);
    }
  else
    max_off = sz;

  tmp = fold_build2 (LE_EXPR, sizetype, off, max_off);
  cond = cond ? fold_build2 (TRUTH_ANDIF_EXPR, sizetype, cond, tmp) : tmp;

  /* Negative offsets.  */
  if (wholesize && wholesize != sz && neg_offsets)
    {
      /* off > SIZE_MAX / 2 */
      max_off = fold_build2 (RSHIFT_EXPR, sizetype, TYPE_MAX_VALUE (sizetype),
			     size_one_node);
      tree cond_neg = fold_build2 (GT_EXPR, sizetype, off, max_off);

      tree neg_part = fold_build2 (MIN_EXPR, sizetype, wholesize, sz);
      neg_part = fold_build2 (MINUS_EXPR, sizetype, wholesize, neg_part);

      if (typesize)
	{
	  /* && wholesize - min(wholesize, size) > typesize */
	  tmp = fold_build2 (GT_EXPR, sizetype, neg_part, typesize);
	  cond_neg = fold_build2 (TRUTH_ANDIF_EXPR, sizetype, cond_neg, tmp);
	  max_off = fold_build2 (EXACT_DIV_EXPR, sizetype, neg_part, typesize);
	}
      else
	max_off = neg_part;

      /* && -off <= (wholesize - min(wholesize, size)) / typesize */
      tmp = fold_build2 (MINUS_EXPR, sizetype, size_zero_node, off);
      tmp = fold_build2 (LE_EXPR, sizetype, tmp, max_off);
      cond_neg = fold_build2 (TRUTH_ANDIF_EXPR, sizetype, cond_neg, tmp);

      cond = fold_build2 (TRUTH_ORIF_EXPR, sizetype, cond, cond_neg);
    }

  off = typesize ? fold_build2 (MULT_EXPR, sizetype, sz, off) : off;

  tree res = fold_build2 (MINUS_EXPR, sizetype, sz, off);
  res = fold_build3 (COND_EXPR, sizetype, cond, res, size_zero_node);

  /* Finally, cap the return value to wholesize.  This could typically happen
     if the whole object did not get any actual storage, e.g. char var[0] or
     less storage, e.g.
     struct some_large_struct = __builtin_malloc (smolval).  */
  if (wholesize)
    res = fold_build2 (MIN_EXPR, sizetype, wholesize, res);

  return res;
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
      tree var = TREE_OPERAND (pt_var, 0);
      if (!osi || subobject || TREE_CODE (var) != SSA_NAME)
	compute_builtin_dyn_object_size (var, min, &pt_var_size);
      else
	{
	  collect_object_sizes_for (osi, var);
	  pt_var_size = object_sizes[object_size_type][SSA_NAME_VERSION (var)];
	}

      if (pt_var_size != NULL_TREE)
	{
	  tree offset = wide_int_to_tree (size_type_node,
					  mem_ref_offset (pt_var));

	  pt_var_size = size_for_offset (pt_var_size, offset, pt_var_size);
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

static bool
addr_dyn_object_size (struct object_size_info *osi, const_tree ptr,
		      int object_size_type, tree *psize,
		      tree *wholesizep = NULL)
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

  var_size = pt_var_size;

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

      bytes = compute_object_offset (TREE_OPERAND (ptr, 0), var);
      if (bytes != error_mark_node)
	{
	  tree cap_size = pt_var_size;

	  /* For subobject sizes where the whole object is a structure,
	     restrict size to the size of the struct less the offset of the
	     subobject in the struct.  */
	  if (var != pt_var && pt_var_size && TREE_CODE (pt_var) == MEM_REF)
	    {
	      tree off = compute_object_offset (TREE_OPERAND (ptr, 0), pt_var);
	      if (off == error_mark_node)
		off = size_zero_node;
	      else
		off = fold_build2 (MIN_EXPR, sizetype, pt_var_size, off);
	      cap_size = fold_build2 (MINUS_EXPR, sizetype, pt_var_size, off);
	    }
	  bytes = size_for_offset (var_size, bytes, cap_size);
	}
    }
  else if (!pt_var_size)
    return false;
  else
    bytes = pt_var_size;

  *psize = bytes == error_mark_node ? NULL_TREE : bytes;
  if (wholesizep)
    *wholesizep = var_size;
  return true;
}


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
emit_size_stmts (object_size_info *osi, gimple *stmt, tree wholesize_ssa,
		 tree wholesize_expr, tree size_ssa, tree size_expr)
{
  gimple_seq seq = NULL;

  /* Gimplify the wholesize and size expressions.  */
  if (!is_gimple_variable (wholesize_expr))
    wholesize_expr = force_gimple_operand (wholesize_expr, &seq, true, NULL);
  if (!is_gimple_variable (size_expr))
    {
      gimple_seq s;
      size_expr = force_gimple_operand (size_expr, &s, true, NULL);
      gimple_seq_add_seq (&seq, s);
    }

  /* Assign them to their SSAs.  */
  gassign *assign = gimple_build_assign (wholesize_ssa, wholesize_expr);
  gimple_seq_add_stmt (&seq, assign);
  assign = gimple_build_assign (size_ssa, size_expr);
  gimple_seq_add_stmt (&seq, assign);

  /* Define object size right before the object is defined, assuming that any
     statements involved in evaluation of the object size expression precede
     the definition statement.  For parameters, we don't have a definition
     statement, so insert into the first code basic block.  */
  gimple_stmt_iterator i;
  if (gimple_code (stmt) == GIMPLE_NOP)
    {
      basic_block first_bb = single_succ (ENTRY_BLOCK_PTR_FOR_FN (osi->fun));
      i = gsi_start_bb (first_bb);
    }
  else
    i = gsi_for_stmt (stmt);
  gsi_insert_seq_before (&i, seq, GSI_CONTINUE_LINKING);
}

static void
emit_size_phi_stmts (gimple *stmt, tree wholesize_ssa, tree *wholesizes,
		     tree size_ssa, tree *sizes)
{
  gphi *wholephi = create_phi_node (wholesize_ssa, gimple_bb (stmt));
  gphi *phi = create_phi_node (size_ssa, gimple_bb (stmt));
  gphi *obj_phi =  as_a <gphi *> (stmt);

  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      gimple_seq seq = NULL;

      /* If we built an expression, we will need to build statements
	 and insert them on the edge right away.  */
      if (!is_gimple_variable (wholesizes[i]))
	wholesizes[i] = force_gimple_operand (wholesizes[i], &seq, true, NULL);
      if (!is_gimple_variable (sizes[i]))
	{
	  gimple_seq s;
	  sizes[i] = force_gimple_operand (sizes[i], &s, true, NULL);
	  gimple_seq_add_seq (&seq, s);
	}

      if (seq)
	{
	  gimple_stmt_iterator gsi;
	  edge e = gimple_phi_arg_edge (obj_phi, i);

	  /* Put it at the end of the source block but right before the last
	     statement.  */
	  gsi = gsi_last_bb (e->src);
	  gsi_insert_seq_before (&gsi, seq, GSI_CONTINUE_LINKING);
	}

      add_phi_arg (wholephi, wholesizes[i],
		   gimple_phi_arg_edge (obj_phi, i),
		   gimple_phi_arg_location (obj_phi, i));

      add_phi_arg (phi, sizes[i],
		   gimple_phi_arg_edge (obj_phi, i),
		   gimple_phi_arg_location (obj_phi, i));
    }
}

/* Set upper bound to SIZE_MAX - 1 so that equality with (size_t) -1 fails.  */

static tree
size_bound_expr (tree sz)
{
  tree max = size_binop (MINUS_EXPR, TYPE_MAX_VALUE (sizetype), size_one_node);
  return fold_build2 (MIN_EXPR, sizetype, max, sz);
}

static void
eval_size_expr (struct object_size_info *osi, tree var, tree wholesize,
		tree *wholesize_expr, tree size, tree *size_expr)
{
  if (size_expr != NULL)
    {
      gcc_assert (*size_expr != error_mark_node);

      gimple *stmt = SSA_NAME_DEF_STMT (var);

      if (gimple_code (stmt) == GIMPLE_PHI)
	{
	  emit_size_phi_stmts (stmt, wholesize, wholesize_expr,
			       size, size_expr);
	  delete[] wholesize_expr;
	  delete[] size_expr;
	}
      else
	{
	  emit_size_stmts (osi, stmt, wholesize, *wholesize_expr, size,
			   size_bound_expr (*size_expr));
	  delete wholesize_expr;
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
	      release_ssa_name (object_whole_sizes[object_size_type][i]);
	      release_ssa_name (object_sizes[object_size_type][i]);
	      if (gimple_code (SSA_NAME_DEF_STMT (ssa_name (i))) == GIMPLE_PHI
		  && object_size_exprs[object_size_type][i])
		{
		  delete [] object_whole_size_exprs[object_size_type][i];
		  delete [] object_size_exprs[object_size_type][i];
		}
	      else
		{
		  delete object_whole_size_exprs[object_size_type][i];
		  delete object_size_exprs[object_size_type][i];
		}
	      object_whole_size_exprs[object_size_type][i] = NULL;
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
	eval_size_expr (osi, ssa_name (i),
			object_whole_sizes[object_size_type][i],
			object_whole_size_exprs[object_size_type][i],
			object_sizes[object_size_type][i],
			object_size_exprs[object_size_type][i]);
	object_whole_size_exprs[object_size_type][i] = NULL;
	object_size_exprs[object_size_type][i] = NULL;
      }
}

/* Compute __builtin_dynamic_object_size value for PTR and set *PSIZE to
   the resulting value.  OBJECT_SIZE_TYPE is the second argument to
   __builtin_dynamic_object_size.  Returns true on success and false when the
   object size could not be determined.  */

bool
compute_builtin_dyn_object_size (tree ptr, int object_size_type, tree *psize,
				 struct function *fun)
{
  gcc_assert (object_size_type >= 0 && object_size_type <= 3);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = NULL_TREE;

  if (TREE_CODE (ptr) == ADDR_EXPR)
    /* We assume that the caller will gimplify the expression.  If the
       expression depends on any SSA objects, its size expression is gimplified
       and returned, so the expression will definitely not depend on the cached
       objects.  */
    return addr_dyn_object_size (NULL, ptr, object_size_type, psize);

  if (TREE_CODE (ptr) != SSA_NAME
      || !POINTER_TYPE_P (TREE_TYPE (ptr)))
      return false;

  if (computed[object_size_type] == NULL)
    {
      if (optimize || object_size_type & 1)
	return false;

      /* Like with __builtin_object_size, when not optimizing, rather than
	 failing, make a small effort to determine the object size without the
	 full benefit of the (costly) computation below.  */
      gimple *def = SSA_NAME_DEF_STMT (ptr);
      if (gimple_code (def) == GIMPLE_ASSIGN)
	{
	  tree_code code = gimple_assign_rhs_code (def);
	  if (code == POINTER_PLUS_EXPR)
	    {
	      tree offset = gimple_assign_rhs2 (def);
	      ptr = gimple_assign_rhs1 (def);

	      if (compute_builtin_dyn_object_size (ptr, object_size_type,
						   psize))
		{
		  *psize = size_for_offset (*psize, offset, *psize, true);
		  return true;
		}
	    }
	}
      return false;
    }

  if (bitmap_bit_p (computed[object_size_type], SSA_NAME_VERSION (ptr)))
    goto out;

  struct object_size_info osi;
  bitmap_iterator bi;
  unsigned int i;

  if (num_ssa_names > object_sizes[object_size_type].length ())
    {
      object_sizes[object_size_type].safe_grow (num_ssa_names, true);
      object_size_exprs[object_size_type].safe_grow (num_ssa_names, true);
      object_whole_sizes[object_size_type].safe_grow (num_ssa_names, true);
      object_whole_size_exprs[object_size_type].safe_grow (num_ssa_names,
							   true);
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

/* Compute object_sizes for PTR, defined to VALUE, which is not an SSA_NAME.  */

static void
expr_object_size (struct object_size_info *osi, tree value, tree *sz,
		  tree *wholeszp)
{
  int object_size_type = osi->object_size_type;
  tree bytes = NULL_TREE, wholesz = NULL_TREE;

  if (TREE_CODE (value) == WITH_SIZE_EXPR)
    value = TREE_OPERAND (value, 0);

  if (TREE_CODE (value) == ADDR_EXPR)
    addr_dyn_object_size (osi, value, object_size_type, &bytes, &wholesz);

  if (bytes)
    STRIP_NOPS (bytes);

  if (wholesz)
    STRIP_NOPS (wholesz);

  *sz = bytes;
  *wholeszp = wholesz;
}

static tree
make_object_size_name (tree ssa_name, tree *val, struct function *fun)
{
  if (ssa_name != NULL_TREE)
    gcc_assert (*val == error_mark_node);
  else
    ssa_name = make_ssa_name_fn (fun, sizetype, 0);

  return ssa_name;
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
cache_object_size (struct object_size_info *osi, unsigned name, tree *sz,
		   tree *wholesz)
{
  int object_size_type = osi->object_size_type;
  struct function *fun = osi->fun;

  gcc_assert (sz && wholesz);

  maybe_update_dependency_loop (osi, name, *sz);

  /* Reuse SSA name if it was created for a dependency loop.  */
  object_sizes[object_size_type][name] =
    make_object_size_name (object_sizes[object_size_type][name],
			   object_size_exprs[object_size_type][name], fun);
  object_size_exprs[object_size_type][name] = sz;

  /* Likewise for whole object size.  */
  object_whole_sizes[object_size_type][name] =
    make_object_size_name (object_whole_sizes[object_size_type][name],
			   object_whole_size_exprs[object_size_type][name],
			   fun);
  object_whole_size_exprs[object_size_type][name] = wholesz;

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
      fprintf (dump_file, ", Object whole size: ");
      print_generic_expr (dump_file,
			  object_whole_sizes[object_size_type][name],
			  dump_flags);
      fprintf (dump_file, " = ");
      print_generic_expr (dump_file,
			  *object_whole_size_exprs[object_size_type][name],
			  dump_flags);
      fprintf (dump_file, "\n");
    }

  bitmap_set_bit (computed[object_size_type], name);
}

/* Copy SZ and then call cache_object_size above.  */

static void
cache_object_size_copy (struct object_size_info *osi, unsigned name, tree sz,
			tree wholesz)
{
  int object_size_type = osi->object_size_type;

  if (sz == NULL_TREE || wholesz == NULL_TREE)
    {
      /* If we are unable to determine the size of a circular dependency,
	 release its SSA.  */
      if (object_sizes[object_size_type][name] != NULL_TREE)
	{
	  release_ssa_name (object_sizes[object_size_type][name]);
	  release_ssa_name (object_whole_sizes[object_size_type][name]);
	}
      object_sizes[object_size_type][name] = NULL_TREE;
      object_size_exprs[object_size_type][name] = NULL;
      object_whole_sizes[object_size_type][name] = NULL_TREE;
      object_whole_size_exprs[object_size_type][name] = NULL;
      bitmap_set_bit (computed[object_size_type], name);
      if (dump_file)
	{
	  fprintf (dump_file, "caching UNKNOWN size for ");
	  print_generic_expr (dump_file, ssa_name (name), dump_flags);
	  fprintf (dump_file, "\n");
	}

      return;
    }

  cache_object_size (osi, name, new tree (sz), new tree (wholesz));
}

/* Use size of ORIG for DEST and return it.  */

static void
set_object_size_ssa (struct object_size_info *osi, tree dest, tree orig)
{
  collect_object_sizes_for (osi, orig);

  tree sz = object_sizes[osi->object_size_type][SSA_NAME_VERSION (orig)];
  tree wholesz =
    object_whole_sizes[osi->object_size_type][SSA_NAME_VERSION (orig)];

  cache_object_size_copy (osi, SSA_NAME_VERSION (dest), sz, wholesz);
}

/* Compute object_sizes for VAR, defined to the result of an assignment
   with operator POINTER_PLUS_EXPR.  Return true if the object size might
   need reexamination  later.  */

static void
plus_stmt_object_size (struct object_size_info *osi, tree var, gimple *stmt)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  tree op0, op1, bytes = NULL_TREE, wholevar = NULL_TREE;

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
      unsigned op0no = SSA_NAME_VERSION (op0);

      collect_object_sizes_for (osi, op0);
      if (object_sizes[object_size_type][op0no])
	{
	  bytes = object_sizes[object_size_type][op0no];
	  wholevar = object_whole_sizes[object_size_type][op0no];
	  bytes = size_for_offset (bytes, op1, wholevar, true);
	}
    }
  else if (TREE_CODE (op0) == ADDR_EXPR)
    {
      /* op0 will be ADDR_EXPR here.  */
      if (addr_dyn_object_size (osi, op0, object_size_type, &bytes, &wholevar))
	bytes = size_for_offset (bytes, op1, wholevar);
    }
  cache_object_size_copy (osi, varno, bytes, wholevar);
}

/* Compute object_sizes for PTR, defined to the result of a call.  */

static void
call_object_size (struct object_size_info *osi, tree ptr, gcall *call)
{
  gcc_assert (is_gimple_call (call));

  tree sz = alloc_object_size (call);
  cache_object_size_copy (osi, SSA_NAME_VERSION (ptr), sz, sz);
}

/* Find size of an object passed as a parameter to the function.  */

static void
parm_object_size (struct object_size_info *osi, tree var)
{
  tree parm = SSA_NAME_VAR (var);
  unsigned varno = SSA_NAME_VERSION (var);
  tree sz = NULL_TREE, wholesz = NULL_TREE;

  if (dump_file)
  {
	  fprintf (dump_file, "Object is a parameter: ");
	  print_generic_expr (dump_file, parm, dump_flags);
	  fprintf (dump_file, " which is %s a pointer type\n",
			  POINTER_TYPE_P (TREE_TYPE (parm)) ? "" : "not");
  }

  if (POINTER_TYPE_P (TREE_TYPE (parm)))
    {
      /* Look for access attribute.  */
      rdwr_map rdwr_idx;

      tree fndecl = osi->fun->decl;
      const attr_access *access = get_parm_access (rdwr_idx, parm, fndecl);
      tree typesize = TYPE_SIZE_UNIT (TREE_TYPE (TREE_TYPE (parm)));

      if (access && access->sizarg != UINT_MAX)
	{
	  tree fnargs = DECL_ARGUMENTS (fndecl);
	  tree arg = NULL_TREE;
	  unsigned argpos = 0;

	  /* Walk through the parameters to pick the size parameter and safely
	     scale it by the type size.  */
	  for (arg = fnargs; argpos != access->sizarg && arg;
	       arg = TREE_CHAIN (arg), ++argpos);

	  if (arg != NULL_TREE && INTEGRAL_TYPE_P (TREE_TYPE (arg)))
	    {
	      tree arrsz = get_or_create_ssa_default_def (osi->fun, arg);
	      if (arrsz != NULL_TREE)
		{
		  arrsz = fold_convert (sizetype, arrsz);
		  if (typesize)
		    {
		      tree res = fold_build2 (MULT_EXPR, sizetype, arrsz,
					      typesize);
		      tree check = fold_build2 (EXACT_DIV_EXPR, sizetype,
						TYPE_MAX_VALUE (sizetype),
						typesize);
		      check = fold_build2 (LT_EXPR, sizetype, arrsz, check);
		      arrsz = fold_build3 (COND_EXPR, sizetype, check, res,
					   size_zero_node);
		    }
		}
	      sz = wholesz = arrsz;
	    }
	}
    }
  else
      expr_object_size (osi, parm, &sz, &wholesz);

  cache_object_size_copy (osi, varno, sz, wholesz);
}

/* Compute object sizes for VAR.

   - For allocation GIMPLE_CALL like malloc or calloc object size is the size
     of the allocation.
   - For a memcpy like GIMPLE_CALL that always returns one of its arguments,
     the object size is object size of that argument.
   - For GIMPLE_PHI, compute a PHI node with sizes of all branches in the PHI
     node of the object.
   - For GIMPLE_ASSIGN, return the size of the object the SSA name points
     to.
   - For GIMPLE_NOP, if the variable is a function parameter, compute the size
     of the parameter.  */

static void
collect_object_sizes_for (struct object_size_info *osi, tree var)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  gimple *stmt;

  if (bitmap_bit_p (computed[object_size_type], varno))
    return;

  if (bitmap_set_bit (osi->visited, varno))
    {
      object_sizes[object_size_type][varno] = NULL_TREE;
      object_whole_sizes[object_size_type][varno] = NULL_TREE;
    }
  else
    {
      /* Add an SSA name but mark the expression as being an error_mark_node.
	 When we go back up the stack, the error_mark_node should get
	 overwritten by a proper expression.  */
      cache_object_size (osi, varno, &error_mark_node, &error_mark_node);
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
	      {
		tree sz, wholesz;
		expr_object_size (osi, rhs, &sz, &wholesz);
		cache_object_size_copy (osi, varno, sz, wholesz);
	      }
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
	      {
		tree sz, wholesz;
		expr_object_size (osi, arg, &sz, &wholesz);
		cache_object_size_copy (osi, varno, sz, wholesz);
	      }
	  }
	else
	  call_object_size (osi, var, call_stmt);
	break;
      }

    case GIMPLE_PHI:
      {
	unsigned i, num_args = gimple_phi_num_args (stmt);
	tree *sizes = new tree[num_args] ();
	tree *wholesizes = new tree[num_args] ();

	/* Bail out if any of the PHI arguments are non-SSA expressions or
	   if size of an argument cannot be determined.  */
	for (i = 0; i < gimple_phi_num_args (stmt); i++)
	  {
	    tree rhs = gimple_phi_arg_def (stmt, i);
	    tree sz, wholesz;

	    if (TREE_CODE (rhs) != SSA_NAME)
	      expr_object_size (osi, rhs, &sz, &wholesz);
	    else
	      {
		collect_object_sizes_for (osi, rhs);
		sz = object_sizes[object_size_type][SSA_NAME_VERSION (rhs)];
		wholesz =
		  object_whole_sizes[object_size_type][SSA_NAME_VERSION (rhs)];
	      }

	    if (sz == NULL_TREE || wholesz == NULL_TREE)
	      break;

	    sizes[i] = sz;
	    wholesizes[i] = wholesz;
	  }

	/* Record all possible sizes to build our PHI node later.  */
	if (i == gimple_phi_num_args (stmt))
	  cache_object_size (osi, varno, sizes, wholesizes);
	else
	  {
	    delete[] sizes;
	    delete[] wholesizes;
	    cache_object_size_copy (osi, varno, NULL_TREE, NULL_TREE);
	  }
	break;
      }

    case GIMPLE_NOP:
      if (SSA_NAME_VAR (var) && TREE_CODE (SSA_NAME_VAR (var)) == PARM_DECL)
	parm_object_size (osi, var);
      else
	/* Uninitialized SSA names point nowhere.  */
	cache_object_size_copy (osi, varno, NULL_TREE, NULL_TREE);
      break;

    /* Bail out for all other cases.  */
    case GIMPLE_ASM:
      cache_object_size_copy (osi, varno, NULL_TREE, NULL_TREE);
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
      object_whole_sizes[object_size_type].safe_grow (num_ssa_names, true);
      object_whole_size_exprs[object_size_type].safe_grow (num_ssa_names,
							   true);
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
      object_whole_sizes[object_size_type].release ();
      object_whole_size_exprs[object_size_type].release ();
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
