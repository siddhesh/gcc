/* __builtin_object_size (ptr, object_size_type) computation
   Copyright (C) 2004-2021 Free Software Foundation, Inc.
   Contributed by Jakub Jelinek <jakub@redhat.com>

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

struct object_size_info
{
  int object_size_type;
  unsigned char phase;
  bitmap visited, reexamine, deploop_ssa;
  vec<unsigned> deploop;
};

static tree compute_object_offset (const_tree, const_tree);
static bool addr_object_size (struct object_size_info *,
			      const_tree, int, tree *);
static tree alloc_object_size (const gcall *, int);
static tree pass_through_call (const gcall *);
static void collect_object_sizes_for (struct object_size_info *, tree);
static void expr_object_size (struct object_size_info *, tree, tree);
static void merge_object_sizes (struct object_size_info *, tree, tree, tree);
static void plus_stmt_object_size (struct object_size_info *, tree, gimple *);
static void cond_expr_object_size (struct object_size_info *, tree, gimple *);
static void init_offset_limit (void);

/* object_sizes[0] is upper bound for number of bytes till the end of
   the object.
   object_sizes[1] is upper bound for number of bytes till the end of
   the subobject (innermost array or field with address taken).
   object_sizes[2] is lower bound for number of bytes till the end of
   the object and object_sizes[3] lower bound for subobject.  */
static vec<tree> object_sizes[4];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[4];

/* Maximum value of offset we consider to be addition.  */
static tree offset_limit;

static inline unsigned HOST_WIDE_INT
unknown (int object_size_type)
{
  return ((unsigned HOST_WIDE_INT) -((object_size_type >> 1) ^ 1));
}

static inline unsigned HOST_WIDE_INT
initval (int object_size_type)
{
  return ((unsigned HOST_WIDE_INT) -(((object_size_type ^ 2) >> 1) ^ 1));
}

static inline tree
size_unknown (int object_size_type)
{
  return size_int (unknown (object_size_type));
}

static inline bool
size_unknown_p (tree val, int object_size_type)
{
  return (tree_fits_uhwi_p (val)
	  && tree_to_uhwi (val) == unknown (object_size_type));
}

static inline void
object_sizes_grow (int object_size_type)
{
  if (num_ssa_names > object_sizes[object_size_type].length ())
    object_sizes[object_size_type].safe_grow (num_ssa_names, true);
}

static inline void
object_sizes_release (int object_size_type)
{
  object_sizes[object_size_type].release ();
}

static inline bool
object_sizes_unknown_p (int object_size_type, unsigned varno)
{
  return (tree_fits_uhwi_p (object_sizes[object_size_type][varno])
	  && (tree_to_uhwi (object_sizes[object_size_type][varno])
	      == unknown (object_size_type)));
}

static inline tree
object_sizes_get (struct object_size_info *osi, unsigned varno)
{
  return object_sizes[osi->object_size_type][varno];
}

static inline void
object_sizes_initialize (struct object_size_info *osi, unsigned varno)
{
  object_sizes[osi->object_size_type][varno]
    = size_int (initval (osi->object_size_type));
}

static inline void
object_sizes_set (struct object_size_info *osi, unsigned varno, tree val)
{
  if (osi->phase == 1)
    {
      object_sizes[osi->object_size_type][varno] = val;
      bitmap_clear_bit (osi->reexamine, varno);
      return;
    }

  int object_size_type = osi->object_size_type;
  tree oldval = object_sizes[object_size_type][varno];

  enum tree_code code = object_size_type & 2 ? MIN_EXPR : MAX_EXPR;

  if (TREE_CODE (oldval) != INTEGER_CST
      || compare_tree_int (oldval, initval (object_size_type)) != 0)
    val = size_binop (code, oldval, val);

  object_sizes[object_size_type][varno] = val;

  if (TREE_CODE (val) != INTEGER_CST)
    bitmap_set_bit (osi->reexamine, varno);
}

/* Initialize OFFSET_LIMIT variable.  */
static void
init_offset_limit (void)
{
  offset_limit = size_binop (RSHIFT_EXPR, TYPE_MAX_VALUE (sizetype),
			     size_int (1));
}

/* Bytes at end of the object with SZ from offset OFFSET. */

static tree
size_for_offset (tree sz, tree offset)
{
  return size_binop (MINUS_EXPR, size_binop (MAX_EXPR, sz, offset), offset);
}

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
      off = size_binop (PLUS_EXPR, DECL_FIELD_OFFSET (t),
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
      off = size_binop (MULT_EXPR, unit_size, t);
      break;

    case MEM_REF:
      gcc_assert (TREE_CODE (TREE_OPERAND (expr, 0)) == ADDR_EXPR);
      return wide_int_to_tree (sizetype, mem_ref_offset (expr));

    default:
      return error_mark_node;
    }

  return size_binop (code, base, off);
}

/* Returns the size of the object designated by DECL considering its
   initializer if it either has one or if it would not affect its size,
   otherwise the size of the object without the initializer when MIN
   is true, else null.  An object's initializer affects the object's
   size if it's a struct type with a flexible array member.  */

tree
decl_init_size (tree decl, bool min)
{
  tree size = DECL_SIZE_UNIT (decl);
  tree type = TREE_TYPE (decl);
  if (TREE_CODE (type) != RECORD_TYPE)
    return size;

  tree last = last_field (type);
  if (!last)
    return size;

  tree last_type = TREE_TYPE (last);
  if (TREE_CODE (last_type) != ARRAY_TYPE
      || TYPE_SIZE (last_type))
    return size;

  /* Use TYPE_SIZE_UNIT; DECL_SIZE_UNIT sometimes reflects the size
     of the initializer and sometimes doesn't.  */
  size = TYPE_SIZE_UNIT (type);
  tree ref = build3 (COMPONENT_REF, type, decl, last, NULL_TREE);
  tree compsize = component_ref_size (ref);
  if (!compsize)
    return min ? size : NULL_TREE;

  /* The size includes tail padding and initializer elements.  */
  tree pos = byte_position (last);
  size = fold_build2 (PLUS_EXPR, TREE_TYPE (size), pos, compsize);
  return size;
}

/* Compute __builtin_object_size for PTR, which is a ADDR_EXPR.
   OBJECT_SIZE_TYPE is the second argument from __builtin_object_size.
   If unknown, return size_unknown (object_size_type).  */

static bool
addr_object_size (struct object_size_info *osi, const_tree ptr,
		  int object_size_type, tree *psize)
{
  tree pt_var, pt_var_size = NULL_TREE, var_size, bytes;

  gcc_assert (TREE_CODE (ptr) == ADDR_EXPR);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = size_unknown (object_size_type);

  pt_var = TREE_OPERAND (ptr, 0);
  while (handled_component_p (pt_var))
    pt_var = TREE_OPERAND (pt_var, 0);

  if (!pt_var)
    return false;

  if (TREE_CODE (pt_var) == MEM_REF)
    {
      tree sz;

      if (!osi || (object_size_type & 1) != 0
	  || TREE_CODE (TREE_OPERAND (pt_var, 0)) != SSA_NAME)
	{
	  compute_builtin_object_size (TREE_OPERAND (pt_var, 0),
				       object_size_type & ~1, &sz);
	}
      else
	{
	  tree var = TREE_OPERAND (pt_var, 0);
	  collect_object_sizes_for (osi, var);
	  if (bitmap_bit_p (computed[object_size_type],
			    SSA_NAME_VERSION (var)))
	    sz = object_sizes_get (osi, SSA_NAME_VERSION (var));
	  else
	    sz = size_unknown (object_size_type);
	}
      if (!size_unknown_p (sz, object_size_type))
	{
	  tree offset = TREE_OPERAND (pt_var, 1);
	  if (TREE_CODE (offset) != INTEGER_CST
	      || TREE_CODE (sz) != INTEGER_CST)
	    sz = size_unknown (object_size_type);
	  else
	    sz = size_for_offset (sz, offset);
	}

      if (!size_unknown_p (sz, object_size_type)
	  && TREE_CODE (sz) == INTEGER_CST
	  && tree_int_cst_lt (sz, offset_limit))
	pt_var_size = sz;
    }
  else if (DECL_P (pt_var))
    {
      pt_var_size = decl_init_size (pt_var, object_size_type & 2);
      if (!pt_var_size)
	return false;
    }
  else if (TREE_CODE (pt_var) == STRING_CST)
    pt_var_size = TYPE_SIZE_UNIT (TREE_TYPE (pt_var));
  else
    return false;

  if (pt_var_size)
    {
      /* Validate the size determined above.  */
      if (tree_int_cst_le (offset_limit, pt_var_size))
	return false;
    }

  if (pt_var != TREE_OPERAND (ptr, 0))
    {
      tree var;

      if (object_size_type & 1)
	{
	  var = TREE_OPERAND (ptr, 0);

	  while (var != pt_var
		 && TREE_CODE (var) != BIT_FIELD_REF
		 && TREE_CODE (var) != COMPONENT_REF
		 && TREE_CODE (var) != ARRAY_REF
		 && TREE_CODE (var) != ARRAY_RANGE_REF
		 && TREE_CODE (var) != REALPART_EXPR
		 && TREE_CODE (var) != IMAGPART_EXPR)
	    var = TREE_OPERAND (var, 0);
	  if (var != pt_var && TREE_CODE (var) == ARRAY_REF)
	    var = TREE_OPERAND (var, 0);
	  if (! TYPE_SIZE_UNIT (TREE_TYPE (var))
	      || ! tree_fits_uhwi_p (TYPE_SIZE_UNIT (TREE_TYPE (var)))
	      || (pt_var_size
		  && tree_int_cst_lt (pt_var_size,
				      TYPE_SIZE_UNIT (TREE_TYPE (var)))))
	    var = pt_var;
	  else if (var != pt_var && TREE_CODE (pt_var) == MEM_REF)
	    {
	      tree v = var;
	      /* For &X->fld, compute object size only if fld isn't the last
		 field, as struct { int i; char c[1]; } is often used instead
		 of flexible array member.  */
	      while (v && v != pt_var)
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
		    while (v != pt_var && TREE_CODE (v) == COMPONENT_REF)
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
		    while (v != pt_var && TREE_CODE (v) == COMPONENT_REF)
		      if (TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
			  != UNION_TYPE
			  && TREE_CODE (TREE_TYPE (TREE_OPERAND (v, 0)))
			  != QUAL_UNION_TYPE)
			break;
		      else
			v = TREE_OPERAND (v, 0);
		    if (v != pt_var)
		      v = NULL_TREE;
		    else
		      v = pt_var;
		    break;
		  default:
		    v = pt_var;
		    break;
		  }
	      if (v == pt_var)
		var = pt_var;
	    }
	}
      else
	var = pt_var;

      if (var != pt_var)
	var_size = TYPE_SIZE_UNIT (TREE_TYPE (var));
      else if (!pt_var_size)
	return false;
      else
	var_size = pt_var_size;
      bytes = compute_object_offset (TREE_OPERAND (ptr, 0), var);
      if (bytes != error_mark_node)
	{
	  if (TREE_CODE (bytes) == INTEGER_CST
	      && tree_int_cst_lt (var_size, bytes))
	    bytes = size_zero_node;
	  else
	    bytes = size_binop (MINUS_EXPR, var_size, bytes);
	}
      if (var != pt_var
	  && pt_var_size
	  && TREE_CODE (pt_var) == MEM_REF
	  && bytes != error_mark_node)
	{
	  tree bytes2 = compute_object_offset (TREE_OPERAND (ptr, 0), pt_var);
	  if (bytes2 != error_mark_node)
	    {
	      if (TREE_CODE (bytes2) == INTEGER_CST
		  && tree_int_cst_lt (pt_var_size, bytes2))
		bytes2 = size_zero_node;
	      else
		bytes2 = size_binop (MINUS_EXPR, pt_var_size, bytes2);
	      bytes = size_binop (MIN_EXPR, bytes, bytes2);
	    }
	}
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
   If unknown, return size_unknown (object_size_type).  */

static tree
alloc_object_size (const gcall *call, int object_size_type)
{
  gcc_assert (is_gimple_call (call));

  tree calltype;
  if (tree callfn = gimple_call_fndecl (call))
    calltype = TREE_TYPE (callfn);
  else
    calltype = gimple_call_fntype (call);

  if (!calltype)
    return size_unknown (object_size_type);

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

  if (arg1 < 0 || arg1 >= (int)gimple_call_num_args (call)
      || TREE_CODE (gimple_call_arg (call, arg1)) != INTEGER_CST
      || (arg2 >= 0
	  && (arg2 >= (int)gimple_call_num_args (call)
	      || TREE_CODE (gimple_call_arg (call, arg2)) != INTEGER_CST)))
    return size_unknown (object_size_type);

  tree bytes = NULL_TREE;
  if (arg2 >= 0)
    bytes = size_binop (MULT_EXPR,
	fold_convert (sizetype, gimple_call_arg (call, arg1)),
	fold_convert (sizetype, gimple_call_arg (call, arg2)));
  else if (arg1 >= 0)
    bytes = fold_convert (sizetype, gimple_call_arg (call, arg1));

  return bytes;
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

/* Recursively look for presence of ORIG in EXPR.  Return true if it was found
   and there was a MINUS_EXPR in the pathway.  */

static bool
reducing_size (tree orig, tree expr, bool found_minus)
{
  switch (TREE_CODE (expr))
    {
    case INTEGER_CST:
      return false;
    case SSA_NAME:
      if (SSA_NAME_VERSION (orig) == SSA_NAME_VERSION (expr))
	return found_minus;
      return false;
    case MIN_EXPR:
    case MAX_EXPR:
      return (reducing_size (orig, TREE_OPERAND (expr, 0), found_minus)
	      || reducing_size (orig, TREE_OPERAND (expr, 1), found_minus));
    case PLUS_EXPR:
      /* Negative object offsets are not supported.  */
      gcc_checking_assert (TREE_CODE (TREE_OPERAND (expr, 1)) == INTEGER_CST);
      gcc_checking_assert (tree_int_cst_lt (offset_limit,
					    TREE_OPERAND (expr, 1)));
      /* Fall through.  */
    case MINUS_EXPR:
      gcc_checking_assert (TREE_CODE (TREE_OPERAND (expr, 1)) == INTEGER_CST);
      if (reducing_size (orig, TREE_OPERAND (expr, 0), true))
	return true;
      return false;
    default:
      gcc_unreachable ();
    }
}

/* Return a constant size estimate for the input SZEXPR and update it with a
   simplified expression.  */

static tree
estimate_size (object_size_info *osi, tree size,
	       vec<tree> &deploop_sizes)
{
  enum tree_code code = TREE_CODE (size);
  int object_size_type = osi->object_size_type;

  switch (code)
    {
    case INTEGER_CST:
      return size;
    case SSA_NAME:
      if (!deploop_sizes[SSA_NAME_VERSION (size)])
	{
	  unsigned i = SSA_NAME_VERSION (size);
	  unsigned varno = osi->deploop[i];
	  tree szexpr = object_sizes_get (osi, varno);

	  if (size_unknown_p (szexpr, object_size_type))
	    deploop_sizes[i] = size_unknown (object_size_type);
	  else if (reducing_size (size, szexpr, false))
	    deploop_sizes[i] = size_int (0);
	  else
	    deploop_sizes[i] = size_int (initval (object_size_type));
	}
      return deploop_sizes[SSA_NAME_VERSION (size)];
    case MIN_EXPR:
    case MAX_EXPR:
	{
	  tree op0 = estimate_size (osi, TREE_OPERAND (size, 0),
				    deploop_sizes);
	  tree op1 = estimate_size (osi, TREE_OPERAND (size, 1),
				    deploop_sizes);
	  if (size_unknown_p (op0, object_size_type)
	      || size_unknown_p (op1, object_size_type))
	    return size_unknown (object_size_type);
	  return size_binop (code, op0, op1);
	}
    case MINUS_EXPR:
    case PLUS_EXPR:
	{
	  tree ret = estimate_size (osi, TREE_OPERAND (size, 0),
				    deploop_sizes);

	  if (size_unknown_p (ret, object_size_type))
	    return size_unknown (object_size_type);

	  tree off = TREE_OPERAND (size, 1);
	  gcc_checking_assert (TREE_CODE (off) == INTEGER_CST);

	  if (code == PLUS_EXPR)
	    off = fold_build1 (NEGATE_EXPR, sizetype, off);

	  if (tree_int_cst_le (ret, off))
	    return size_int (0);
	  return size_binop (MINUS_EXPR, ret, off);
	}
    default:
      gcc_unreachable ();
    }
}

/* Replace dependency loop SSA names with their actual values.  */

static void
resolve_dependency_loops (struct object_size_info *osi)
{
  bitmap_iterator bi;
  unsigned int i;
  int object_size_type = osi->object_size_type;
  vec<tree> deploop_sizes;

  deploop_sizes.create (0);
  deploop_sizes.safe_grow_cleared (num_ssa_names, true);

  /* Update the self-referencing size expressions until they don't change
     anymore.  */
  bool changed;
  do
    {
      changed = false;
      EXECUTE_IF_SET_IN_BITMAP (osi->deploop_ssa, 0, i, bi)
	{
	  tree sz = ssa_name (i);
	  unsigned varno = osi->deploop[i];
	  tree szexpr = object_sizes_get (osi, varno);

	  if (TREE_CODE (szexpr) == INTEGER_CST)
	    continue;

	  sz = estimate_size (osi, szexpr, deploop_sizes);

	  if (size_unknown_p (sz, object_size_type))
	    {
	      object_sizes_set (osi, varno, sz);
	      continue;
	    }

	  /* If we have a new estimate, then update it.  */
	  if (tree_int_cst_compare (deploop_sizes[i], sz) != 0)
	    {
	      deploop_sizes[i] = sz;
	      changed = true;
	    }
	}
    }
  while (changed);

  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "After dependency resolution:\n");
      EXECUTE_IF_SET_IN_BITMAP (osi->deploop_ssa, 0, i, bi)
	{
	  fprintf (dump_file, "  ");
	  print_generic_expr (dump_file, ssa_name (i), dump_flags);
	  fprintf (dump_file, ": ");
	  if (deploop_sizes[i])
	    print_generic_expr (dump_file, deploop_sizes[i], dump_flags);
	  else
	    fprintf (dump_file, "(null)");
	  fprintf (dump_file, "\n");
	}
    }

  /* Finally, update all sizes that were marked to be reexamined so that they
     get their final sizes.  */
  bitmap reexamine = BITMAP_ALLOC (NULL);
  bitmap_copy (reexamine, osi->reexamine);
  EXECUTE_IF_SET_IN_BITMAP (reexamine, 0, i, bi)
    {
      tree sz = estimate_size (osi, object_sizes_get (osi, i), deploop_sizes);
      object_sizes_set (osi, i, sz);
    }

  /* Release all the SSA names we created.  */
  EXECUTE_IF_SET_IN_BITMAP (osi->deploop_ssa, 0, i, bi)
    release_ssa_name (ssa_name (i));

  BITMAP_FREE (reexamine);
  deploop_sizes.release ();
}

/* Compute __builtin_object_size value for PTR and set *PSIZE to
   the resulting value.  If the declared object is known and PDECL
   is nonnull, sets *PDECL to the object's DECL.  OBJECT_SIZE_TYPE
   is the second argument   to __builtin_object_size.
   Returns true on success and false when the object size could not
   be determined.  */

bool
compute_builtin_object_size (tree ptr, int object_size_type,
			     tree *psize)
{
  gcc_assert (object_size_type >= 0 && object_size_type <= 3);

  /* Set to unknown and overwrite just before returning if the size
     could be determined.  */
  *psize = size_unknown (object_size_type);

  if (! offset_limit)
    init_offset_limit ();

  if (TREE_CODE (ptr) == ADDR_EXPR)
    return addr_object_size (NULL, ptr, object_size_type, psize);

  if (TREE_CODE (ptr) != SSA_NAME
      || !POINTER_TYPE_P (TREE_TYPE (ptr)))
      return false;

  if (computed[object_size_type] == NULL)
    {
      if (optimize || object_size_type & 1)
	return false;

      /* When not optimizing, rather than failing, make a small effort
	 to determine the object size without the full benefit of
	 the (costly) computation below.  */
      gimple *def = SSA_NAME_DEF_STMT (ptr);
      if (gimple_code (def) == GIMPLE_ASSIGN)
	{
	  tree_code code = gimple_assign_rhs_code (def);
	  if (code == POINTER_PLUS_EXPR)
	    {
	      tree offset = gimple_assign_rhs2 (def);
	      ptr = gimple_assign_rhs1 (def);

	      if (tree_fits_shwi_p (offset)
		  && compute_builtin_object_size (ptr, object_size_type,
						  psize))
		{
		  /* Return zero when the offset is out of bounds.  */
		  *psize = size_for_offset (*psize, offset);
		  return true;
		}
	    }
	}
      return false;
    }

  struct object_size_info osi;
  osi.object_size_type = object_size_type;
  if (!bitmap_bit_p (computed[object_size_type], SSA_NAME_VERSION (ptr)))
    {
      bitmap_iterator bi;
      unsigned int i;

      object_sizes_grow (object_size_type);
      if (dump_file)
	{
	  fprintf (dump_file, "Computing %s %sobject size for ",
		   (object_size_type & 2) ? "minimum" : "maximum",
		   (object_size_type & 1) ? "sub" : "");
	  print_generic_expr (dump_file, ptr, dump_flags);
	  fprintf (dump_file, ":\n");
	}

      osi.phase = 0;
      osi.visited = BITMAP_ALLOC (NULL);
      osi.reexamine = BITMAP_ALLOC (NULL);
      osi.deploop_ssa = BITMAP_ALLOC (NULL);
      osi.deploop.create (0);
      collect_object_sizes_for (&osi, ptr);

      osi.phase = 1;
      if (!bitmap_empty_p (osi.reexamine))
	resolve_dependency_loops (&osi);
      gcc_checking_assert (bitmap_empty_p (osi.reexamine));

      /* Debugging dumps.  */
      if (dump_file)
	{
	  EXECUTE_IF_SET_IN_BITMAP (osi.visited, 0, i, bi)
	    if (!object_sizes_unknown_p (object_size_type, i))
	      {
		print_generic_expr (dump_file, ssa_name (i),
				    dump_flags);
		fprintf (dump_file,
			 ": %s %sobject size ",
			 (object_size_type & 2) ? "minimum" : "maximum",
			 (object_size_type & 1) ? "sub" : "");
		print_generic_expr (dump_file, object_sizes_get (&osi, i),
				    dump_flags);
		fprintf (dump_file, "\n");
	      }
	}

      osi.deploop.release();
      BITMAP_FREE (osi.deploop_ssa);
      BITMAP_FREE (osi.reexamine);
      BITMAP_FREE (osi.visited);
    }

  *psize = object_sizes_get (&osi, SSA_NAME_VERSION (ptr));
  return !size_unknown_p (*psize, object_size_type);
}

/* Compute object_sizes for PTR, defined to VALUE, which is not an SSA_NAME.  */

static void
expr_object_size (struct object_size_info *osi, tree ptr, tree value)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (ptr);
  tree bytes;

  gcc_assert (!object_sizes_unknown_p (object_size_type, varno));

  if (TREE_CODE (value) == WITH_SIZE_EXPR)
    value = TREE_OPERAND (value, 0);

  /* Pointer variables should have been handled by merge_object_sizes.  */
  gcc_assert (TREE_CODE (value) != SSA_NAME
	      || !POINTER_TYPE_P (TREE_TYPE (value)));

  if (TREE_CODE (value) == ADDR_EXPR)
    addr_object_size (osi, value, object_size_type, &bytes);
  else
    bytes = size_unknown (object_size_type);

  object_sizes_set (osi, varno, bytes);
}


/* Compute object_sizes for PTR, defined to the result of a call.  */

static void
call_object_size (struct object_size_info *osi, tree ptr, gcall *call)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (ptr);

  gcc_assert (is_gimple_call (call));

  gcc_assert (!object_sizes_unknown_p (object_size_type, varno));

  object_sizes_set (osi, varno, alloc_object_size (call, object_size_type));
}


/* Compute object_sizes for PTR, defined to an unknown value.  */

static void
unknown_object_size (struct object_size_info *osi, tree ptr)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (ptr);

  gcc_checking_assert (!object_sizes_unknown_p (object_size_type, varno));

  object_sizes_set (osi, varno, size_unknown (object_size_type));
}


/* Merge object sizes of ORIG + OFFSET into DEST.  */

static void
merge_object_sizes (struct object_size_info *osi, tree dest, tree orig,
		    tree offset)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (dest);
  tree orig_bytes;

  if (object_sizes_unknown_p (object_size_type, varno))
    return;
  if (tree_int_cst_le (offset_limit, offset))
    {
      object_sizes_set (osi, varno, size_unknown (object_size_type));
      return;
    }

  collect_object_sizes_for (osi, orig);

  orig_bytes = object_sizes_get (osi, SSA_NAME_VERSION (orig));
  if (!size_unknown_p (orig_bytes, object_size_type)
      && !integer_zerop (offset))
    orig_bytes = size_for_offset (orig_bytes, offset);

  object_sizes_set (osi, varno, orig_bytes);
}


/* Compute object_sizes for VAR, defined to the result of an assignment
   with operator POINTER_PLUS_EXPR.  */

static void
plus_stmt_object_size (struct object_size_info *osi, tree var, gimple *stmt)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  tree bytes;
  tree op0, op1;

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

  if (object_sizes_unknown_p (object_size_type, varno))
    return;

  /* Handle PTR + OFFSET here.  */
  if (TREE_CODE (op1) == INTEGER_CST
      && (TREE_CODE (op0) == SSA_NAME
	  || TREE_CODE (op0) == ADDR_EXPR))
    {
      if (TREE_CODE (op0) == SSA_NAME)
	{
	  merge_object_sizes (osi, var, op0, op1);
	  return;
	}
      else
	{
          /* op0 will be ADDR_EXPR here.  */
	  addr_object_size (osi, op0, object_size_type, &bytes);
	  if (size_unknown_p (bytes, object_size_type))
	    ;
	  else if (tree_int_cst_lt (offset_limit, op1))
	    bytes = size_unknown (object_size_type);
	  else if (!integer_zerop (op1))
	    bytes = size_for_offset (bytes, op1);
	}
    }
  else
    bytes = size_unknown (object_size_type);

  object_sizes_set (osi, varno, bytes);
}


/* Compute object_sizes for VAR, defined at STMT, which is
   a COND_EXPR.  */

static void
cond_expr_object_size (struct object_size_info *osi, tree var, gimple *stmt)
{
  tree then_, else_;
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);

  gcc_assert (gimple_assign_rhs_code (stmt) == COND_EXPR);

  if (object_sizes_unknown_p (object_size_type, varno))
    return;

  then_ = gimple_assign_rhs2 (stmt);
  else_ = gimple_assign_rhs3 (stmt);

  if (TREE_CODE (then_) == SSA_NAME)
    merge_object_sizes (osi, var, then_, size_int (0));
  else
    expr_object_size (osi, var, then_);

  if (object_sizes_unknown_p (object_size_type, varno))
    return;

  if (TREE_CODE (else_) == SSA_NAME)
    merge_object_sizes (osi, var, else_, size_int (0));
  else
    expr_object_size (osi, var, else_);
}

/* Compute object sizes for VAR.
   For ADDR_EXPR an object size is the number of remaining bytes
   to the end of the object (where what is considered an object depends on
   OSI->object_size_type).
   For allocation GIMPLE_CALL like malloc or calloc object size is the size
   of the allocation.
   For POINTER_PLUS_EXPR where second operand is a constant integer,
   object size is object size of the first operand minus the constant.
   If the constant is bigger than the number of remaining bytes until the
   end of the object, object size is 0, but if it is instead a pointer
   subtraction, object size is size_unknown (object_size_type).
   To differentiate addition from subtraction, ADDR_EXPR returns
   size_unknown (object_size_type) for all objects bigger than half of the
   address space, and constants less than half of the address space are
   considered addition, while bigger constants subtraction.
   For a memcpy like GIMPLE_CALL that always returns one of its arguments, the
   object size is object size of that argument.
   Otherwise, object size is the maximum of object sizes of variables
   that it might be set to.  */

static void
collect_object_sizes_for (struct object_size_info *osi, tree var)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  gimple *stmt;

  if (bitmap_bit_p (computed[object_size_type], varno))
    return;

  /* We want to evaluate the self-referencing object only once.  */
  if (bitmap_set_bit (osi->visited, varno))
    {
      /* Initialize to 0 for maximum size and M1U for minimum size so that
	 it gets immediately overridden.  */
      object_sizes_initialize (osi, varno);
    }
  else
    {
      /* Found a dependency loop.  Mark it for later resolution.  */
      tree ssa = make_ssa_name (sizetype);
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  print_generic_expr (dump_file, var, dump_flags);
	  fprintf (dump_file, ": Found a dependency loop, marking with ");
	  print_generic_expr (dump_file, ssa, dump_flags);
	  fprintf (dump_file, "\n");
	}
      object_sizes_set (osi, varno, ssa);
      /* Try not to grow too often.  The exponential growth in vec should
	 handle it, but give it a leg up.  */
      if (osi->deploop.length () < num_ssa_names)
	osi->deploop.safe_grow (num_ssa_names * 2);
      osi->deploop[SSA_NAME_VERSION (ssa)] = varno;
      bitmap_set_bit (osi->deploop_ssa, SSA_NAME_VERSION (ssa));
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
	else if (gimple_assign_rhs_code (stmt) == COND_EXPR)
	  cond_expr_object_size (osi, var, stmt);
        else if (gimple_assign_single_p (stmt)
                 || gimple_assign_unary_nop_p (stmt))
          {
            if (TREE_CODE (rhs) == SSA_NAME
                && POINTER_TYPE_P (TREE_TYPE (rhs)))
	      merge_object_sizes (osi, var, rhs, size_int (0));
            else
              expr_object_size (osi, var, rhs);
          }
        else
	  unknown_object_size (osi, var);
        break;
      }

    case GIMPLE_CALL:
      {
	gcall *call_stmt = as_a <gcall *> (stmt);
        tree arg = pass_through_call (call_stmt);
        if (arg)
          {
            if (TREE_CODE (arg) == SSA_NAME
                && POINTER_TYPE_P (TREE_TYPE (arg)))
	      merge_object_sizes (osi, var, arg, size_int (0));
            else
              expr_object_size (osi, var, arg);
          }
        else
          call_object_size (osi, var, call_stmt);
	break;
      }

    case GIMPLE_ASM:
      /* Pointers defined by __asm__ statements can point anywhere.  */
      object_sizes_set (osi, varno, size_unknown (object_size_type));
      break;

    case GIMPLE_NOP:
      if (SSA_NAME_VAR (var)
	  && TREE_CODE (SSA_NAME_VAR (var)) == PARM_DECL)
	expr_object_size (osi, var, SSA_NAME_VAR (var));
      else
	/* Uninitialized SSA names point nowhere.  */
	object_sizes_set (osi, varno, size_unknown (object_size_type));
      break;

    case GIMPLE_PHI:
      {
	unsigned i;

	for (i = 0; i < gimple_phi_num_args (stmt); i++)
	  {
	    tree rhs = gimple_phi_arg (stmt, i)->def;

	    if (object_sizes_unknown_p (object_size_type, varno))
	      break;

	    if (TREE_CODE (rhs) == SSA_NAME)
	      merge_object_sizes (osi, var, rhs, size_int (0));
	    else
	      expr_object_size (osi, var, rhs);
	  }
	break;
      }

    default:
      gcc_unreachable ();
    }
  bitmap_set_bit (computed[object_size_type], varno);
}


/* Initialize data structures for the object size computation.  */

void
init_object_sizes (void)
{
  int object_size_type;

  if (computed[0])
    return;

  for (object_size_type = 0; object_size_type <= 3; object_size_type++)
    {
      object_sizes_grow (object_size_type);
      computed[object_size_type] = BITMAP_ALLOC (NULL);
    }

  init_offset_limit ();
}


/* Destroy data structures after the object size computation.  */

void
fini_object_sizes (void)
{
  int object_size_type;

  for (object_size_type = 0; object_size_type <= 3; object_size_type++)
    {
      object_sizes_release (object_size_type);
      BITMAP_FREE (computed[object_size_type]);
    }
}

/* Dummy valueize function.  */

static tree
do_valueize (tree t)
{
  return t;
}

static unsigned int
object_sizes_execute (function *fun, bool insert_min_max_p)
{
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      gimple_stmt_iterator i;
      for (i = gsi_start_bb (bb); !gsi_end_p (i); gsi_next (&i))
	{
	  tree result;
	  gimple *call = gsi_stmt (i);
	  if (!gimple_call_builtin_p (call, BUILT_IN_OBJECT_SIZE))
	    continue;

	  tree lhs = gimple_call_lhs (call);
	  if (!lhs)
	    continue;

	  init_object_sizes ();

	  /* If insert_min_max_p, only attempt to fold
	     __builtin_object_size (x, 1) and __builtin_object_size (x, 3),
	     and rather than folding the builtin to the constant if any,
	     create a MIN_EXPR or MAX_EXPR of the __builtin_object_size
	     call result and the computed constant.  */
	  if (insert_min_max_p)
	    {
	      tree ost = gimple_call_arg (call, 1);
	      if (tree_fits_uhwi_p (ost))
		{
		  unsigned HOST_WIDE_INT object_size_type = tree_to_uhwi (ost);
		  tree ptr = gimple_call_arg (call, 0);
		  if ((object_size_type == 1 || object_size_type == 3)
		      && (TREE_CODE (ptr) == ADDR_EXPR
			  || TREE_CODE (ptr) == SSA_NAME))
		    {
		      tree type = TREE_TYPE (lhs);
		      tree bytes;
		      if (compute_builtin_object_size (ptr, object_size_type,
						       &bytes))
			{
			  tree tem = make_ssa_name (type);
			  gimple_call_set_lhs (call, tem);
			  enum tree_code code
			    = object_size_type == 1 ? MIN_EXPR : MAX_EXPR;
			  tree cst = fold_convert (type, bytes);
			  gimple *g
			    = gimple_build_assign (lhs, code, tem, cst);
			  gsi_insert_after (&i, g, GSI_NEW_STMT);
			  update_stmt (call);
			}
		    }
		}
	      continue;
	    }

	  result = gimple_fold_stmt_to_constant (call, do_valueize);
	  if (!result)
	    {
	      tree ost = gimple_call_arg (call, 1);

	      if (tree_fits_uhwi_p (ost))
		{
		  unsigned HOST_WIDE_INT object_size_type = tree_to_uhwi (ost);

		  if (object_size_type < 2)
		    result = fold_convert (size_type_node,
					   integer_minus_one_node);
		  else if (object_size_type < 4)
		    result = build_zero_cst (size_type_node);
		}

	      if (!result)
		continue;
	    }

	  gcc_assert (TREE_CODE (result) == INTEGER_CST);

	  if (dump_file && (dump_flags & TDF_DETAILS))
	    {
	      fprintf (dump_file, "Simplified\n  ");
	      print_gimple_stmt (dump_file, call, 0, dump_flags);
	      fprintf (dump_file, " to ");
	      print_generic_expr (dump_file, result);
	      fprintf (dump_file, "\n");
	    }

	  /* Propagate into all uses and fold those stmts.  */
	  if (!SSA_NAME_OCCURS_IN_ABNORMAL_PHI (lhs))
	    replace_uses_by (lhs, result);
	  else
	    replace_call_with_value (&i, result);
	}
    }

  fini_object_sizes ();
  return 0;
}

/* Simple pass to optimize all __builtin_object_size () builtins.  */

namespace {

const pass_data pass_data_object_sizes =
{
  GIMPLE_PASS, /* type */
  "objsz", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  ( PROP_cfg | PROP_ssa ), /* properties_required */
  PROP_objsz, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_object_sizes : public gimple_opt_pass
{
public:
  pass_object_sizes (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_object_sizes, ctxt)
  {}

  /* opt_pass methods: */
  opt_pass * clone () { return new pass_object_sizes (m_ctxt); }
  virtual unsigned int execute (function *fun)
  {
    return object_sizes_execute (fun, false);
  }
}; // class pass_object_sizes

} // anon namespace

gimple_opt_pass *
make_pass_object_sizes (gcc::context *ctxt)
{
  return new pass_object_sizes (ctxt);
}

/* Early version of pass to optimize all __builtin_object_size () builtins.  */

namespace {

const pass_data pass_data_early_object_sizes =
{
  GIMPLE_PASS, /* type */
  "early_objsz", /* name */
  OPTGROUP_NONE, /* optinfo_flags */
  TV_NONE, /* tv_id */
  ( PROP_cfg | PROP_ssa ), /* properties_required */
  0, /* properties_provided */
  0, /* properties_destroyed */
  0, /* todo_flags_start */
  0, /* todo_flags_finish */
};

class pass_early_object_sizes : public gimple_opt_pass
{
public:
  pass_early_object_sizes (gcc::context *ctxt)
    : gimple_opt_pass (pass_data_early_object_sizes, ctxt)
  {}

  /* opt_pass methods: */
  virtual unsigned int execute (function *fun)
  {
    return object_sizes_execute (fun, true);
  }
}; // class pass_object_sizes

} // anon namespace

gimple_opt_pass *
make_pass_early_object_sizes (gcc::context *ctxt)
{
  return new pass_early_object_sizes (ctxt);
}
