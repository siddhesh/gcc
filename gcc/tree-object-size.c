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
#include "tree-dfa.h"
#include "stringpool.h"
#include "attribs.h"
#include "builtins.h"
#include "gimplify-me.h"

struct object_size_info
{
  int object_size_type;
  bitmap visited, reexamine, phiresults;
  vec<unsigned> tempsize_objs;
};

enum
{
  OST_SUBOBJECT = 1,
  OST_MINIMUM = 2,
  OST_DYNAMIC = 4,
  OST_END = 8,
};

#define OST_TREE_CODE(_ost) ((_ost) & OST_MINIMUM ? MIN_EXPR : MAX_EXPR)

static tree compute_object_offset (const_tree, const_tree);
static bool addr_object_size (struct object_size_info *,
			      const_tree, int, tree *);
static tree alloc_object_size (const gcall *, int);
static tree pass_through_call (const gcall *);
static void collect_object_sizes_for (struct object_size_info *, tree);
static tree expr_object_size (struct object_size_info *, tree);
static tree ssa_object_size (struct object_size_info *, tree, tree);
static tree plus_stmt_object_size (struct object_size_info *, gimple *);
static tree cond_expr_object_size (struct object_size_info *, gimple *);
static void init_offset_limit (void);

/* object_sizes[0] is upper bound for number of bytes till the end of
   the object.
   object_sizes[1] is upper bound for number of bytes till the end of
   the subobject (innermost array or field with address taken).
   object_sizes[2] is lower bound for number of bytes till the end of
   the object and object_sizes[3] lower bound for subobject.

   Each array contains sizes subscripted by an SSA name version, which could be
   of two types and correspondingly, their values have special properties:

   When the SSA name is an object:
   - The value is either a constant or a gimple variable that is the size of
     the object.
   - If the value is an SSA variable, it could be a placeholder SSA name, which
   again is a subscript in object_sizes.

   When the SSA name is a placeholder:
   - The name version is also set in the osi.reexamine bitmap
   - The value at its index in osi.tempsize_objs is the SSA name version of the
     object whose size it is.
   - Its value in object_sizes is an expression that evaluates to the size.  */
static vec<tree> object_sizes[OST_END];

/* Bitmaps what object sizes have been computed already.  */
static bitmap computed[OST_END];

/* Maximum value of offset we consider to be addition.  */
static unsigned HOST_WIDE_INT offset_limit;

/* Initial value of object sizes; zero for maximum and SIZE_MAX for minimum
   object size.  */

static inline unsigned HOST_WIDE_INT
initval (int object_size_type)
{
  return (unsigned HOST_WIDE_INT) -popcount_hwi (object_size_type
						 & OST_MINIMUM);
}

/* Unknown object size value; it's the opposite of initval.  */

static inline unsigned HOST_WIDE_INT
unknown (int object_size_type)
{
  return ~initval (object_size_type);
}

/* Return true if VAL is represents an unknown size for OBJECT_SIZE_TYPE.  */

static inline bool
size_unknown_p (tree val, int object_size_type)
{
  return (tree_fits_uhwi_p (val)
	  && tree_to_uhwi (val) == unknown (object_size_type));
}

/* Return a tree with initial value for OBJECT_SIZE_TYPE.  */

static inline tree
size_initval (int object_size_type)
{
  return size_int (initval (object_size_type));
}

/* Return a tree with unknown value for OBJECT_SIZE_TYPE.  */

static inline tree
size_unknown (int object_size_type)
{
  return size_int (unknown (object_size_type));
}

/* Grow object_sizes[OBJECT_SIZE_TYPE] to num_ssa_names.  */

static inline void
object_sizes_grow (int object_size_type)
{
  if (num_ssa_names > object_sizes[object_size_type].length ())
    object_sizes[object_size_type].safe_grow (num_ssa_names, true);
}

/* Release object_sizes[OBJECT_SIZE_TYPE].  */

static inline void
object_sizes_release (int object_size_type)
{
  object_sizes[object_size_type].release ();
}

/* Return true if object_sizes[OBJECT_SIZE_TYPE][VARNO] is unknown.  */

static inline bool
object_sizes_unknown_p (int object_size_type, unsigned varno)
{
  return size_unknown_p (object_sizes[object_size_type][varno],
			 object_size_type);
}

/* Return size for VARNO corresponding to OSI.  */

static inline tree
object_sizes_get (struct object_size_info *osi, unsigned varno)
{
  return object_sizes[osi->object_size_type][varno];
}

/* Set size for VARNO corresponding to OSI to VAL.  */

static inline void
object_sizes_initialize (struct object_size_info *osi, unsigned varno,
			 tree val = NULL_TREE)
{
  int object_size_type = osi->object_size_type;

  if (!val)
    val = size_initval (object_size_type);
  object_sizes[object_size_type][varno] = val;
}

/* Set size for VARNO corresponding to OSI to VAL if it is the new minimum or
   maximum.  */

static inline void
object_sizes_set (struct object_size_info *osi, unsigned varno, tree val)
{
  int object_size_type = osi->object_size_type;
  tree curval = object_sizes[object_size_type][varno];

  /* Object size is set at most twice, once to put in an SSA name to resolve
     dependency loops and the second time to set the final size.  */
  gcc_checking_assert (TREE_CODE (curval) == SSA_NAME
		       || (tree_fits_uhwi_p (curval)
			   && !compare_tree_int (curval,
						 initval (object_size_type))));

  /* For self-referencing objects, update the element that the size SSA name
     refers to, not the object SSA name, except if the size is unknown, in
     which case we update both.  */
  if (TREE_CODE (curval) == SSA_NAME
      && bitmap_bit_p (osi->reexamine, SSA_NAME_VERSION (curval))
      && (TREE_CODE (val) != SSA_NAME
	  || SSA_NAME_VERSION (curval) != SSA_NAME_VERSION (val)))
    {
      object_sizes[object_size_type][SSA_NAME_VERSION (curval)] = val;
      if (size_unknown_p (val, object_size_type))
	object_sizes[object_size_type][varno] = val;
    }
  else
    object_sizes[object_size_type][varno] = val;
}

/* Initialize OFFSET_LIMIT variable.  */
static void
init_offset_limit (void)
{
  if (tree_fits_uhwi_p (TYPE_MAX_VALUE (sizetype)))
    offset_limit = tree_to_uhwi (TYPE_MAX_VALUE (sizetype));
  else
    offset_limit = -1;
  offset_limit /= 2;
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

      if (!osi || (object_size_type & OST_SUBOBJECT) != 0
	  || TREE_CODE (TREE_OPERAND (pt_var, 0)) != SSA_NAME)
	{
	  compute_builtin_object_size (TREE_OPERAND (pt_var, 0),
				       object_size_type & OST_MINIMUM, &sz,
				       object_size_type & OST_DYNAMIC);
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
	  && compare_tree_int (sz, offset_limit) < 0)
	pt_var_size = sz;
    }
  else if (DECL_P (pt_var))
    {
      pt_var_size = decl_init_size (pt_var, object_size_type & OST_MINIMUM);
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
      if (compare_tree_int (pt_var_size, offset_limit) >= 0)
	return false;
    }

  if (pt_var != TREE_OPERAND (ptr, 0))
    {
      tree var;

      if (object_size_type & OST_SUBOBJECT)
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
      gcc_checking_assert (compare_tree_int (TREE_OPERAND (expr, 1),
					     offset_limit) > 0);
      /* Fall through.  */
    case MINUS_EXPR:
      gcc_checking_assert (TREE_CODE (TREE_OPERAND (expr, 1)) == INTEGER_CST);
      if (reducing_size (orig, TREE_OPERAND (expr, 0), true))
	return true;
      /* Fall through.  */
    case INTEGER_CST:
    default:
      return false;
    }
}

/* Return a constant size estimate for the input SZEXPR and update it with a
   simplified expression.  */

static tree
estimate_size (object_size_info *osi, tree size, bitmap *visitlog = NULL)
{
  enum tree_code code = TREE_CODE (size);
  int object_size_type = osi->object_size_type;

  switch (code)
    {
    case SSA_NAME:
	{
	  unsigned num = SSA_NAME_VERSION (size);
	  if (!bitmap_bit_p (osi->reexamine, num)
	      || (visitlog && !bitmap_set_bit (*visitlog, num)))
	    return size;
	  gimple *stmt = SSA_NAME_DEF_STMT (size);
	  if (stmt)
	    {
	      /* Only the PHI results are added to gimple.  */
	      gcc_checking_assert (gimple_code (stmt) == GIMPLE_PHI);
	      gcc_checking_assert (osi->object_size_type & OST_DYNAMIC);
	      unsigned i, num_args = gimple_phi_num_args (stmt);

	      gcc_checking_assert (num_args > 0);
	      for (i = 0; i < num_args; i++)
		{
		  tree rhs = gimple_phi_arg_def (stmt, i);

		  if (TREE_CODE (rhs) == SSA_NAME
		      && bitmap_bit_p (osi->reexamine, SSA_NAME_VERSION (rhs)))
		    rhs = estimate_size (osi, rhs, visitlog);

		  if (size_unknown_p (rhs, object_size_type))
		    return size_unknown (object_size_type);
		}
	      return size;
	    }
	  return object_sizes_get (osi, osi->tempsize_objs[num]);
	}
    case MIN_EXPR:
    case MAX_EXPR:
	{
	  tree op0 = estimate_size (osi, TREE_OPERAND (size, 0), visitlog);
	  tree op1 = estimate_size (osi, TREE_OPERAND (size, 1), visitlog);
	  if (size_unknown_p (op0, object_size_type)
	      || size_unknown_p (op1, object_size_type))
	    return size_unknown (object_size_type);
	  return size_binop (code, op0, op1);
	}
    case MINUS_EXPR:
    case PLUS_EXPR:
	{
	  tree ret = estimate_size (osi, TREE_OPERAND (size, 0), visitlog);

	  if (size_unknown_p (ret, object_size_type))
	    return size_unknown (object_size_type);

	  tree off = TREE_OPERAND (size, 1);
	  gcc_checking_assert (TREE_CODE (off) == INTEGER_CST);

	  if (code == PLUS_EXPR)
	    off = fold_build1 (NEGATE_EXPR, sizetype, off);

	  if (tree_fits_uhwi_p (ret) && tree_int_cst_le (ret, off))
	    return size_int (0);
	  return size_binop (MINUS_EXPR, ret, off);
	}
    case INTEGER_CST:
    default:
      return size;
    }
}

/* Replace dependency loop SSA names with their actual values.  */

static void
resolve_dependency_loops (struct object_size_info *osi)
{
  bitmap_iterator bi;
  unsigned int i;
  int object_size_type = osi->object_size_type;

  /* Step 1: Update the self-referencing sizes until they don't
     change anymore.  */
  bool changed;
  bitmap tempsize_free = BITMAP_ALLOC (NULL);
  do
    {
      changed = false;
      bitmap_and_compl_into (osi->reexamine, tempsize_free);
      EXECUTE_IF_SET_IN_BITMAP (osi->reexamine, 0, i, bi)
	{
	  unsigned varno = osi->tempsize_objs[i];

	  tree cur = object_sizes_get (osi, varno);

	  if (size_unknown_p (cur, object_size_type))
	    {
	      bitmap_set_bit (tempsize_free, i);
	      continue;
	    }

	  tree szexpr = object_sizes_get (osi, i);

	  /* First run, initialize.  */
	  if (TREE_CODE (cur) == SSA_NAME)
	    {
	      if (reducing_size (cur, szexpr, false))
		{
		  cur = size_int (0);
		  object_sizes_initialize (osi, varno, cur);
		  if (object_size_type & OST_MINIMUM)
		    bitmap_set_bit (tempsize_free, i);
		}
	      else
		{
		  cur = size_initval (object_size_type);
		  object_sizes_initialize (osi, varno, cur);
		}
	      changed = true;
	    }

	  tree sz = estimate_size (osi, szexpr);

	  /* It depends on some self-referencing size that has not been
	     initialized yet.  */
	  if (TREE_CODE (sz) != INTEGER_CST)
	    continue;

	  if (size_unknown_p (sz, object_size_type))
	    bitmap_set_bit (tempsize_free, i);
	  /* If we have a new estimate, then update it.  */
	  if (tree_int_cst_compare (cur, sz) != 0)
	    {
	      object_sizes_initialize (osi, varno, sz);
	      changed = true;
	    }
	}
    }
  while (changed);

  /* Now we only need to dump and free all SSAs.  */
  bitmap_ior_into_and_free (osi->reexamine, &tempsize_free);
  if (dump_file && (dump_flags & TDF_DETAILS))
    {
      fprintf (dump_file, "After dependency resolution:\n");
      EXECUTE_IF_SET_IN_BITMAP (osi->reexamine, 0, i, bi)
	{
	  fprintf (dump_file, "  ");
	  print_generic_expr (dump_file, ssa_name (i), dump_flags);
	  fprintf (dump_file, ": ");
	  print_generic_expr (dump_file,
			      object_sizes_get (osi, osi->tempsize_objs[i]),
			      dump_flags);
	  fprintf (dump_file, "\n");
	}
    }

  /* Step 2: Update all remaining non-constant sizes.  */
  EXECUTE_IF_SET_IN_BITMAP (computed[object_size_type], 0, i, bi)
    {
      tree szexpr = object_sizes_get (osi, i);
      if (TREE_CODE (szexpr) == INTEGER_CST)
	continue;
      tree sz = estimate_size (osi, szexpr);
      gcc_checking_assert (TREE_CODE (sz) == INTEGER_CST);
      object_sizes_initialize (osi, i, sz);
    }

  /* Release all the SSA names we created.  */
  EXECUTE_IF_SET_IN_BITMAP (osi->reexamine, 0, i, bi)
    release_ssa_name (ssa_name (i));
}

static void
get_insertion_point (struct object_size_info *osi, unsigned ssano,
		     gimple_stmt_iterator *gsi)
{
  unsigned varno = osi->tempsize_objs[ssano];
  gimple *stmt = SSA_NAME_DEF_STMT (ssa_name (varno));

  switch (gimple_code (stmt))
    {
    case GIMPLE_NOP:
      *gsi = gsi_start_bb (single_succ (ENTRY_BLOCK_PTR_FOR_FN (cfun)));
      break;
    case GIMPLE_PHI:
	{
	  gimple *size_stmt = SSA_NAME_DEF_STMT (object_sizes_get (osi,
								   varno));

	  for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
	    {
	      tree rhs = gimple_phi_arg_def (size_stmt, i);
	      if (TREE_CODE (rhs) == SSA_NAME
		  && SSA_NAME_VERSION (rhs) == ssano)
		{
		  edge e = gimple_phi_arg_edge (as_a <gphi *> (stmt), i);
		  *gsi = gsi_last_bb (e->src);
		  break;
		}
	    }
	  break;
	}
    default:
      *gsi = gsi_for_stmt (stmt);
    }
}

static void
gimplify_size_expressions (object_size_info *osi)
{
  int object_size_type = osi->object_size_type;
  bitmap_iterator bi;
  unsigned int i;
  bool changed;

  /* Step 1: Propagate unknowns into expressions.  */
  bitmap tempsize_free = BITMAP_ALLOC (NULL);
  do
    {
      changed = false;
      EXECUTE_IF_SET_IN_BITMAP (osi->reexamine, 0, i, bi)
	{
	  unsigned varno = osi->tempsize_objs[i];

	  tree cur = object_sizes_get (osi, varno);

	  if (size_unknown_p (cur, object_size_type))
	    {
	      bitmap_set_bit (tempsize_free, i);
	      continue;
	    }

	  tree szexpr = object_sizes_get (osi, i);
	  bitmap visitlog = BITMAP_ALLOC (NULL);
	  tree sz = estimate_size (osi, szexpr, &visitlog);

	  if (size_unknown_p (sz, object_size_type))
	    {
	      gimple *stmt = SSA_NAME_DEF_STMT (cur);
	      if (stmt)
		{
		  gimple_stmt_iterator gsi = gsi_for_stmt (stmt);
		  remove_phi_node (&gsi, true);
		}
	      bitmap_set_bit (tempsize_free, i);
	      object_sizes_initialize (osi, varno, sz);
	      changed = true;
	    }
	}
      bitmap_and_compl_into (osi->reexamine, tempsize_free);
    }
  while (changed);

  /* Expand all size expressions to put their definitions close to the objects
     for whom size is being computed.  */
  bitmap_and_compl_into (osi->reexamine, osi->phiresults);
  EXECUTE_IF_SET_IN_BITMAP (osi->reexamine, 0, i, bi)
    {
      gimple_stmt_iterator gsi;
      gimple_seq seq = NULL;
      tree size_expr = object_sizes_get (osi, i);

      size_expr = size_binop (MODIFY_EXPR, ssa_name (i), size_expr);
      force_gimple_operand (size_expr, &seq, true, NULL);

      get_insertion_point (osi, i, &gsi);
      gsi_insert_seq_before (&gsi, seq, GSI_CONTINUE_LINKING);
    }

  EXECUTE_IF_SET_IN_BITMAP (tempsize_free, 0, i, bi)
    release_ssa_name (ssa_name (i));

  BITMAP_FREE (tempsize_free);
}

/* Compute __builtin_object_size value for PTR and set *PSIZE to
   the resulting value.  If the declared object is known and PDECL
   is nonnull, sets *PDECL to the object's DECL.  OBJECT_SIZE_TYPE
   is the second argument   to __builtin_object_size.
   Returns true on success and false when the object size could not
   be determined.  */

bool
compute_builtin_object_size (tree ptr, int object_size_type,
			     tree *psize, bool dynamic)
{
  gcc_assert (object_size_type >= 0 && object_size_type < OST_END);
  object_size_type |= dynamic ? OST_DYNAMIC : 0;

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
      if (optimize || object_size_type & OST_SUBOBJECT)
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
		  && compute_builtin_object_size (ptr,
						  (object_size_type
						   & ~OST_DYNAMIC),
						  psize, dynamic))
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
	  fprintf (dump_file, "Computing %s %s%sobject size for ",
		   (object_size_type & OST_MINIMUM) ? "minimum" : "maximum",
		   dynamic ? "dynamic " : "",
		   (object_size_type & OST_SUBOBJECT) ? "sub" : "");
	  print_generic_expr (dump_file, ptr, dump_flags);
	  fprintf (dump_file, ":\n");
	}

      osi.visited = BITMAP_ALLOC (NULL);
      osi.reexamine = BITMAP_ALLOC (NULL);
      osi.phiresults = BITMAP_ALLOC (NULL);
      osi.tempsize_objs.create (0);
      collect_object_sizes_for (&osi, ptr);

      if (!bitmap_empty_p (osi.reexamine))
	{
	  if (dynamic)
	    gimplify_size_expressions (&osi);
	  else
	    resolve_dependency_loops (&osi);
	}

      /* Debugging dumps.  */
      if (dump_file)
	{
	  EXECUTE_IF_SET_IN_BITMAP (osi.visited, 0, i, bi)
	    if (!object_sizes_unknown_p (object_size_type, i))
	      {
		print_generic_expr (dump_file, ssa_name (i),
				    dump_flags);
		fprintf (dump_file,
			 ": %s %s%sobject size ",
			 ((object_size_type & OST_MINIMUM) ? "minimum"
			  : "maximum"),
			 dynamic ? "dynamic " : "",
			 (object_size_type & OST_SUBOBJECT) ? "sub" : "");
		print_generic_expr (dump_file, object_sizes_get (&osi, i),
				    dump_flags);
		fprintf (dump_file, "\n");
	      }
	}

      osi.tempsize_objs.release ();
      BITMAP_FREE (osi.phiresults);
      BITMAP_FREE (osi.reexamine);
      BITMAP_FREE (osi.visited);
    }

  *psize = object_sizes_get (&osi, SSA_NAME_VERSION (ptr));
  return !size_unknown_p (*psize, object_size_type);
}

/* Make a temporary placeholder variable for size.  */

static tree
make_tempsize (struct object_size_info *osi, unsigned varno)
{
  tree ssa = make_ssa_name (sizetype);
  unsigned ssano = SSA_NAME_VERSION (ssa);

  if (dump_file)
    {
      print_generic_expr (dump_file, ssa_name (varno), dump_flags);
      fprintf (dump_file, ": Making temp SSA name: ");
      print_generic_expr (dump_file, ssa, dump_flags);
      fprintf (dump_file, "\n");
    }

  object_sizes_grow (osi->object_size_type);
  if (osi->tempsize_objs.length () < num_ssa_names)
    osi->tempsize_objs.safe_grow (num_ssa_names);

  bitmap_set_bit (osi->reexamine, ssano);
  osi->tempsize_objs[ssano] = varno;

  return ssa;
}

/* Get the temp size variable if it exists for the object with VARNO as ssa
   name version and if it doesn't exist, create one.  */

static tree
make_or_get_tempsize (struct object_size_info *osi, unsigned varno)
{
  tree ssa = object_sizes_get (osi, varno);
  if (TREE_CODE (ssa) != SSA_NAME)
    ssa = make_tempsize (osi, varno);
  else if (dump_file)
    {
      fprintf (dump_file, "  temp name already assigned: ");
      print_generic_expr (dump_file, ssa, dump_flags);
      fprintf (dump_file, "\n");
    }
  return ssa;
}

/* Compute object_sizes for PTR, defined to VALUE, which is not an SSA_NAME.  */

static tree
expr_object_size (struct object_size_info *osi, tree value)
{
  int object_size_type = osi->object_size_type;
  tree bytes;

  if (TREE_CODE (value) == WITH_SIZE_EXPR)
    value = TREE_OPERAND (value, 0);

  /* Pointer variables should have been handled by ssa_object_size.  */
  gcc_assert (TREE_CODE (value) != SSA_NAME
	      || !POINTER_TYPE_P (TREE_TYPE (value)));

  if (TREE_CODE (value) == ADDR_EXPR
      && addr_object_size (osi, value, object_size_type, &bytes))
    return bytes;

  return size_unknown (object_size_type);
}


/* Compute object_sizes for PTR, defined to the result of a call.  */

static tree
call_object_size (struct object_size_info *osi, gcall *call)
{
  int object_size_type = osi->object_size_type;

  gcc_assert (is_gimple_call (call));

  return alloc_object_size (call, object_size_type);
}


/* Compute object_sizes for PTR, defined to an unknown value.  */

static tree
unknown_object_size (struct object_size_info *osi)
{
  int object_size_type = osi->object_size_type;
  return size_unknown (object_size_type);
}


/* Return object size of ORIG + OFFSET.  */

static tree
ssa_object_size (struct object_size_info *osi, tree orig, tree offset)
{
  int object_size_type = osi->object_size_type;
  tree orig_bytes;

  if (compare_tree_int (offset, offset_limit) >= 0)
    return size_unknown (object_size_type);

  collect_object_sizes_for (osi, orig);

  orig_bytes = object_sizes_get (osi, SSA_NAME_VERSION (orig));
  if (!size_unknown_p (orig_bytes, object_size_type)
      && !integer_zerop (offset))
    orig_bytes = size_for_offset (orig_bytes, offset);

  return orig_bytes;
}


/* Compute object_sizes for VAR, defined to the result of an assignment
   with operator POINTER_PLUS_EXPR.  */

static tree
plus_stmt_object_size (struct object_size_info *osi, gimple *stmt)
{
  int object_size_type = osi->object_size_type;
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

  /* Handle PTR + OFFSET here.  */
  if (TREE_CODE (op1) == INTEGER_CST
      && (TREE_CODE (op0) == SSA_NAME
	  || TREE_CODE (op0) == ADDR_EXPR))
    {
      if (TREE_CODE (op0) == SSA_NAME)
	bytes = ssa_object_size (osi, op0, op1);
      else
	{
          /* op0 will be ADDR_EXPR here.  */
	  addr_object_size (osi, op0, object_size_type, &bytes);
	  if (size_unknown_p (bytes, object_size_type))
	    ;
	  else if (compare_tree_int (op1, offset_limit) > 0)
	    bytes = size_unknown (object_size_type);
	  else if (!integer_zerop (op1))
	    bytes = size_for_offset (bytes, op1);
	}
    }
  else
    bytes = size_unknown (object_size_type);

  return bytes;
}


/* Compute object_sizes for VAR, defined at STMT, which is
   a COND_EXPR.  */

static tree
cond_expr_object_size (struct object_size_info *osi, gimple *stmt)
{
  tree then_, else_;
  int object_size_type = osi->object_size_type;
  tree thenbytes, elsebytes;

  gcc_assert (gimple_assign_rhs_code (stmt) == COND_EXPR);

  then_ = gimple_assign_rhs2 (stmt);
  else_ = gimple_assign_rhs3 (stmt);

  if (TREE_CODE (then_) == SSA_NAME)
    thenbytes = ssa_object_size (osi, then_, size_int (0));
  else
    thenbytes = expr_object_size (osi, then_);

  if (TREE_CODE (else_) == SSA_NAME)
    elsebytes = ssa_object_size (osi, else_, size_int (0));
  else
    elsebytes = expr_object_size (osi, else_);

  if (size_unknown_p (thenbytes, object_size_type)
      || size_unknown_p (elsebytes, object_size_type))
    return size_unknown (object_size_type);

  if (object_size_type & OST_DYNAMIC)
    return fold_build3 (COND_EXPR, sizetype, gimple_assign_rhs1 (stmt),
			thenbytes, elsebytes);

  return size_binop (OST_TREE_CODE (object_size_type), thenbytes, elsebytes);
}

static tree
phi_object_size (struct object_size_info *osi, gimple *stmt)
{
  int object_size_type = osi->object_size_type;
  unsigned i;

  tree res = size_initval (object_size_type);

  for (i = 0; i < gimple_phi_num_args (stmt); i++)
    {
      tree rhs = gimple_phi_arg (stmt, i)->def;
      tree phires;

      if (TREE_CODE (rhs) == SSA_NAME)
	phires = ssa_object_size (osi, rhs, size_int (0));
      else
	phires = expr_object_size (osi, rhs);

      res = size_binop (OST_TREE_CODE (object_size_type), res, phires);

      if (size_unknown_p (phires, object_size_type))
	break;
    }
  return res;
}

static tree
phi_dynamic_object_size (struct object_size_info *osi, tree var)
{
  int object_size_type = osi->object_size_type;
  unsigned int varno = SSA_NAME_VERSION (var);
  gimple *stmt = SSA_NAME_DEF_STMT (var);
  unsigned i, num_args = gimple_phi_num_args (stmt);
  tree res;

  vec<tree> sizes;
  sizes.create (0);
  sizes.safe_grow (num_args);

  /* Bail out if the size of any of the PHI arguments cannot be
     determined.  */
  for (i = 0; i < num_args; i++)
    {
      tree rhs = gimple_phi_arg_def (stmt, i);
      tree sz;

      if (TREE_CODE (rhs) != SSA_NAME)
	sz = expr_object_size (osi, rhs);
      else
	sz = ssa_object_size (osi, rhs, size_int (0));

      if (size_unknown_p (sz, object_size_type))
	break;

      sizes[i] = sz;
    }

  if (i == num_args)
    {
      res = make_or_get_tempsize (osi, varno);
      bitmap_set_bit (osi->phiresults, SSA_NAME_VERSION (res));
      object_sizes_initialize (osi, SSA_NAME_VERSION (res), res);

      gphi *phi = create_phi_node (res, gimple_bb (stmt));
      gphi *obj_phi =  as_a <gphi *> (stmt);

      for (unsigned i = 0; i < gimple_phi_num_args (stmt); i++)
	{
	  if (!is_gimple_variable (sizes[i]))
	    {
	      tree ssa = make_tempsize (osi, varno);
	      object_sizes_initialize (osi, SSA_NAME_VERSION (ssa), sizes[i]);
	      sizes[i] = ssa;
	    }

	  add_phi_arg (phi, sizes[i],
		       gimple_phi_arg_edge (obj_phi, i),
		       gimple_phi_arg_location (obj_phi, i));
	}

      if (dump_file)
	{
	  print_generic_expr (dump_file, var, dump_flags);
	  fprintf (dump_file, ": PHI Node with result: ");
	  print_gimple_stmt (dump_file, phi, dump_flags);
	}
    }
  else
    res = size_unknown (object_size_type);

  sizes.release ();

  return res;
}

/* Find size of an object passed as a parameter to the function.  */

static tree
parm_object_size (struct object_size_info *osi, tree var)
{
  int object_size_type = osi->object_size_type;
  tree parm = SSA_NAME_VAR (var);

  if (dump_file)
    {
      fprintf (dump_file, "Object is a parameter: ");
      print_generic_expr (dump_file, parm, dump_flags);
      fprintf (dump_file, " which is %s a pointer type\n",
	       POINTER_TYPE_P (TREE_TYPE (parm)) ? "" : "not");
    }

  if (!(object_size_type & OST_DYNAMIC) || !POINTER_TYPE_P (TREE_TYPE (parm)))
    return expr_object_size (osi, parm);

  /* Look for access attribute.  */
  rdwr_map rdwr_idx;

  tree fndecl = cfun->decl;
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
	  tree sz = get_or_create_ssa_default_def (cfun, arg);
	  if (sz != NULL_TREE)
	    {
	      sz = fold_convert (sizetype, sz);
	      if (typesize)
		sz = size_binop (MULT_EXPR, sz, typesize);
	      return sz;
	    }
	}
    }
  return size_unknown (object_size_type);
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
  tree res;

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
      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Found a dependency loop at ");
	  print_generic_expr (dump_file, var, dump_flags);
	  fprintf (dump_file, "\n");
	}
      res = make_or_get_tempsize (osi, varno);
      goto out;
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
	  res = plus_stmt_object_size (osi, stmt);
	else if (gimple_assign_rhs_code (stmt) == COND_EXPR)
	  res = cond_expr_object_size (osi, stmt);
	else if (gimple_assign_single_p (stmt)
		 || gimple_assign_unary_nop_p (stmt))
	  {
	    if (TREE_CODE (rhs) == SSA_NAME
		&& POINTER_TYPE_P (TREE_TYPE (rhs)))
	      res = ssa_object_size (osi, rhs, size_int (0));
	    else
	       res = expr_object_size (osi, rhs);
	  }
	else
	  res = unknown_object_size (osi);
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
	      res = ssa_object_size (osi, arg, size_int (0));
	    else
	      res = expr_object_size (osi, arg);
	  }
	else
	  res = call_object_size (osi, call_stmt);
	break;
      }

    case GIMPLE_ASM:
      /* Pointers defined by __asm__ statements can point anywhere.  */
      res = size_unknown (object_size_type);
      break;

    case GIMPLE_NOP:
      if (SSA_NAME_VAR (var)
	  && TREE_CODE (SSA_NAME_VAR (var)) == PARM_DECL)
	res = parm_object_size (osi, var);
      else
	/* Uninitialized SSA names point nowhere.  */
	res = size_unknown (object_size_type);
      break;

    case GIMPLE_PHI:
      {
	if (object_size_type & OST_DYNAMIC)
	  res = phi_dynamic_object_size (osi, var);
	else
	  res = phi_object_size (osi, stmt);
	break;
      }

    default:
      gcc_unreachable ();
    }

  if ((object_size_type & OST_DYNAMIC)
      && TREE_CODE (res) != INTEGER_CST && !is_gimple_variable (res))
    {
      tree ssa = make_or_get_tempsize (osi, varno);
      object_sizes_initialize (osi, SSA_NAME_VERSION (ssa), res);
      res = ssa;
    }
  bitmap_set_bit (computed[object_size_type], varno);
out:
  object_sizes_set (osi, varno, res);
}


/* Initialize data structures for the object size computation.  */

void
init_object_sizes (void)
{
  int object_size_type;

  if (computed[0])
    return;

  for (object_size_type = 0; object_size_type < OST_END; object_size_type++)
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

  for (object_size_type = 0; object_size_type < OST_END; object_size_type++)
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

/* Process a __builtin_object_size or __builtin_dynamic_object_size call in
   CALL early before any object information is lost due to optimization.
   Insert a MIN or MAX expression of the result and __builtin_object_size at I
   so that it may be processed in the second pass.  */

static void
early_object_sizes_execute_one (gimple_stmt_iterator *i, gimple *call)
{
  tree ost = gimple_call_arg (call, 1);
  tree lhs = gimple_call_lhs (call);
  gcc_assert (lhs != NULL_TREE);

  if (tree_fits_uhwi_p (ost))
    {
      unsigned HOST_WIDE_INT object_size_type = tree_to_uhwi (ost);
      tree ptr = gimple_call_arg (call, 0);
      if ((object_size_type == 1 || object_size_type == 3)
	  && (TREE_CODE (ptr) == ADDR_EXPR || TREE_CODE (ptr) == SSA_NAME))
	{
	  tree type = TREE_TYPE (lhs);
	  tree bytes;
	  if (compute_builtin_object_size (ptr, object_size_type, &bytes))
	    {
	      tree tem = make_ssa_name (type);
	      gimple_call_set_lhs (call, tem);
	      enum tree_code code
		= object_size_type & OST_MINIMUM ? MAX_EXPR : MIN_EXPR;
	      tree cst = fold_convert (type, bytes);
	      gimple *g = gimple_build_assign (lhs, code, tem, cst);
	      gsi_insert_after (i, g, GSI_NEW_STMT);
	      update_stmt (call);
	    }
	}
    }
}

/* Attempt to fold one __builtin_dynamic_object_size call in CALL into an
   expression and insert it at I.  Return true if it succeeds.  */

static bool
dynamic_object_sizes_execute_one (gimple_stmt_iterator *i, gimple *call)
{
  unsigned numargs = gimple_call_num_args (call);
  tree *args = XALLOCAVEC (tree, numargs);
  args[0] = gimple_call_arg (call, 0);
  args[1] = gimple_call_arg (call, 1);

  location_t loc = EXPR_LOC_OR_LOC (args[0], input_location);
  tree result_type = gimple_call_return_type (as_a <gcall *> (call));
  tree result = fold_builtin_call_array (loc, result_type,
					 gimple_call_fn (call), numargs, args);

  if (result)
    {
      /* fold_builtin_call_array may wrap the result inside a
	 NOP_EXPR.  */
      STRIP_NOPS (result);
      gimplify_and_update_call_from_tree (i, result);

      if (dump_file && (dump_flags & TDF_DETAILS))
	{
	  fprintf (dump_file, "Simplified (dynamic)\n  ");
	  print_gimple_stmt (dump_file, call, 0, dump_flags);
	  fprintf (dump_file, " to ");
	  print_generic_expr (dump_file, result);
	  fprintf (dump_file, "\n");
	}
      return true;
    }
  return false;
}

static unsigned int
object_sizes_execute (function *fun, bool early)
{
  basic_block bb;
  FOR_EACH_BB_FN (bb, fun)
    {
      gimple_stmt_iterator i;
      for (i = gsi_start_bb (bb); !gsi_end_p (i); gsi_next (&i))
	{
	  tree result;
	  bool dynamic = false;

	  gimple *call = gsi_stmt (i);
	  if (gimple_call_builtin_p (call, BUILT_IN_DYNAMIC_OBJECT_SIZE))
	    dynamic = true;
	  else if (!gimple_call_builtin_p (call, BUILT_IN_OBJECT_SIZE))
	    continue;

	  tree lhs = gimple_call_lhs (call);
	  if (!lhs)
	    continue;

	  init_object_sizes ();

	  /* If early, only attempt to fold
	     __builtin_object_size (x, 1) and __builtin_object_size (x, 3),
	     and rather than folding the builtin to the constant if any,
	     create a MIN_EXPR or MAX_EXPR of the __builtin_object_size
	     call result and the computed constant.  */
	  if (early && !dynamic)
	    {
	      early_object_sizes_execute_one (&i, call);
	      continue;
	    }

	  if (dynamic)
	    {
	      bool done = dynamic_object_sizes_execute_one (&i, call);
	      if (done || early)
		continue;
	      else
		{
		  /* If we could not find a suitable size expression, lower to
		     __builtin_object_size so that we may at least get a
		     constant lower or higher estimate.  */
		  tree bosfn = builtin_decl_implicit (BUILT_IN_OBJECT_SIZE);
		  gimple_call_set_fndecl (call, bosfn);
		  update_stmt (call);

		  if (dump_file && (dump_flags & TDF_DETAILS))
		    {
		      print_generic_expr (dump_file, gimple_call_arg (call, 0),
					  dump_flags);
		      fprintf (dump_file,
			       ": Retrying as __builtin_object_size\n");
		    }
		}
	    }

	  result = gimple_fold_stmt_to_constant (call, do_valueize);
	  if (!result)
	    {
	      tree ost = gimple_call_arg (call, 1);

	      if (tree_fits_uhwi_p (ost))
		{
		  unsigned HOST_WIDE_INT object_size_type = tree_to_uhwi (ost);

		  if (object_size_type & OST_MINIMUM)
		    result = build_zero_cst (size_type_node);
		  else if (object_size_type < OST_END)
		    result = fold_convert (size_type_node,
					   integer_minus_one_node);
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
