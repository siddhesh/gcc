/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-dynobjsz1-details" } */

extern void *alloc_func (__SIZE_TYPE__)
     __attribute__ ((alloc_size (1)))
     __attribute__ ((__nothrow__ , __leaf__));

extern void *calloc_func (__SIZE_TYPE__, __SIZE_TYPE__)
     __attribute__ ((alloc_size (1, 2)))
     __attribute__ ((__nothrow__ , __leaf__));

extern void *unknown_allocator (__SIZE_TYPE__, __SIZE_TYPE__);

void *
test_unknown (__SIZE_TYPE__ csz, __SIZE_TYPE__ cnt, __SIZE_TYPE__ *outsz)
{
  void *ret = unknown_allocator (cnt, csz);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump "ret.*: Simplified to __builtin_object_size" "dynobjsz1" } } */

/* Malloc-like allocator.  */

void *
test_malloc (__SIZE_TYPE__ sz, __SIZE_TYPE__ *outsz)
{
  void *ret = alloc_func (sz);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump "maximum dynamic object size sz_" "dynobjsz1" } } */

void *
test_builtin_malloc (__SIZE_TYPE__ bsz, __SIZE_TYPE__ *outsz)
{
  void *ret = __builtin_malloc (bsz);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump "maximum dynamic object size bsz_" "dynobjsz1" } } */

void *
test_builtin_malloc_cond (int cond, __SIZE_TYPE__ *outsz)
{
  void *ret = __builtin_malloc (cond ? 32 : 64);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _\[0-9\]" "dynobjsz1" } } */

void *
test_builtin_malloc_condphi (int cond, __SIZE_TYPE__ *outsz)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (32);
  else
    ret = __builtin_malloc (64);

  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _\[0-9\]" "dynobjsz1" } } */

void *
test_builtin_malloc_condphi2 (int cond, __SIZE_TYPE__ *outsz, __SIZE_TYPE__ in)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (in);
  else
    ret = __builtin_malloc (64);

  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _\[0-9\]" "dynobjsz1" } } */

void *
test_builtin_malloc_condphi3 (int cond, __SIZE_TYPE__ *outsz, __SIZE_TYPE__ in,
			      __SIZE_TYPE__ in2)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (in);
  else
    ret = __builtin_malloc (in2);

  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _\[0-9\]" "dynobjsz1" } } */

__SIZE_TYPE__
test_builtin_malloc_condphi4 (__SIZE_TYPE__ sz, int cond)
{
  char *a = __builtin_malloc (sz);
  char b[sz];

  return __builtin_dynamic_object_size (cond ? b : (void *) &a, 0);
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _.*" "dynobjsz1" } } */

__SIZE_TYPE__
test_builtin_malloc_condphi5 (__SIZE_TYPE__ sz, int cond, char *c)
{
  char *a = __builtin_malloc (sz);

  return __builtin_dynamic_object_size (cond ? c : (void *) &a, 0);
}
/* { dg-final { scan-tree-dump ": Simplified to __builtin_object_size" "dynobjsz1" } } */

/* Calloc-like allocator.  */

void *
test_calloc (__SIZE_TYPE__ csz, __SIZE_TYPE__ cnt, __SIZE_TYPE__ *outsz)
{
  void *ret = calloc_func (cnt, csz);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump "maximum dynamic object size \\(sizetype\\) cnt.* \* \\(sizetype\\) csz.*" "dynobjsz1" } } */

void *
test_builtin_calloc (__SIZE_TYPE__ bcsz, __SIZE_TYPE__ bcnt,
		     __SIZE_TYPE__ *outsz)
{
  void *ret = __builtin_calloc (bcnt, bcsz);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump "maximum dynamic object size \\(sizetype\\) bcnt.* \* \\(sizetype\\) bcsz.*" "dynobjsz1" } } */

void *
test_builtin_calloc_cond (int cond1, int cond2, __SIZE_TYPE__ *outsz)
{
  void *ret = __builtin_calloc (cond1 ? 32 : 64, cond2 ? 1024 : 16);
  *outsz = __builtin_dynamic_object_size (ret, 0);
  return ret;
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size \\(sizetype\\) .* \* \\(sizetype\\)" "dynobjsz1" } } */

__SIZE_TYPE__
test_builtin_calloc_condphi (__SIZE_TYPE__ ccsz, int cond)
{
  struct
    {
      int a;
      char b;
    } bin[ccsz];

  char *ch = __builtin_calloc (ccsz, 10);

  return __builtin_dynamic_object_size (cond ? ch : (void *) &bin, 0);
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size _" "dynobjsz1" } } */
/* { dg-final { scan-tree-dump ": maximum dynamic object size ccsz_" "dynobjsz1" } } */

/* Passthrough functions.  */

__SIZE_TYPE__
test_passthrough (__SIZE_TYPE__ psz, char *in)
{
  char *bin = __builtin_malloc (psz);
  char *dest = __builtin_memcpy (bin, in, psz);

  return __builtin_dynamic_object_size (dest, 0);
}
/* { dg-final { scan-tree-dump "maximum dynamic object size psz_" "dynobjsz1" } } */

__SIZE_TYPE__
test_passthrough_nonssa (__SIZE_TYPE__ sz, char *in)
{
  char bin[sz];
  char *dest = __builtin_memcpy (&bin, in, sz);

  return __builtin_dynamic_object_size (dest, 0);
}
/* { dg-final { scan-tree-dump ": maximum dynamic object size \[0-9\]" "dynobjsz1" } } */

/* Variable length arrays.  */
__SIZE_TYPE__
test_dynarray (__SIZE_TYPE__ dsz)
{
  char bin[dsz];

  return __builtin_dynamic_object_size (bin, 0);
}
/* { dg-final { scan-tree-dump "maximum dynamic object size dsz_" "dynobjsz1" } } */

__SIZE_TYPE__
test_dynarray_cond (int cond)
{
  char bin[cond ? 8 : 16];

  return __builtin_dynamic_object_size (bin, 0);
}
/* { dg-final { scan-tree-dump "maximum dynamic object size _.*" "dynobjsz1" } } */

/* Address expressions.  Object size is a saturated math expression of SZ and
   OFF, so a MIN_EXPR is expected.  */

__SIZE_TYPE__
test_dynarray_struct (__SIZE_TYPE__ sz, __SIZE_TYPE__ off)
{
  struct
    {
      long a;
      char c;
    } bin[sz];

  return __builtin_dynamic_object_size (&bin[off].c, 0);
}

/* { dg-final { scan-tree-dump ": maximum dynamic object size .*MIN_EXPR.*" "dynobjsz1" } } */

__SIZE_TYPE__
test_substring (__SIZE_TYPE__ sz, __SIZE_TYPE__ off)
{
  char str[sz];

  return __builtin_dynamic_object_size (&str[off], 0);
}

/* { dg-final { scan-tree-dump ": maximum dynamic object size sz.*MIN_EXPR.*" "dynobjsz1" } } */

__SIZE_TYPE__
test_substring_ptrplus (__SIZE_TYPE__ sz, __SIZE_TYPE__ off)
{
  int str[sz];

  return __builtin_dynamic_object_size (str + off, 0);
}

/* { dg-final { scan-tree-dump ": maximum dynamic object size .*MIN_EXPR.*" "dynobjsz1" } } */
