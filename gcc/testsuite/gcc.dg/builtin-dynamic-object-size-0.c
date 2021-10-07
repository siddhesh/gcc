/* { dg-do run } */
/* { dg-options "-O2" } */

typedef __SIZE_TYPE__ size_t;
#define abort __builtin_abort

void *
__attribute__ ((alloc_size (1)))
__attribute__ ((__nothrow__ , __leaf__))
__attribute__ ((noinline))
alloc_func (size_t sz)
{
  return __builtin_malloc (sz);
}

void *
__attribute__ ((alloc_size (1, 2)))
__attribute__ ((__nothrow__ , __leaf__))
__attribute__ ((noinline))
calloc_func (size_t cnt, size_t sz)
{
  return __builtin_calloc (cnt, sz);
}

void *
__attribute__ ((noinline))
unknown_allocator (size_t cnt, size_t sz)
{
  return __builtin_calloc (cnt, sz);
}

size_t
__attribute__ ((noinline))
test_unknown (size_t cnt, size_t sz)
{
  void *ret = unknown_allocator (cnt, sz);
  return __builtin_dynamic_object_size (ret, 0);
}

/* Malloc-like allocator.  */

size_t
__attribute__ ((noinline))
test_malloc (size_t sz)
{
  void *ret = alloc_func (sz);
  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc (size_t sz)
{
  void *ret = __builtin_malloc (sz);
  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc_cond (int cond)
{
  void *ret = __builtin_malloc (cond ? 32 : 64);
  return __builtin_dynamic_object_size (ret, 0);
}

/* Calloc-like allocator.  */

size_t
__attribute__ ((noinline))
test_calloc (size_t cnt, size_t sz)
{
  void *ret = calloc_func (cnt, sz);
  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_calloc (size_t cnt, size_t sz)
{
  void *ret = __builtin_calloc (cnt, sz);
  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_calloc_cond (int cond1, int cond2)
{
  void *ret = __builtin_calloc (cond1 ? 32 : 64, cond2 ? 1024 : 16);
  return __builtin_dynamic_object_size (ret, 0);
}

/* Passthrough functions.  */

size_t
__attribute__ ((noinline))
test_passthrough (size_t sz, char *in)
{
  char *bin = __builtin_malloc (sz);
  char *dest = __builtin_memcpy (bin, in, sz);

  return __builtin_dynamic_object_size (dest, 0);
}

/* Variable length arrays.  */
size_t
__attribute__ ((noinline))
test_dynarray (size_t sz)
{
  char bin[sz];

  return __builtin_dynamic_object_size (bin, 0);
}

size_t
__attribute__ ((noinline))
test_dynarray_cond (int cond)
{
  char bin[cond ? 8 : 16];

  return __builtin_dynamic_object_size (bin, 0);
}

int
main (int argc, char **argv)
{
  unsigned nfails = 0;

#define FAIL() ({ \
  __builtin_printf ("Failure at line: %d\n", __LINE__);			      \
  nfails++;								      \
})

  size_t outsz = test_unknown (32, 42);
  if (outsz != -1 && outsz != 32)
    FAIL ();
  if (test_malloc (2048) != 2048)
    FAIL ();
  if (test_builtin_malloc (2048) != 2048)
    FAIL ();
  if (test_builtin_malloc_cond (1) != 32)
    FAIL ();
  if (test_builtin_malloc_cond (0) != 64)
    FAIL ();
  if (test_calloc (2048, 4) != 2048 * 4)
    FAIL ();
  if (test_builtin_calloc (2048, 8) != 2048 * 8)
    FAIL ();
  if (test_builtin_calloc_cond (0, 0) != 64 * 16)
    FAIL ();
  if (test_builtin_calloc_cond (1, 1) != 32 * 1024)
    FAIL ();
  if (test_passthrough (__builtin_strlen (argv[0]) + 1, argv[0])
      != __builtin_strlen (argv[0]) + 1)
    FAIL ();
  if (test_dynarray (__builtin_strlen (argv[0])) != __builtin_strlen (argv[0]))
    FAIL ();
  if (test_dynarray_cond (0) != 16)
    FAIL ();
  if (test_dynarray_cond (1) != 8)
    FAIL ();

  if (nfails > 0)
    __builtin_abort ();

  return 0;
}
