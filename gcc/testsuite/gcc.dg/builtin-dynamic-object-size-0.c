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

size_t
__attribute__ ((noinline))
test_builtin_malloc_condphi (int cond)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (32);
  else
    ret = __builtin_malloc (64);

  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc_condphi2 (int cond, size_t in)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (in);
  else
    ret = __builtin_malloc (64);

  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc_condphi3 (int cond, size_t in, size_t in2)
{
  void *ret;
 
  if (cond)
    ret = __builtin_malloc (in);
  else
    ret = __builtin_malloc (in2);

  return __builtin_dynamic_object_size (ret, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc_condphi4 (size_t sz, int cond)
{
  char *a = __builtin_malloc (sz);
  char b[sz / 2];

  return __builtin_dynamic_object_size (cond ? b : (void *) &a, 0);
}

size_t
__attribute__ ((noinline))
test_builtin_malloc_condphi5 (size_t sz, int cond, char *c)
{
  char *a = __builtin_malloc (sz);

  return __builtin_dynamic_object_size (cond ? c : (void *) &a, 0);
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

size_t
__attribute__ ((noinline))
test_builtin_calloc_condphi (size_t cnt, size_t sz, int cond)
{
  struct
    {
      int a;
      char b;
    } bin[cnt];

  char *ch = __builtin_calloc (cnt, sz);

  return __builtin_dynamic_object_size (cond ? ch : (void *) &bin, 0);
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

size_t
__attribute__ ((noinline))
test_passthrough_nonssa (char *in)
{
  char bin[__builtin_strlen (in) + 1];
  char *dest = __builtin_memcpy (bin, in, __builtin_strlen (in) + 1);

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

size_t
__attribute__ ((noinline))
test_deploop (size_t sz, size_t cond)
{
  char *bin = __builtin_alloca (32);

  for (size_t i = 0; i < sz; i++)
    if (i == cond)
      bin = __builtin_alloca (sz);

  return __builtin_dynamic_object_size (bin, 0);
}

/* Address expressions.  */

struct dynarray_struct
{
  long a;
  char c[16];
  int b;
};

size_t
__attribute__ ((noinline))
test_dynarray_struct (size_t sz, size_t off)
{
  struct dynarray_struct bin[sz];

  return __builtin_dynamic_object_size (&bin[off].c, 0);
}

size_t
__attribute__ ((noinline))
test_substring (size_t sz, size_t off)
{
  char str[sz];

  return __builtin_dynamic_object_size (&str[off], 0);
}

size_t
__attribute__ ((noinline))
test_substring_ptrplus (size_t sz, size_t off)
{
  int str[sz];

  return __builtin_dynamic_object_size (str + off, 0);
}

size_t
__attribute__ ((noinline))
__attribute__ ((access (__read_write__, 1, 2)))
test_parmsz (void *obj, size_t sz, size_t off)
{
  return __builtin_dynamic_object_size (obj + off, 0);
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
  if (test_builtin_malloc_condphi (1) != 32)
    FAIL ();
  if (test_builtin_malloc_condphi (0) != 64)
    FAIL ();
  if (test_builtin_malloc_condphi2 (1, 128) != 128)
    FAIL ();
  if (test_builtin_malloc_condphi2 (0, 128) != 64)
    FAIL ();
  if (test_builtin_malloc_condphi3 (1, 128, 256) != 128)
    FAIL ();
  if (test_builtin_malloc_condphi3 (0, 128, 256) != 256)
    FAIL ();
  if (test_builtin_malloc_condphi4 (128, 1) != 64)
    FAIL ();
  if (test_builtin_malloc_condphi4 (128, 0) != sizeof (void *))
    FAIL ();
  if (test_builtin_malloc_condphi5 (128, 0, argv[0]) != -1)
    FAIL ();
  if (test_calloc (2048, 4) != 2048 * 4)
    FAIL ();
  if (test_builtin_calloc (2048, 8) != 2048 * 8)
    FAIL ();
  if (test_builtin_calloc_cond (0, 0) != 64 * 16)
    FAIL ();
  if (test_builtin_calloc_cond (1, 1) != 32 * 1024)
    FAIL ();
  if (test_builtin_calloc_condphi (128, 1, 1) != 128)
    FAIL ();
  if (test_builtin_calloc_condphi (128, 1, 0) == 128)
    FAIL ();
  if (test_builtin_calloc_condphi (128, 1, 0) == -1)
    FAIL ();
  if (test_passthrough (__builtin_strlen (argv[0]) + 1, argv[0])
      != __builtin_strlen (argv[0]) + 1)
    FAIL ();
  if (test_passthrough_nonssa (argv[0]) != __builtin_strlen (argv[0]) + 1)
     FAIL ();
  if (test_dynarray (__builtin_strlen (argv[0])) != __builtin_strlen (argv[0]))
    FAIL ();
  if (test_dynarray_struct (42, 4) !=
      ((42 - 4) * sizeof (struct dynarray_struct)
       - __builtin_offsetof (struct dynarray_struct, c)))
    FAIL ();
  if (test_dynarray_struct (42, 48) != 0)
    FAIL ();
  if (test_substring (128, 4) != 128 - 4)
    FAIL ();
  if (test_substring (128, 142) != 0)
    FAIL ();
  if (test_substring_ptrplus (128, 4) != (128 - 4) * sizeof (int))
    FAIL ();
  if (test_substring_ptrplus (128, 142) != 0)
    FAIL ();
  if (test_dynarray_cond (0) != 16)
    FAIL ();
  if (test_dynarray_cond (1) != 8)
    FAIL ();
  if (test_deploop (128, 4) != 128)
    FAIL ();
  if (test_deploop (128, 129) != 32)
    FAIL ();

  if (test_parmsz (argv[0], __builtin_strlen (argv[0]) + 1, -1)!= 0)
    FAIL ();

  if (test_parmsz (argv[0], __builtin_strlen (argv[0]) + 1, 0)
      != __builtin_strlen (argv[0]) + 1)
    FAIL ();
  if (test_parmsz (argv[0], __builtin_strlen (argv[0]) + 1,
		   __builtin_strlen (argv[0]))!= 1)
    FAIL ();
  if (test_parmsz (argv[0], __builtin_strlen (argv[0]) + 1,
		   __builtin_strlen (argv[0]) + 2)!= 0)
    FAIL ();

  if (nfails > 0)
    __builtin_abort ();

  return 0;
}
