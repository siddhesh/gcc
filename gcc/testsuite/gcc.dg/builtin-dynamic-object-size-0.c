/* { dg-do run } */
/* { dg-options "-O2" } */

typedef __SIZE_TYPE__ size_t;
#define abort __builtin_abort

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

size_t
__attribute__ ((noinline))
test_deploop (size_t sz, size_t cond)
{
  char *bin = __builtin_alloca (32);

  for (size_t i = 0; i < sz; i++)
    if (i == cond)
      bin = __builtin_alloca (64);

  return __builtin_dynamic_object_size (bin, 0);
}

unsigned nfails = 0;

#define FAIL() ({ \
  __builtin_printf ("Failure at line: %d\n", __LINE__);			      \
  nfails++;								      \
})

int
main (int argc, char **argv)
{
  if (test_builtin_malloc_condphi (1) != 32)
    FAIL ();
  if (test_builtin_malloc_condphi (0) != 64)
    FAIL ();
  if (test_builtin_calloc_condphi (128, 1, 0) == 128)
    FAIL ();
  if (test_deploop (128, 129) != 32)
    FAIL ();

  if (nfails > 0)
    __builtin_abort ();

  return 0;
}
