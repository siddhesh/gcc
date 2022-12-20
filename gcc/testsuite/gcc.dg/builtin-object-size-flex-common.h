#include "builtin-object-size-common.h"

typedef __SIZE_TYPE__ size_t;

void
__attribute__ ((noinline))
test_flexarray_allocate (const char *name)
{
  size_t n = sizeof (flex_t);

  if (name != (void *) 0)
    n += __builtin_strlen (name) + 1;

  flex_t *p = __builtin_malloc (n);

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 0)
      != n - sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 1)
      != n - sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 2)
      != n - sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 3)
      != n - sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  __builtin_free (p);
}

void
__attribute__ ((noinline))
__attribute__ ((access (read_only, 1, 2)))
test_flexarray_access (flex_t *p, size_t sz)
{
  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 0)
      != (sz - 1) * sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 1)
      != (sz - 1) * sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 2)
      != (sz - 1) * sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 3)
      != (sz - 1) * sizeof (*p) + SIZEOF_FLEX_ARRAY)
    FAIL ();
}

void
__attribute__ ((noinline))
test_flexarray_none (flex_t *p)
{
  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 0) != -1)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 1) != -1)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 2) != 0)
    FAIL ();

  if (__builtin_dynamic_object_size (FLEX_ARRAY (p), 3) != SIZEOF_FLEX_ARRAY)
    FAIL ();
}

int
main (int argc, char **argv)
{
  const char *str = "qwertyuiopasdfgghjklzxcvbnm";

  test_flexarray_allocate (str);

  const size_t sz = 1024;
  flex_t *p = __builtin_malloc (sz * sizeof (*p));

  test_flexarray_access (p, sz);

  test_flexarray_none (p);
  __builtin_free (p);

  DONE ();
}
