/* { dg-do run } */
/* { dg-options "-O1" } */

#include "builtin-object-size-common.h"

typedef __SIZE_TYPE__ size_t;

void
__attribute__ ((noinline))
pin_pointer(void *)
{
}

struct magic_ {
        char unused[9]; // at least 9
};

struct magic_map {
        struct magic_ *magic;
};

static int
coalesce_entries(struct magic_ **ma)
{
  size_t slen;

  slen = sizeof (**ma);
  *ma = __builtin_malloc (slen);

  for (unsigned i = 0; i < 1; i++)
    {
      char b[1024] = {};
      struct magic_ *ptr = *ma;
      /* It should either give the correct size or fail graciously.  */
      if (__builtin_dynamic_object_size (ptr, 0) != sizeof (**ma)
	  && __builtin_dynamic_object_size (ptr, 0) != (size_t) -1)
	FAIL ();
    }
  return 0;
}

int
main (void)
{
  char buf[128]; // did not shrink, but needs to be more than 100
  struct magic_map *map2;

  map2 = __builtin_malloc (sizeof (*map2));

  pin_pointer(&buf);
  coalesce_entries(&map2->magic);
  pin_pointer(map2);

  DONE ();

  return 0;
}
