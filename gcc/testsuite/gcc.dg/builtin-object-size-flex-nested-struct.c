/* { dg-do run } */
/* { dg-options "-O2" } */

#ifndef SIZEOF_FLEX_ARRAY
# define SIZEOF_FLEX_ARRAY_DECL
# define SIZEOF_FLEX_ARRAY 0
#else
# define SIZEOF_FLEX_ARRAY_DECL SIZEOF_FLEX_ARRAY
#endif

typedef struct {
  unsigned pad;
  struct {
    unsigned pad;
    char data[SIZEOF_FLEX_ARRAY_DECL];
  } s;
} flex_t;

#define FLEX_ARRAY(p) p->s.data
#define SIZE_OF_FLEX sizeof (unsigned) + sizeof (unsigned)

#include "builtin-object-size-flex-common.h"
