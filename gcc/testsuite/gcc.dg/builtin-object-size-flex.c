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
  char data[SIZEOF_FLEX_ARRAY_DECL];
} flex_t;

#define FLEX_ARRAY(p) p->data

#include "builtin-object-size-flex-common.h"
