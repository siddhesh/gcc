/* { dg-do run } */
/* { dg-options "-O0" } */

#define DYNAMIC_OBJECT_SIZE
#define __builtin_object_size __builtin_dynamic_object_size
char ax2[];               /* { dg-warning "assumed to have one element" } */
#include "builtin-object-size-16.c"
