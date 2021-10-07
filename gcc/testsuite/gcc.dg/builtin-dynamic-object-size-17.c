/* { dg-do compile } */
/* { dg-options "-O0 -fdump-tree-ssa" } */

char ax2[];               /* { dg-warning "assumed to have one element" } */
#define __builtin_object_size __builtin_dynamic_object_size
#define DYNAMIC_OBJECT_SIZE
#include "builtin-object-size-17.c"
/* { dg-final { scan-tree-dump-not "failure_on_line" "ssa" } } */
