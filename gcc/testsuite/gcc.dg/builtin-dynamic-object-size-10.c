/* { dg-do compile } */
/* { dg-options "-O2 -fdump-tree-dynobjsz1-details" } */
// { dg-skip-if "packed attribute missing for drone_source_packet" { "epiphany-*-*" } }

#define __builtin_object_size __builtin_dynamic_object_size
#include "builtin-object-size-10.c"

/* { dg-final { scan-tree-dump "maximum dynamic object size 21" "objsz1" } } */
/* { dg-final { scan-tree-dump "maximum dynamic subobject size 16" "objsz1" } } */
