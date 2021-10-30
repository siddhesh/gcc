/* { dg-do compile { target i?86-*-linux* i?86-*-gnu* x86_64-*-linux* } } */
/* { dg-options "-O2" } */
/* For dynamic object sizes we 'succeed' if the returned size is known for
   maximum object size.  */

typedef __SIZE_TYPE__ size_t;
extern void abort (void);
extern char buf[0x40000000];

void
test1 (size_t x)
{
  char *p = &buf[8];
  size_t i;

  for (i = 0; i < x; ++i)
    p = p + 4;
#ifdef DYNAMIC_OBJECT_SIZE
  if (__builtin_object_size (p, 0) == -1)
#else
  if (__builtin_object_size (p, 0) != sizeof (buf) - 8)
#endif
    abort ();
}

void
test2 (size_t x)
{
  char *p = &buf[8];
  size_t i;

  for (i = 0; i < x; ++i)
    p = p + 4;
#ifdef DYNAMIC_OBJECT_SIZE
  if (__builtin_object_size (p, 1) == -1)
#else
  if (__builtin_object_size (p, 1) != sizeof (buf) - 8)
#endif
    abort ();
}

#ifndef DYNAMIC_OBJECT_SIZE
void
test3 (size_t x)
{
  char *p = &buf[8];
  size_t i;

  for (i = 0; i < x; ++i)
    p = p + 4;
  if (__builtin_object_size (p, 2) != 0)
    abort ();
}

void
test4 (size_t x)
{
  char *p = &buf[8];
  size_t i;

  for (i = 0; i < x; ++i)
    p = p + 4;
  if (__builtin_object_size (p, 3) != 0)
    abort ();
}
#endif

/* { dg-final { scan-assembler-not "abort" } } */
