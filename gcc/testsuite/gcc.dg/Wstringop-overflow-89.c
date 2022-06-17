/* PR middle-end/97185 - missing -Wstringop-overflow for 0 or invalid sizes.
   { dg-do compile }
   { dg-options "-O2" } */

void
f0 (void *p, const void *q, int n)
{ 
  if (n > 0)
    return;
  __builtin_memcpy (p, q, n);      // { dg-warning "-Wstringop-overflow" }
}

void
f1 (void *p, const void *q, int n)
{
  if (n > 0)
    return;
  __builtin_memmove (p, q, n);      // { dg-warning "-Wstringop-overflow" }
}

void
f2 (char *p, const char *q, int n)
{
  if (n > 0)
    return;
  __builtin_strncpy (p, q, n);      // { dg-warning "-Wstringop-overflow" }
}

void
f3 (void *p, int n)
{ 
  if (n > 0)
    return;
  __builtin_memset (p, 0, n);      // { dg-warning "-Wstringop-overflow" }
}
