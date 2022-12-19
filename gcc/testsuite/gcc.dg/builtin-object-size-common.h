unsigned nfails = 0;

#define FAIL() ({ \
  __builtin_printf ("Failure at line: %d\n", __LINE__);			      \
  nfails++;								      \
})

#define DONE() ({ \
  if (nfails > 0)							      \
    __builtin_abort ();							      \
  return 0;								      \
})
