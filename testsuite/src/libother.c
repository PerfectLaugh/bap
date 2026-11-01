/* What is loaded before libmain.so in one test, to be found first: see libdep.c. */
int either_one(void) { return 2; }
int host_given(int value) { return value + 1000; }
