/* the stand-in libc, whose functions Primus replaces with its stubs,
   so that the programs link dynamically without a libc */

int putchar(int c) { return c; }
int getchar(void) { return -1; }
void exit(int code) { for (;;); }
void *stdin;
int fgetc(void *stream) { return -1; }
