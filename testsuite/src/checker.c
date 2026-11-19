/* Of what Bap.Analysis.Checker finds of a program without running it: a load through a pointer that one way makes null, and through
   one loaded of memory that one way finds null; a return before what it guards, of MIPS in a delay slot; a local
   that one way leaves unwritten, and one that every way writes; a store at an index of a mask past an array of the stack, and one
   past an array of the program, and loads within them; and two ways, one of which no input takes, which each end in a call of a function of their
   own. It is never run: _start doesn't end. Built as partition.c is, see BapTests/Checker.lean. */

volatile long sink;

long cell;

long table[8];

__attribute__((noinline)) long nulls(long x) {
  long *p = &cell;
  if (x > 3) {
    p = 0;
    /* what the compiler can't see is null, so that it loads through it */
    __asm__ volatile("" : "+r"(p));
  }
  return *p;
}

long *global;

/* A pointer loaded of memory, which one way finds in the first page and then loads through */
__attribute__((noinline)) long fromGlobal(void) {
  long *p = global;
  if ((unsigned long)p < 16) return *p;
  return 0;
}

/* A return that the compiler lays out before what it guards, as the likely way: what is after it isn't of the way that returns */
__attribute__((noinline)) long guarded(long *p) {
  if (__builtin_expect(p == 0, 1)) return 0;
  return *p + 1;
}

__attribute__((noinline)) long nonnull(long x) {
  long *p = &cell;
  if (x > 3) p = &table[1];
  return *p;
}

__attribute__((noinline)) long uninit(long x) {
  volatile long v;
  if (x > 0) v = x;
  return v;
}

__attribute__((noinline)) long init(long x) {
  volatile long v;
  if (x > 0) v = x;
  else v = -x;
  return v;
}

__attribute__((noinline)) long overflow(long i) {
  volatile long buf[4];
  buf[0] = i;
  buf[1] = i;
  buf[2] = i;
  buf[3] = i;
  buf[i & 7] = 5;
  return buf[i & 3];
}

__attribute__((noinline)) long globalOverflow(long i) {
  table[i & 15] = 7;
  return table[i & 7];
}

__attribute__((noinline)) void taken(void) { sink = 1; }

__attribute__((noinline)) void untaken(void) { sink = 2; }

__attribute__((noinline)) long feasible(long x) {
  /* x ^ (x << 7) is a bijection: 645 of x = 5, and 12345 of no x below 100 */
  if ((x ^ (x << 7)) == 645 && (unsigned long)x < 100) taken();
  if ((x ^ (x << 7)) == 12345 && (unsigned long)x < 100) untaken();
  return sink;
}

void _start(void) {
  long total = 0;
  for (long i = 0; i < 10; i++)
    total += nulls(i) + nonnull(i) + uninit(i) + init(i) + overflow(i) + globalOverflow(i) + feasible(i) + fromGlobal() +
             guarded(&cell);
  sink = total;
  for (;;) {
  }
}
