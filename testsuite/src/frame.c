/* Of what Bap.Analysis.Frame finds of functions without running them: how many arguments each takes, in registers and on the
   stack; whether its callers use what it returns; that it keeps the registers its convention has it keep, which `saver` has to
   save, as what it holds lives across its calls; and where it leaves the stack pointer, which a `stdcall` function of i686 moves
   past its arguments. It is never run: _start doesn't end. Built as partition.c is, see BapTests/Partition.lean. */

volatile long sink;

__attribute__((noinline)) void zero(void) { sink = 1; }

__attribute__((noinline)) long one(long a) { return a * sink + 3; }

__attribute__((noinline)) long three(long a, long b, long c) { return (a + sink) * (b - sink) + c; }

__attribute__((noinline)) long eight(long a, long b, long c, long d, long e, long f, long g, long h) {
  return (a * sink) ^ (b + sink) ^ (c - sink) ^ (d | sink) ^ (e & sink) ^ (f * 3) ^ (g + 7) ^ (h * sink);
}

__attribute__((noinline)) long saver(long x) {
  long a = one(x);
  long b = one(a + 1);
  long c = one(b + x);
  return a + b + c + x;
}

#if defined(__i386__)
__attribute__((noinline, stdcall)) long cleans(long a, long b, long c) { return a * b + c + sink; }
#endif

void _start(void) {
  long total = 0;
  for (long i = 0; i < 10; i++) {
    zero();
    total += one(i) + three(i, total, 2) + eight(i, 1, 2, 3, 4, 5, 6, total) + saver(i);
#if defined(__i386__)
    total += cleans(i, 2, total);
#endif
  }
  sink = total;
  for (;;) {
  }
}
