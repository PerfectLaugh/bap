/* A flattened machine, as cff.c is but freestanding, of what Bap.Analysis.Flattening finds without running it: the dispatcher, which
   switches on a state on the stack that each handler sets, by a constant, by a branch on its input, or by a choice without a branch;
   the handlers; and the graph of the states. The state is volatile, so that the compiler keeps the dispatcher. Of x86_64 and AArch64,
   it is also run, to compare what Bap.Analysis.Cff sees of it, and _start exits; of the others it doesn't end. Built as partition.c
   is, see BapTests/Flattening.lean. */

volatile long sink;

__attribute__((noinline)) void emit(unsigned long n) { sink = n; }

__attribute__((noinline)) unsigned long steps(unsigned long n) {
  volatile unsigned state = 0x3a1f;
  unsigned long count = 0;
  for (;;) {
    switch (state) {
    case 0x3a1f: count = 0; state = 0x91c4; break;
    case 0x91c4: if (n == 1) state = 0x5e02; else state = 0x77b0; break;
    case 0x77b0: state = (n & 1) ? 0x1d6e : 0xc823; break;
    case 0x1d6e: n = 3 * n + 1; state = 0x4b19; break;
    case 0xc823: n = n / 2; state = 0x4b19; break;
    case 0x4b19: count++; state = count == 100 ? 0x0e55 : 0x91c4; break;
    case 0x0e55: emit(n); state = 0x91c4; break;
    case 0x5e02: return count;
    }
  }
}

void _start(void) {
  sink = steps(27);
#if defined(__x86_64__)
  __asm__ volatile("syscall" : : "a"(60), "D"(0));
#elif defined(__aarch64__)
  register long number __asm__("x8") = 93;
  register long code __asm__("x0") = 0;
  __asm__ volatile("svc #0" : : "r"(number), "r"(code));
#endif
  for (;;) {
  }
}
