/* Of what Bap.Analysis.Flattening finds of a flattened function compiled without optimization, whose state is on the stack beside
   what its handlers change: a handler that returns from its middle, and two that end. It is never run past its end. Built as
   flattened.c is, but with -O0, see BapTests/Flattening.lean:

     clang --target=x86_64-linux-gnu -O0 -ffreestanding -fno-builtin -nostdlib -static -fuse-ld=lld -fno-pic -no-pie \
       -Wl,-e,_start flattened0.c -o ../bin/x86_64-linux-none-flattened0 */

volatile unsigned long sink;

__attribute__((noinline)) unsigned long exits(unsigned long n) {
  volatile unsigned state = 0x11;
  unsigned long count = 0;
  for (;;) {
    switch (state) {
    case 0x11: count = 0; state = 0x22; break;
    case 0x22: if (n > 1000) return 7; state = (n & 1) ? 0x33 : 0x44; break;
    case 0x33: n = 3 * n + 1; state = 0x55; break;
    case 0x44: n = n / 2; state = 0x55; break;
    case 0x55: count++; state = n == 1 ? 0x66 : 0x22; break;
    case 0x66: return count;
    }
  }
}

void _start(void) {
  sink = exits(27);
  __asm__ volatile("syscall" : : "a"(60), "D"(0));
  for (;;) {
  }
}
