/* A program of the ELFv1 ABI of PowerPC, with no libc: where it starts is a function descriptor, which has the address of its
   code and its table of contents, without which it can't find its data. */
static char message[] = "from a descriptor\n";
static long count = sizeof message - 1;

static long call(long number, long a, long b, long c) {
  register long r0 __asm__("r0") = number;
  register long r3 __asm__("r3") = a;
  register long r4 __asm__("r4") = b;
  register long r5 __asm__("r5") = c;
  __asm__ volatile("sc" : "+r"(r0), "+r"(r3), "+r"(r4), "+r"(r5) : : "cr0", "memory");
  return r3;
}

void _start(void) {
  call(4, 1, (long)message, count);
  call(234, 7, 0, 0);
}
