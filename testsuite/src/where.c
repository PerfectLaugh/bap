/* Says where its own code is, by an address that it finds relative to
   itself, in hexadecimal, and ends. It has no libc and needs no
   relocation, so that it runs wherever it is loaded:

   clang --target=TRIPLE -O1 -fPIE -nostdlib -ffreestanding -c where.c
   ld.lld -pie --no-dynamic-linker -e start where.o -o ../bin/TRIPLE-where */

static long call(long number, long a, long b, long c) {
#if defined(__x86_64__)
  long result;
  __asm__ volatile("syscall" : "=a"(result) : "a"(number), "D"(a), "S"(b), "d"(c) : "rcx", "r11", "memory");
  return result;
#elif defined(__aarch64__)
  register long x8 __asm__("x8") = number, x0 __asm__("x0") = a, x1 __asm__("x1") = b, x2 __asm__("x2") = c;
  __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2) : "memory");
  return x0;
#endif
}

#if defined(__x86_64__)
#define WRITE 1
#define EXIT 60
#else
#define WRITE 64
#define EXIT 93
#endif

void start(void) {
  char text[18];
  unsigned long at = (unsigned long)&start;
  for (int i = 0; i < 16; i++) text[i] = "0123456789abcdef"[(at >> (60 - 4 * i)) & 15];
  text[16] = '\n';
  call(WRITE, 1, (long)text, 17);
  call(EXIT, 0, 0, 0);
}
