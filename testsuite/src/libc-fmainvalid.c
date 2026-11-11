// A fused multiply-add of an infinity and a zero, with a quiet NaN to add, is invalid on Arm, RISC-V and PowerPC, and isn't on x86
// (testLinuxRaises): the result, and the flags of invalid, as each has them.
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int main(void) {
  volatile double inf = INFINITY, zero = 0.0, quiet = NAN;
  double a = inf, b = zero, c = quiet, r;
  uint64_t bits;
  unsigned long long flags = 0;
#if defined(__aarch64__)
  __asm__ volatile("msr fpsr, xzr\n fmadd %d0, %d1, %d2, %d3\n mrs %4, fpsr" : "=&w"(r), "+w"(a), "+w"(b), "+w"(c), "=r"(flags));
  flags &= 1;
#elif defined(__riscv)
  __asm__ volatile("csrw fflags, zero\n fmadd.d %0, %1, %2, %3\n csrr %4, fflags" : "=&f"(r), "+f"(a), "+f"(b), "+f"(c), "=r"(flags));
  flags = flags >> 4 & 1;
#elif defined(__powerpc__)
  union {
    double d;
    uint64_t u;
  } status;
  double clear = 0.0;
  __asm__ volatile("mtfsf 0xff, %5\n fmadd %0, %1, %2, %3\n mffs %4" : "=&d"(r), "+d"(a), "+d"(b), "+d"(c), "=&d"(status.d) : "d"(clear));
  flags = status.u >> 20 & 1;
#elif defined(__x86_64__)
  unsigned mxcsr = 0x1f80;
  __asm__ volatile("ldmxcsr %4\n vmovsd %1, %%xmm0\n vmovsd %2, %%xmm1\n vmovsd %3, %%xmm2\n vfmadd213sd %%xmm2, %%xmm1, %%xmm0\n"
                   "vmovsd %%xmm0, %0\n stmxcsr %4"
                   : "=m"(r) : "m"(a), "m"(b), "m"(c), "m"(mxcsr) : "xmm0", "xmm1", "xmm2");
  flags = mxcsr & 1;
#endif
  memcpy(&bits, &r, 8);
  printf("fma inf, 0, quiet NaN: %016llx, invalid %llu\n", (unsigned long long)bits, flags);
  return 0;
}
