// What a minimum or a maximum is, which picks an operand, of the controls of denormals and NaNs (testLinuxRaises): x86's MINSD and MAXSD
// of a denormal with DAZ; and AArch64's FMIN, FMINNM and FMAXNM of a denormal with FZ, which say IDC, FMIN of a signaling NaN with DN,
// and FRINTX of a denormal with FZ, which is exact.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int main(void) {
  uint64_t denormal = 0x0008000000000000ull, one = 0x3ff0000000000000ull, signaling = 0x7ff0000000000001ull, out;
  double a, b, r;
  memcpy(&a, &denormal, 8);
  memcpy(&b, &one, 8);
#if defined(__x86_64__)
  unsigned daz = 0x1f80 | 0x40, standard = 0x1f80, after;
  r = a;
  __asm__ volatile("ldmxcsr %2\n minsd %1, %0\n stmxcsr %2" : "+x"(r) : "x"(b), "m"(daz));
  after = daz;
  __asm__ volatile("ldmxcsr %0" : : "m"(standard));
  memcpy(&out, &r, 8);
  printf("minsd denormal, 1 with DAZ: %016llx\n", (unsigned long long)out);
  r = b;
  double negative;
  uint64_t negativeBits = 0x8008000000000000ull;
  memcpy(&negative, &negativeBits, 8);
  __asm__ volatile("ldmxcsr %2\n maxsd %1, %0\n stmxcsr %2" : "+x"(r) : "x"(negative), "m"(daz));
  __asm__ volatile("ldmxcsr %0" : : "m"(standard));
  memcpy(&out, &r, 8);
  printf("maxsd 1, -denormal with DAZ: %016llx, flags %x\n", (unsigned long long)out, after & 0x3f);
#elif defined(__aarch64__)
  uint64_t fz = 1u << 24, dn = 1u << 25, fpsr;
#define OP(name, insn, control, x, y)                                                                                                    \
  do {                                                                                                                                   \
    double p = (x), q = (y);                                                                                                             \
    __asm__ volatile("msr fpcr, %4\n msr fpsr, xzr\n " insn " %d0, %d2, %d3\n mrs %1, fpsr\n msr fpcr, xzr"                            \
                     : "=&w"(r), "=&r"(fpsr) : "w"(p), "w"(q), "r"(control));                                                           \
    memcpy(&out, &r, 8);                                                                                                                 \
    printf("%-26s %016llx flags %llx\n", name, (unsigned long long)out, (unsigned long long)(fpsr & 0x9f));                                                                           \
  } while (0)
  double s;
  memcpy(&s, &signaling, 8);
  OP("fmin denormal, 1 with FZ", "fmin", fz, a, b);
  OP("fminnm denormal, 1 with FZ", "fminnm", fz, a, b);
  OP("fmaxnm -1, denormal with FZ", "fmaxnm", fz, -1.0, a);
  OP("fmin denormal, 1", "fmin", (uint64_t)0, a, b);
  OP("fmin signaling, 1 with DN", "fmin", dn, s, b);
  OP("fmin signaling, 1", "fmin", (uint64_t)0, s, b);
  uint64_t flags;
  __asm__ volatile("msr fpcr, %3\n msr fpsr, xzr\n frintx %d0, %d2\n mrs %1, fpsr\n msr fpcr, xzr" : "=&w"(r), "=&r"(flags) : "w"(a), "r"(fz));
  printf("frintx denormal with FZ: flags %llx\n", (unsigned long long)(flags & 0x9f));
#endif
  return 0;
}
