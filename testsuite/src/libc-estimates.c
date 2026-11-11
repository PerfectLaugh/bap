// What Arm's estimates give, which its pseudocode says to the bit, FPRecipEstimate and FPRSqrtEstimate, with the flags of FPSR, or
// of AArch32's FPSCR (testLinuxRaises): FRECPE and FRSQRTE of single and double precision on AArch64, and VRECPE and VRSQRTE of NEON on
// AArch32, which go by its standard FPSCR, whatever FPSCR says.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static const uint32_t singles[] = {0x40000000, 0x3f800000, 0x40490fdb, 0x3dcccccd, 0x7f7fffff, 0x00400000, 0x00100000,
                                   0x00000001, 0x80000000, 0x00000000, 0x7f800000, 0xff800000, 0xc0000000, 0x7fc00000,
                                   0x7f800001, 0x3f7fffff, 0x7e800000, 0x00800000};
static const uint64_t doubles[] = {0x4000000000000000, 0x3fb999999999999a, 0x7fefffffffffffff, 0x0008000000000000,
                                   0x0000000000000001, 0xbff0000000000000, 0x7ff0000000000000, 0x0010000000000000};

#if defined(__aarch64__)
static uint32_t flags(void) {
  uint64_t value;
  __asm__ volatile("mrs %0, fpsr" : "=r"(value));
  return (uint32_t)value;
}
static void clear(void) { __asm__ volatile("msr fpsr, %0" : : "r"((uint64_t)0)); }
#endif

int main(void) {
  for (unsigned index = 0; index < sizeof singles / sizeof singles[0]; index++) {
    float x, r, q;
    uint32_t rb, qb, rf, qf;
    memcpy(&x, &singles[index], 4);
#if defined(__aarch64__)
    clear();
    __asm__ volatile("frecpe %s0, %s1" : "=w"(r) : "w"(x));
    rf = flags();
    clear();
    __asm__ volatile("frsqrte %s0, %s1" : "=w"(q) : "w"(x));
    qf = flags();
#else
    __asm__ volatile("vmsr fpscr, %4\n vdup.32 d0, %2\n vrecpe.f32 d1, d0\n vmov %0, s2\n vmrs %1, fpscr"
                     : "=r"(r), "=r"(rf) : "r"(x), "r"(0), "r"(0u) : "d0", "d1");
    __asm__ volatile("vmsr fpscr, %4\n vdup.32 d0, %2\n vrsqrte.f32 d1, d0\n vmov %0, s2\n vmrs %1, fpscr"
                     : "=r"(q), "=r"(qf) : "r"(x), "r"(0), "r"(0u) : "d0", "d1");
#endif
    memcpy(&rb, &r, 4);
    memcpy(&qb, &q, 4);
    printf("%08x: recip %08x flags %x, rsqrt %08x flags %x\n", singles[index], rb, rf & 0x9f, qb, qf & 0x9f);
  }
#if defined(__aarch64__)
  for (unsigned index = 0; index < sizeof doubles / sizeof doubles[0]; index++) {
    double x, r, q;
    uint64_t rb, qb;
    memcpy(&x, &doubles[index], 8);
    clear();
    __asm__ volatile("frecpe %d0, %d1" : "=w"(r) : "w"(x));
    uint32_t rf = flags();
    clear();
    __asm__ volatile("frsqrte %d0, %d1" : "=w"(q) : "w"(x));
    uint32_t qf = flags();
    memcpy(&rb, &r, 8);
    memcpy(&qb, &q, 8);
    printf("%016llx: recip %016llx flags %x, rsqrt %016llx flags %x\n", (unsigned long long)doubles[index], (unsigned long long)rb,
           rf & 0x9f, (unsigned long long)qb, qf & 0x9f);
  }
  // Towards zero, of what is too small to have a reciprocal: the largest number rather than infinity.
  uint64_t control = 3u << 22;
  __asm__ volatile("msr fpcr, %0" : : "r"(control));
  float tiny, r;
  uint32_t bits = 0x00100000, rb;
  memcpy(&tiny, &bits, 4);
  __asm__ volatile("frecpe %s0, %s1" : "=w"(r) : "w"(tiny));
  memcpy(&rb, &r, 4);
  printf("towards zero, of a tiny one: %08x\n", rb);
#endif
  return 0;
}
