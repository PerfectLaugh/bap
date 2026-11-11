// Instructions whose rounding is to nearest whatever the rounding mode of the machine is, which a fifth review found went by that
// mode instead (testLinuxRaises): with the mode toward zero or down, MIPS's ROUND.W against CVT.W, x86's VCVTPS2PH of mode 0 against 4,
// NEON's VADD against VFP's, and AltiVec's VADDFP and VRFIN, which also say nothing to FPSCR.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

int main(void) {
#if defined(__mips__)
  float x = 2.7f;
  int rounded, converted;
  unsigned fcsr;
  __asm__ volatile("li $t0, 1\n ctc1 $t0, $31\n round.w.s $f2, %3\n mfc1 %0, $f2\n cvt.w.s $f4, %3\n mfc1 %1, $f4\n"
                   "cfc1 %2, $31\n ctc1 $zero, $31\n"
                   : "=r"(rounded), "=r"(converted), "=r"(fcsr) : "f"(x) : "t0", "$f2", "$f4");
  printf("toward zero: round.w.s 2.7 %d, cvt.w.s %d\n", rounded, converted);
#elif defined(__x86_64__)
  uint32_t bits = 0x3f801008, down = 0x3f80 | (1 << 13);
  float x;
  memcpy(&x, &bits, 4);
  unsigned short nearest, current;
  __asm__ volatile("ldmxcsr %3\n vmovd %2, %%xmm0\n vcvtps2ph $0, %%xmm0, %%xmm1\n vmovd %%xmm1, %%eax\n mov %%ax, %0\n"
                   "vcvtps2ph $4, %%xmm0, %%xmm1\n vmovd %%xmm1, %%eax\n mov %%ax, %1\n"
                   : "=m"(nearest), "=m"(current) : "r"(bits), "m"(down) : "eax", "xmm0", "xmm1");
  uint32_t standard = 0x1f80;
  __asm__ volatile("ldmxcsr %0" : : "m"(standard));
  printf("down: vcvtps2ph of mode 0 %04x, of MXCSR %04x\n", nearest, current);
  (void)x;
#elif defined(__arm__)
  uint32_t one = 0x3f800000, small = 0x33820000, vector, scalar, mode = 2u << 22;
  __asm__ volatile("vmsr fpscr, %4\n vdup.32 d0, %2\n vdup.32 d1, %3\n vadd.f32 d2, d0, d1\n vmov %0, s4\n"
                   "vmov s6, %2\n vmov s7, %3\n vadd.f32 s8, s6, s7\n vmov %1, s8\n vmsr fpscr, %5\n"
                   : "=&r"(vector), "=&r"(scalar) : "r"(one), "r"(small), "r"(mode), "r"(0) : "d0", "d1", "d2", "d3", "d4");
  printf("down: neon vadd %08x, vfp vadd %08x\n", vector, scalar);
#elif defined(__powerpc__)
  typedef float v4 __attribute__((vector_size(16)));
  v4 a = {1.0f, 3.5f, -3.5f, 1.0f}, b = {0x1p-24f + 0x1p-30f, 0, 0, 0}, r;
  union {
    double d;
    uint64_t u;
  } f = {.u = 1}, after;
  __asm__ volatile("mtfsf 0xff, %4\n vaddfp %0, %1, %3\n vrfin %1, %1\n mffs %2\n"
                   : "=&v"(r), "+v"(a), "=&d"(after.d) : "v"(b), "d"(f.d));
  double zero = 0.0;
  __asm__ volatile("mtfsf 0xff, %0" : : "d"(zero));
  uint32_t first;
  memcpy(&first, &r, 4);
  printf("toward zero: vaddfp %08x, vrfin %g %g, FPSCR %llx\n", first, a[1], a[2], (unsigned long long)(after.u & 0xffffffff));
#endif
  return 0;
}
