// Which comparisons of a quiet NaN raise invalid, as each architecture has them (testLinuxRaises): the ordered ones do, and the quiet
// ones don't. AArch64's FCMP and FCMPE, FCCMPE and FCMGT and FCMEQ; AArch32's VCMP and VCMPE and NEON's VCGT and VCEQ; RISC-V's FEQ,
// FLT and FLE; x87's FUCOM, FCOM, FCOMI and FTST; and MIPS's C.OLT, C.LT and R6's CMP.LT and CMP.SLT.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

// A quiet NaN: of MIPS before NaN2008, of the top bit of the fraction clear.
#if defined(__mips__) && !defined(__mips_nan2008)
static float nanf32(void) { uint32_t bits = 0x7fbfffff; float value; memcpy(&value, &bits, 4); return value; }
static double nanf64(void) { uint64_t bits = 0x7ff7ffffffffffffull; double value; memcpy(&value, &bits, 8); return value; }
#else
static float nanf32(void) { uint32_t bits = 0x7fc00000; float value; memcpy(&value, &bits, 4); return value; }
static double nanf64(void) { uint64_t bits = 0x7ff8000000000000ull; double value; memcpy(&value, &bits, 8); return value; }
#endif

#define SHOW(name) printf("%-10s %x\n", name, flags())

#if defined(__aarch64__)
static unsigned flags(void) { uint64_t value; __asm__ volatile("mrs %0, fpsr\n msr fpsr, xzr" : "=r"(value)); return value & 0x9f; }
#elif defined(__arm__)
static unsigned flags(void) {
  unsigned value;
  __asm__ volatile("vmrs %0, fpscr\n vmsr fpscr, %1" : "=r"(value) : "r"(0));
  return value & 0x9f;
}
#elif defined(__riscv)
static unsigned flags(void) { unsigned value; __asm__ volatile("csrrw %0, fflags, zero" : "=r"(value)); return value; }
#elif defined(__x86_64__) || defined(__i386__)
static unsigned flags(void) {
  unsigned short status;
  __asm__ volatile("fnstsw %0\n fnclex" : "=m"(status));
  return status & 0x3f;
}
#elif defined(__mips__)
static unsigned flags(void) {
  unsigned value;
  __asm__ volatile("cfc1 %0, $31\n ctc1 $zero, $31" : "=r"(value));
  return value >> 2 & 0x1f;
}
#endif

int main(void) {
  volatile float n = nanf32(), one = 1.0f;
  volatile double dn = nanf64(), done = 1.0;
  float a = n, b = one;
  double c = dn, d = done;
  flags();
#if defined(__aarch64__)
  float r;
  __asm__ volatile("fcmp %s0, %s1" : : "w"(a), "w"(b) : "cc"); SHOW("fcmp");
  __asm__ volatile("fcmpe %s0, %s1" : : "w"(a), "w"(b) : "cc"); SHOW("fcmpe");
  __asm__ volatile("fcmpe %s0, #0.0" : : "w"(a) : "cc"); SHOW("fcmpe #0");
  __asm__ volatile("cmp xzr, xzr\n fccmpe %s0, %s1, #0, eq" : : "w"(a), "w"(b) : "cc"); SHOW("fccmpe");
  __asm__ volatile("fcmgt %s0, %s1, %s2" : "=w"(r) : "w"(a), "w"(b)); SHOW("fcmgt");
  __asm__ volatile("fcmeq %s0, %s1, %s2" : "=w"(r) : "w"(a), "w"(b)); SHOW("fcmeq");
  __asm__ volatile("facge %s0, %s1, %s2" : "=w"(r) : "w"(a), "w"(b)); SHOW("facge");
  (void)c; (void)d;
#elif defined(__arm__)
  __asm__ volatile("vcmp.f32 %0, %1\n vmrs APSR_nzcv, fpscr" : : "t"(a), "t"(b) : "cc"); SHOW("vcmp");
  __asm__ volatile("vcmpe.f32 %0, %1\n vmrs APSR_nzcv, fpscr" : : "t"(a), "t"(b) : "cc"); SHOW("vcmpe");
  __asm__ volatile("vcmpe.f64 %P0, #0\n vmrs APSR_nzcv, fpscr" : : "w"(c) : "cc"); SHOW("vcmpe #0");
  uint32_t bits;
  memcpy(&bits, &a, 4);
  __asm__ volatile("vdup.32 d16, %0\n vmov.f32 d17, #1.0\n vcgt.f32 d18, d16, d17" : : "r"(bits) : "d16", "d17", "d18"); SHOW("vcgt");
  __asm__ volatile("vdup.32 d16, %0\n vmov.f32 d17, #1.0\n vceq.f32 d18, d16, d17" : : "r"(bits) : "d16", "d17", "d18"); SHOW("vceq");
  (void)d;
#elif defined(__riscv)
  long r;
  __asm__ volatile("feq.s %0, %1, %2" : "=r"(r) : "f"(a), "f"(b)); SHOW("feq.s");
  __asm__ volatile("flt.s %0, %1, %2" : "=r"(r) : "f"(a), "f"(b)); SHOW("flt.s");
  __asm__ volatile("fle.d %0, %1, %2" : "=r"(r) : "f"(c), "f"(d)); SHOW("fle.d");
#elif defined(__x86_64__)
  __asm__ volatile("fldl %0\n fldl %1\n fucompp" : : "m"(d), "m"(c)); SHOW("fucompp");
  __asm__ volatile("fldl %0\n fldl %1\n fcompp" : : "m"(d), "m"(c)); SHOW("fcompp");
  __asm__ volatile("fldl %0\n fldl %1\n fucomip %%st(1), %%st\n fstp %%st(0)" : : "m"(d), "m"(c) : "cc"); SHOW("fucomip");
  __asm__ volatile("fldl %0\n fldl %1\n fcomip %%st(1), %%st\n fstp %%st(0)" : : "m"(d), "m"(c) : "cc"); SHOW("fcomip");
  __asm__ volatile("fldl %0\n ftst\n fstp %%st(0)" : : "m"(c)); SHOW("ftst");
#elif defined(__mips__)
  __asm__ volatile("c.olt.s %0, %1" : : "f"(a), "f"(b)); SHOW("c.olt.s");
  __asm__ volatile("c.lt.s %0, %1" : : "f"(a), "f"(b)); SHOW("c.lt.s");
  __asm__ volatile("c.ngt.d %0, %1" : : "f"(c), "f"(d)); SHOW("c.ngt.d");
  __asm__ volatile("c.eq.d %0, %1" : : "f"(c), "f"(d)); SHOW("c.eq.d");
#endif
  return 0;
}
