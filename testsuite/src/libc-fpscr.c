// What PowerPC's FPSCR says after each kind of operation, from all clear (testLinuxRaises): the invalid operations each by its own bit
// of VXSNAN, VXISI, VXIDI, VXZDZ, VXIMZ, VXVC, VXSQRT and VXCVI, with VX of them, FX of any exception that comes to be, FI and FR of
// what was rounded and FPRF of the class of the result; VX that stays when a bit of FPSCR is written; and CR1 of a record form.
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static double of(uint64_t bits) { double value; memcpy(&value, &bits, 8); return value; }

static uint32_t fpscr(void) {
  union {
    double d;
    uint64_t u;
  } value;
  __asm__ volatile("mffs %0" : "=d"(value.d));
  // But FR, which qemu doesn't keep, of whether what was rounded went up.
  return (uint32_t)value.u & ~0x40000u;
}

static void clear(void) {
  double zero = 0.0;
  __asm__ volatile("mtfsf 0xff, %0" : : "d"(zero));
}

#define TWO(name, insn, x, y)                                                                                                            \
  do {                                                                                                                                   \
    double a = (x), b = (y), r;                                                                                                          \
    clear();                                                                                                                             \
    __asm__ volatile(insn " %0, %1, %2" : "=d"(r) : "d"(a), "d"(b));                                                                    \
    printf("%-22s %08x\n", name, fpscr());                                                                                               \
  } while (0)

int main(void) {
  double inf = INFINITY, qnan = of(0x7ff8000000000000ull), snan = of(0x7ff0000000000001ull);
  TWO("fdiv 0/0", "fdiv", 0.0, 0.0);
  TWO("fdiv inf/inf", "fdiv", inf, inf);
  TWO("fsub inf-inf", "fsub", inf, inf);
  TWO("fmul inf*0", "fmul", inf, 0.0);
  TWO("fadd snan", "fadd", snan, 1.0);
  TWO("fadd qnan", "fadd", qnan, 1.0);
  TWO("fadd 1+2^-60", "fadd", 1.0, 0x1p-60);
  TWO("fadd 1+3*2^-53", "fadd", 1.0, 0x1.8p-52);
  TWO("fadd 3+(-5)", "fadd", 3.0, -5.0);
  TWO("fdiv 1/0", "fdiv", 1.0, 0.0);
  TWO("fmul huge", "fmul", 0x1p1000, 0x1p1000);
  TWO("fmul tiny", "fmul", 0x1p-1000, 0x1p-60);
  TWO("fsub 2-2", "fsub", 2.0, 2.0);
  double r, a = -1.0;
  clear();
  __asm__ volatile("fsqrt %0, %1" : "=d"(r) : "d"(a));
  printf("%-22s %08x\n", "fsqrt -1", fpscr());
  clear();
  __asm__ volatile("fctiwz %0, %1" : "=d"(r) : "d"(qnan));
  // Of which FPRF is undefined.
  printf("%-22s %08x\n", "fctiwz qnan", fpscr() & ~0x1f000u);
  clear();
  __asm__ volatile("fcmpo 0, %0, %1" : : "d"(qnan), "d"(1.0) : "cr0");
  // Of which C, which qemu sets, isn't of what FCMPO alters.
  printf("%-22s %08x\n", "fcmpo qnan", fpscr() & ~0x10000u);
  clear();
  __asm__ volatile("fcmpu 0, %0, %1" : : "d"(qnan), "d"(1.0) : "cr0");
  printf("%-22s %08x\n", "fcmpu qnan", fpscr());
  clear();
  __asm__ volatile("fcmpu 0, %0, %1" : : "d"(snan), "d"(1.0) : "cr0");
  printf("%-22s %08x\n", "fcmpu snan", fpscr());
  clear();
  double zero = 0.0;
  __asm__ volatile("fdiv %0, %1, %1\n mtfsb0 31" : "=d"(r) : "d"(zero));
  printf("%-22s %08x\n", "0/0, then mtfsb0 31", fpscr());
  clear();
  uint32_t cr;
  __asm__ volatile("fdiv. %0, %2, %2\n mfcr %1" : "=d"(r), "=r"(cr) : "d"(zero) : "cr1");
  printf("%-22s %x\n", "fdiv. 0/0 CR1", (cr >> 24) & 15);
  clear();
  return 0;
}
