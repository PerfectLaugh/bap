// What x86's floating point raises that a fourth review found the machine didn't, as MXCSR's flags after each (testLinuxRaises):
// COMISD, MINSD, MAXSD and the predicates of CMPSD that signal raise invalid of a quiet NaN, where UCOMISD and CMPEQSD don't; ROUNDSD of
// a denormal raises no denormal, of SSE; and an unnormal of x87 stored as a double is the indefinite, which is invalid.
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint32_t flags(void) {
  uint32_t mxcsr;
  __asm__ volatile("stmxcsr %0" : "=m"(mxcsr));
  return mxcsr & 0x3f;
}
static void clear(void) {
  uint32_t mxcsr = 0x1f80;
  __asm__ volatile("ldmxcsr %0" : : "m"(mxcsr));
}
static double of(uint64_t bits) { double value; memcpy(&value, &bits, 8); return value; }

int main(void) {
  volatile double nan = of(0x7ff8000000000000ull), one = 1.0, tiny = of(1);
  double out = 0;
  clear();
  __asm__ volatile("comisd %1, %0" : : "x"(one), "x"(nan) : "cc");
  printf("comisd of a quiet NaN: %#x\n", flags());
  clear();
  __asm__ volatile("ucomisd %1, %0" : : "x"(one), "x"(nan) : "cc");
  printf("ucomisd of a quiet NaN: %#x\n", flags());
  clear();
  out = one;
  __asm__ volatile("minsd %1, %0" : "+x"(out) : "x"(nan));
  printf("minsd of a quiet NaN: %#x\n", flags());
  clear();
  out = one;
  __asm__ volatile("maxsd %1, %0" : "+x"(out) : "x"(nan));
  printf("maxsd of a quiet NaN: %#x\n", flags());
  clear();
  out = one;
  __asm__ volatile("cmpltsd %1, %0" : "+x"(out) : "x"(nan));
  printf("cmpltsd of a quiet NaN: %#x\n", flags());
  clear();
  out = one;
  __asm__ volatile("cmpeqsd %1, %0" : "+x"(out) : "x"(nan));
  printf("cmpeqsd of a quiet NaN: %#x\n", flags());
  clear();
  out = 0;
  __asm__ volatile("roundsd $4, %1, %0" : "+x"(out) : "x"(tiny));
  printf("roundsd of a denormal: %#x\n", flags());
  // An unnormal: an exponent that isn't 0, and no integer bit.
  unsigned char unnormal[10] = {0, 0, 0, 0, 0, 0, 0, 0x40, 0xff, 0x3f};
  uint16_t status;
  double stored;
  __asm__ volatile("fninit; fldt %2; fstpl %0; fnstsw %1" : "=m"(stored), "=m"(status) : "m"(unnormal));
  uint64_t bits;
  memcpy(&bits, &stored, 8);
  printf("an unnormal stored as a double: %#llx, invalid %d\n", (unsigned long long)bits, status & 1);
  return 0;
}
