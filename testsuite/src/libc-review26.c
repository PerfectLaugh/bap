// What x87 does that a review found the machine didn't, of x86_64: what a store of a register to memory, FSTP of 32 and of 64 bits,
// raises, as the status word has it after, of its six exceptions.
//   tiny: what is below every number of where it goes, however far, is underflow and inexact, and not inexact alone.
//   denormal: a denormal in the register is none of a store, which has no operand to say it of; a load of one from memory is.
#include <stdio.h>
#include <string.h>

static long double of(unsigned short exponent, unsigned long long significand) {
  long double value = 0;
  memcpy(&value, &significand, 8);
  memcpy((char *)&value + 8, &exponent, 2);
  return value;
}

static unsigned toDouble(long double value) {
  double stored;
  unsigned short status;
  __asm__("fldt %1\n fnclex\n fstpl %0\n fnstsw %2" : "=m"(stored) : "m"(value), "m"(status));
  return status & 0x3f;
}

static unsigned toFloat(long double value) {
  float stored;
  unsigned short status;
  __asm__("fldt %1\n fnclex\n fstps %0\n fnstsw %2" : "=m"(stored) : "m"(value), "m"(status));
  return status & 0x3f;
}

static unsigned fromDouble(double value) {
  unsigned short status;
  __asm__("fnclex\n fldl %0\n fnstsw %1\n fstp %%st(0)" : : "m"(value), "m"(status));
  return status & 0x3f;
}

int main(void) {
  printf("tiny to float: %x\n", toFloat(of(0x24e1, 0xdff94831dc6b0910ULL)));
  printf("least normal to float: %x\n", toFloat(of(0x0001, 0x8000000000000000ULL)));
  printf("least normal to double: %x\n", toDouble(of(0x0001, 0x8000000000000000ULL)));
  printf("2^-1000 and a bit to float: %x\n", toFloat(of(0x3fff - 1000, 0x8000000000000001ULL)));
  printf("2^-140 to float: %x\n", toFloat(of(0x3fff - 140, 0x8000000000000000ULL)));
  printf("denormal to double: %x\n", toDouble(of(0x0000, 0x5a6ee4ff48ff7591ULL)));
  printf("denormal to float: %x\n", toFloat(of(0x0000, 0x0000000000000007ULL)));
  printf("one to float: %x\n", toFloat(of(0x3fff, 0x8000000000000000ULL)));
  printf("a third to double: %x\n", toDouble(of(0x3ffd, 0xaaaaaaaaaaaaaaabULL)));
  printf("a denormal from double: %x\n", fromDouble(4.9406564584124654e-324));
  printf("one from double: %x\n", fromDouble(1.0));
  return 0;
}
