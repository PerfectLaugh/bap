// What x87 and SSE compute that a fifth review found the machine couldn't (testLinuxRaises): F2XM1, FSIN, FCOS, FPTAN, FPATAN, FYL2X,
// FYL2XP1, each rounded to a double, as x87 isn't always the nearest in the last of its own bits; FXTRACT, FPREM and FPREM1 exactly,
// with the bits of the quotient in the status word; FSCALE; FBSTP and FBLD of packed decimals; and RCPSS and RSQRTSS, to within their 12 bits.
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static double one(const char *op, double x) {
  double out;
  if (!strcmp(op, "f2xm1")) __asm__("fldl %1; f2xm1; fstpl %0" : "=m"(out) : "m"(x));
  else if (!strcmp(op, "fsin")) __asm__("fldl %1; fsin; fstpl %0" : "=m"(out) : "m"(x));
  else if (!strcmp(op, "fcos")) __asm__("fldl %1; fcos; fstpl %0" : "=m"(out) : "m"(x));
  else __asm__("fldl %1; fptan; fstp %%st(0); fstpl %0" : "=m"(out) : "m"(x));
  return out;
}

static double two(const char *op, double y, double x) {
  double out;
  if (!strcmp(op, "fpatan")) __asm__("fldl %1; fldl %2; fpatan; fstpl %0" : "=m"(out) : "m"(y), "m"(x));
  else if (!strcmp(op, "fyl2x")) __asm__("fldl %1; fldl %2; fyl2x; fstpl %0" : "=m"(out) : "m"(y), "m"(x));
  else __asm__("fldl %1; fldl %2; fyl2xp1; fstpl %0" : "=m"(out) : "m"(y), "m"(x));
  return out;
}

static void remainder87(int nearest, double x, double y) {
  double out;
  uint16_t status;
  if (nearest) __asm__("fninit; fldl %3; fldl %2; fprem1; fnstsw %1; fstpl %0; fstp %%st(0)" : "=m"(out), "=m"(status) : "m"(x), "m"(y));
  else __asm__("fninit; fldl %3; fldl %2; fprem; fnstsw %1; fstpl %0; fstp %%st(0)" : "=m"(out), "=m"(status) : "m"(x), "m"(y));
  printf("%s %g %g: %a, C0 %d C1 %d C2 %d C3 %d\n", nearest ? "fprem1" : "fprem", x, y, out, status >> 8 & 1, status >> 9 & 1,
         status >> 10 & 1, status >> 14 & 1);
}

int main(void) {
  double values[] = {0.5, 1.0, -0.75, 1e-10, 3.0};
  const char *ones[] = {"f2xm1", "fsin", "fcos", "fptan"};
  for (int op = 0; op < 4; op++)
    for (int index = 0; index < 5; index++) {
      if (op == 0 && index == 4) continue;
      printf("%s %g: %a\n", ones[op], values[index], one(ones[op], values[index]));
    }
  const char *twos[] = {"fpatan", "fyl2x", "fyl2xp1"};
  double pairs[][2] = {{1, 2}, {-3, 0.5}, {2, 10}, {0.5, 0.25}};
  for (int op = 0; op < 3; op++)
    for (int index = 0; index < 4; index++)
      printf("%s %g %g: %a\n", twos[op], pairs[index][0], pairs[index][1], two(twos[op], pairs[index][0], pairs[index][1]));
  double exponent, significand, twelve = -12.0;
  __asm__("fldl %2; fxtract; fstpl %1; fstpl %0" : "=m"(exponent), "=m"(significand) : "m"(twelve));
  printf("fxtract -12: %g %g\n", exponent, significand);
  remainder87(0, 10, 3);
  remainder87(1, 10, 3);
  remainder87(0, -7.5, 2);
  remainder87(1, 11, 2);
  remainder87(0, 1e30, 3);
  double scales[][2] = {{1, 0}, {1, -1}, {0.5, 3}, {3, 100}, {1, 70000}, {1, -70000}, {1.5, 2.9}};
  for (int index = 0; index < 7; index++) {
    double out;
    __asm__("fldl %2; fldl %1; fscale; fstpl %0; fstp %%st(0)" : "=m"(out) : "m"(scales[index][0]), "m"(scales[index][1]));
    printf("fscale %g %g: %a\n", scales[index][0], scales[index][1], out);
  }
  double outside[] = {-9223372036854775808.0, -2147483649.0, 40000.0, 2147483647.5, -9223372036854777856.0, 1e300};
  for (int index = 0; index < 6; index++) {
    short word;
    int dword;
    long long qword, truncated;
    __asm__("fldl %1; fistps %0" : "=m"(word) : "m"(outside[index]));
    __asm__("fldl %1; fistpl %0" : "=m"(dword) : "m"(outside[index]));
    __asm__("fldl %1; fistpll %0" : "=m"(qword) : "m"(outside[index]));
    __asm__("fldl %1; fisttpll %0" : "=m"(truncated) : "m"(outside[index]));
    int converted;
    __asm__("cvtsd2si %1, %0" : "=r"(converted) : "x"(outside[index]));
    printf("fist %g: %04hx %08x %016llx fisttp %016llx cvtsd2si %08x\n", outside[index], (unsigned short)word, (unsigned)dword,
           (unsigned long long)qword, (unsigned long long)truncated, (unsigned)converted);
  }
  unsigned short controls[] = {0x37f, 0x27f, 0x07f, 0xa7f};
  for (int index = 0; index < 4; index++) {
    long double third, one = 1.0L, three = 3.0L;
    unsigned short status;
    unsigned char bytes[10];
    __asm__ volatile("fldcw %2\n fnclex\n fldt %3\n fldt %4\n fdivrp\n fnstsw %1\n fstpt %0\n fninit"
                     : "=m"(third), "=m"(status) : "m"(controls[index]), "m"(one), "m"(three));
    memcpy(bytes, &third, 10);
    printf("control %04x: 1/3 ", controls[index]);
    for (int at = 9; at >= 0; at--) printf("%02x", bytes[at]);
    printf(" status %02x\n", status & 0x3f);
  }
  {
    uint64_t doubleBits = 0x7ff0000000000001ull;
    uint32_t singleBits = 0x7f800001;
    double d;
    float f;
    unsigned short status;
    long double loaded;
    memcpy(&d, &doubleBits, 8);
    memcpy(&f, &singleBits, 4);
    __asm__ volatile("fninit\n fldl %2\n fnstsw %1\n fstpt %0" : "=m"(loaded), "=m"(status) : "m"(d));
    printf("fld of a signaling NaN: status %02x", status & 0x3f);
    __asm__ volatile("fninit\n flds %2\n fnstsw %1\n fstpt %0" : "=m"(loaded), "=m"(status) : "m"(f));
    printf(", flds %02x\n", status & 0x3f);
  }
  unsigned char packed[10];
  double number = -1234567.0, back;
  __asm__("fldl %1; fbstp %0" : "=m"(packed) : "m"(number));
  printf("fbstp -1234567:");
  for (int index = 0; index < 10; index++) printf(" %02x", packed[index]);
  __asm__("fbld %1; fstpl %0" : "=m"(back) : "m"(packed));
  printf("\nfbld: %g\n", back);
  float estimates[] = {2.0f, 3.0f, 0.1f, 1e30f};
  for (int index = 0; index < 4; index++) {
    float x = estimates[index], r, q;
    __asm__("rcpss %1, %0" : "=x"(r) : "x"(x));
    __asm__("rsqrtss %1, %0" : "=x"(q) : "x"(x));
    printf("rcpss %g within: %d, rsqrtss within: %d\n", x, fabs(r * x - 1) <= 1.5 / 4096, fabs(q * sqrt(x) - 1) <= 1.5 / 4096);
  }
  return 0;
}
