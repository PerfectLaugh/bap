// What musl's libm of i686 gives, which is of x87: atan2 of FPATAN, log of FYL2X, exp and exp2 of F2XM1 and FSCALE, fmod of FPREM,
// remainder of FPREM1, ldexp of FSCALE, and the long doubles of the same (testLinuxRaises).
#include <math.h>
#include <stdio.h>

int main(void) {
  volatile double values[] = {0.5, 1.5, 10.0, 123.456};
  for (int index = 0; index < 4; index++) {
    double x = values[index];
    printf("%g: atan2 %.15g log %.15g log2 %.15g log10 %.15g exp %.15g exp2 %.15g fmod %.15g remainder %.15g ldexp %.15g\n", x,
           atan2(x, 0.75), log(x), log2(x), log10(x), exp(x), exp2(x), fmod(x * 7, 1.3), remainder(x * 7, 1.3), ldexp(x, 9));
    long double y = x;
    printf("  long: expl %.15Lg logl %.15Lg atan2l %.15Lg fmodl %.15Lg\n", expl(y), logl(y), atan2l(y, 3.0L), fmodl(y * 11, 0.7L));
  }
  return 0;
}
