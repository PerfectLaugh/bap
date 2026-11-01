/* What the rounding modes do, printed so that a run can be compared with qemu. */
#include <fenv.h>
#include <stdio.h>
volatile double one = 1.0, three = 3.0, big = 1e308, tiny = 1e-300;
volatile float fone = 1.0f, fthree = 3.0f;
volatile double half = 2.5, neg = -2.5;
int main(void) {
  int modes[] = {FE_TONEAREST, FE_UPWARD, FE_DOWNWARD, FE_TOWARDZERO};
  for (int i = 0; i < 4; i++) {
    fesetround(modes[i]);
    volatile double a = one / three, b = big * 10, c = tiny * tiny, d = one + tiny, e = __builtin_sqrt(three);
    volatile float f = fone / fthree;
    volatile float g = (float)(one / three);
    volatile long h = (long)half;
    double r1, r2;
#ifdef __aarch64__
    
    __asm__("frinti %d0, %d1" : "=w"(r1) : "w"(half));
    __asm__("frintx %d0, %d1" : "=w"(r2) : "w"(neg));
#else
    r1 = __builtin_rint(half); r2 = __builtin_nearbyint(neg);
#endif
    /* The digits come from a table of constants far from the code, for a load with a large offset. */
    printf("%f\n", a * 3);
    printf("%d %a %a %a %a %a %a %a %ld %a %a %d\n", i, a, b, c, d, e, f, g, h, r1, r2, fegetround() == modes[i]);
  }
  return 0;
}
