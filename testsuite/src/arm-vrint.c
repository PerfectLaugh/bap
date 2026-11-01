/* The VRINT instructions of ARMv8 under each of the rounding modes, printed so that a run can be compared with qemu. */
#include <fenv.h>
#include <stdio.h>
volatile double h = 2.5, n = -2.5, g = 3.5; volatile float fh = 2.5f, fn = -3.5f;
#define D(op, x) ({ double r; __asm__ volatile(op ".f64 %P0, %P1" : "=w"(r) : "w"(x)); r; })
#define S(op, x) ({ float r; __asm__ volatile(op ".f32 %0, %1" : "=t"(r) : "t"(x)); r; })
int main(void) {
  int modes[] = {FE_TONEAREST, FE_UPWARD, FE_DOWNWARD, FE_TOWARDZERO};
  for (int i = 0; i < 4; i++) {
    fesetround(modes[i]);
    printf("%d %a %a %a %a %a %a %a\n", i, D("vrintx", h), D("vrintr", n), D("vrintz", g), D("vrinta", h), D("vrintn", h), D("vrintp", h), D("vrintm", h));
    printf("%d %a %a %a %a %a %a %a\n", i, S("vrintx", fh), S("vrintr", fn), S("vrintz", fn), S("vrinta", fh), S("vrintn", fh), S("vrintp", fh), S("vrintm", fh));
  }
  return 0;
}
