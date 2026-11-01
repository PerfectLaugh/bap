/* What each operation raises, on what its edges are, printed so that a run can be compared with qemu. */
#include <fenv.h>
#include <math.h>
#include <stdio.h>
#include <string.h>
static const unsigned long long values[] = {
  0x3ff0000000000000ull, 0x4008000000000000ull, 0xbff0000000000000ull, 0, 0x8000000000000000ull, 0x7ff0000000000000ull,
  0xfff0000000000000ull, 0x7ff8000000000000ull, 0x7ff0000000000001ull, 0x7fefffffffffffffull, 0x0010000000000000ull,
  0x0000000000000001ull, 0x3ca0000000000000ull, 0x41f0000000000000ull, 0x47efffffe0000000ull };
enum { COUNT = sizeof values / sizeof values[0] };
static double of(unsigned long long bits) { double value; memcpy(&value, &bits, 8); return value; }
static unsigned long hash;
static void show(const char *name, int flags) { (void)name;
  hash = hash * 31 + ((flags & FE_INVALID) != 0) + 2 * ((flags & FE_DIVBYZERO) != 0) + 4 * ((flags & FE_OVERFLOW) != 0) +
    8 * ((flags & FE_UNDERFLOW) != 0) + 16 * ((flags & FE_INEXACT) != 0); }
#define RAISED() fetestexcept(FE_ALL_EXCEPT)
int main(void) {
  const char *name = "";
  for (int i = 0; i < COUNT; i++) for (int j = 0; j < COUNT; j++) {
    volatile double a = of(values[i]), b = of(values[j]), r;
    feclearexcept(FE_ALL_EXCEPT); r = a + b; show(name, RAISED());
    feclearexcept(FE_ALL_EXCEPT); r = a - b; show(name, RAISED());
    feclearexcept(FE_ALL_EXCEPT); r = a * b; show(name, RAISED());
    feclearexcept(FE_ALL_EXCEPT); r = a / b; show(name, RAISED());
    (void)r;
  }
  printf("binary %lx\n", hash);
  for (int i = 0; i < COUNT; i++) {
    volatile double a = of(values[i]), r; volatile float f; volatile int n; volatile long l;
    feclearexcept(FE_ALL_EXCEPT); r = __builtin_sqrt(a); show(name, RAISED()); (void)r;
    feclearexcept(FE_ALL_EXCEPT); f = (float)a; show(name, RAISED()); (void)f;
    feclearexcept(FE_ALL_EXCEPT); n = (int)a; show(name, RAISED()); (void)n;
    feclearexcept(FE_ALL_EXCEPT); l = (long)a; show(name, RAISED()); (void)l;
  }
  printf("unary %lx\n", hash);
  return 0;
}
