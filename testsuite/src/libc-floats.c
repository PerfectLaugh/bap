/* Floating point, whose output has to be the same on the machine and in the emulator: exact bits, through the operations of
   SSE2, the conversions and what libc does with them. */
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static uint64_t bits(double x) { uint64_t u; memcpy(&u, &x, 8); return u; }
static uint32_t bits32(float x) { uint32_t u; memcpy(&u, &x, 4); return u; }

int main(void) {
  volatile double values[] = {0.0, -0.0, 1.0, -1.5, 0.1, 3.14159265358979, 1e308, -1e308, 1e-308, 5e-324,
                              2.2250738585072014e-308, INFINITY, -INFINITY, 1e15, 123456789.125, 0.3333333333333333};
  int n = sizeof values / sizeof *values;
  unsigned long sum = 0;
  for (int i = 0; i < n; i++) {
    double x = values[i];
    printf("%016lx %.17g %f %e\n", bits(x), x, x, x);
    printf(" sqrt %016lx floor %016lx ceil %016lx trunc %016lx\n", bits(sqrt(fabs(x))), bits(floor(x)), bits(ceil(x)), bits(trunc(x)));
    printf(" float %08x neg %016lx\n", bits32((float)x), bits(-x));
    if (fabs(x) < 1e18) printf(" long %ld int %d\n", (long)x, fabs(x) < 2e9 ? (int)x : 0);
    for (int j = 0; j < n; j++) {
      double y = values[j];
      float fx = (float)x, fy = (float)y;
      sum = sum * 31 + bits(x + y);
      sum = sum * 31 + bits(x - y);
      sum = sum * 31 + bits(x * y);
      if (!isnan(x / y)) sum = sum * 31 + bits(x / y);
      sum = sum * 31 + bits32(fx + fy) + bits32(fx * fy);
      sum = sum * 31 + (x < y) + 2 * (x <= y) + 4 * (x == y) + 8 * (x > y);
    }
  }
  printf("sum %016lx\n", sum);
  for (long i = -3; i < 4; i++) printf("%ld %016lx %08x\n", i, bits((double)(i * 1000000007L)), bits32((float)i / 3.0f));
  printf("%016lx %016lx\n", bits((double)(unsigned long)18446744073709551615UL), bits((double)9007199254740993L));
  double accumulated = 0;
  for (int i = 1; i < 2000; i++) accumulated += 1.0 / (i * i);
  printf("%.15f\n", accumulated);
  printf("%.3f %5.2f %g\n", 2.5, 3.14159, 1e100);
  return 0;
}
