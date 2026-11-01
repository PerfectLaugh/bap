/* What the controls of denormals and NaNs do, printed so that a run can be compared with qemu or the machine. */
#include <fenv.h>
#include <stdio.h>
#include <string.h>
static const unsigned long long values[] = {0x3ff0000000000000ull, 0x0000000000000001ull, 0x8000000000000001ull, 0x000fffffffffffffull, 0x0010000000000000ull, 0x7ff8000000000123ull, 0x7ff0000000000123ull, 0, 0x7ff0000000000000ull, 0x2000000000000000ull};
enum { COUNT = sizeof values / sizeof values[0] };
static double of(unsigned long long b) { double v; memcpy(&v, &b, 8); return v; }
static unsigned long long bits(double v) { unsigned long long b; memcpy(&b, &v, 8); return b; }
static unsigned long hash;
static void add(unsigned long long v) { hash = hash * 31 + (unsigned)v + (unsigned)(v >> 32) * 7; }
#if defined(__aarch64__)
static void control(unsigned on) { unsigned long v; __asm__ volatile("mrs %0, fpcr" : "=r"(v)); v = (v & ~(3ul << 24)) | ((unsigned long)on << 24); __asm__ volatile("msr fpcr, %0" :: "r"(v)); }
static unsigned status(void) { unsigned long v; __asm__ volatile("mrs %0, fpsr" : "=r"(v)); __asm__ volatile("msr fpsr, xzr"); return (unsigned)v; }
#elif defined(__arm__)
static void control(unsigned on) { unsigned v; __asm__ volatile("vmrs %0, fpscr" : "=r"(v)); v = (v & ~(3u << 24)) | (on << 24); __asm__ volatile("vmsr fpscr, %0" :: "r"(v)); }
static unsigned status(void) { unsigned v, c; __asm__ volatile("vmrs %0, fpscr" : "=r"(v)); c = v & ~0x9fu; __asm__ volatile("vmsr fpscr, %0" :: "r"(c)); return v & 0x9f; }
#else
static void control(unsigned on) { unsigned v; __asm__ volatile("stmxcsr %0" : "=m"(v)); v &= ~((1u << 15) | (1u << 6)); if (on & 1) v |= 1u << 15 | 1u << 6; __asm__ volatile("ldmxcsr %0" :: "m"(v)); }
static unsigned status(void) { unsigned v, c; __asm__ volatile("stmxcsr %0" : "=m"(v)); c = v & ~0x3fu; __asm__ volatile("ldmxcsr %0" :: "m"(c)); return v & 0x3f; }
#endif
int main(void) {
  for (unsigned on = 0; on < 4; on++) {
    control(on); status();
    for (int i = 0; i < COUNT; i++) for (int j = 0; j < COUNT; j++) {
      volatile double a = of(values[i]), b = of(values[j]), r;
      r = a + b; add(bits(r)); add(status());
      r = a - b; add(bits(r)); add(status());
      r = a * b; add(bits(r)); add(status());
      r = a / b; add(bits(r)); add(status());
      volatile int lt = a < b; add(lt); add(status());
    }
    printf("binary %u %lx\n", on, hash);
    for (int i = 0; i < COUNT; i++) {
      volatile double a = of(values[i]), r; volatile float f; volatile int n;
      r = __builtin_sqrt(a); add(bits(r)); add(status());
      f = (float)a; { unsigned u; float g = f; memcpy(&u, &g, 4); add(u); } add(status());
      r = (double)f; add(bits(r)); add(status());
      n = (int)a; add(n); add(status());
    }
    printf("unary %u %lx\n", on, hash);
  }
  return 0;
}
