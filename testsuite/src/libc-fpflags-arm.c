// What FPSR says of results at the ends of float: overflow of the result in its own rounding mode, and underflow of what is tiny
// before rounding, as Arm tells it.
#include <unistd.h>

static void say(const char *label, unsigned long flags) {
  char line[64];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  const char *names = "IZOUP";
  line[n++] = ' ';
  for (int bit = 0; bit < 5; bit++) line[n++] = flags & (1ul << bit) ? names[bit] : '.';
  line[n++] = '\n';
  write(1, line, n);
}

static unsigned long run(unsigned long rounding, float (*op)(float, float), float a, float b) {
  unsigned long fpcr = rounding << 22, zero = 0;
  __asm__ volatile("msr fpcr, %0\n msr fpsr, %1" : : "r"(fpcr), "r"(zero));
  volatile float r = op(a, b);
  (void)r;
  unsigned long out;
  __asm__ volatile("mrs %0, fpsr" : "=r"(out));
  return out & 0x1f;
}

static float add(float a, float b) { volatile float x = a, y = b; return x + y; }
static float mul(float a, float b) { volatile float x = a, y = b; return x * y; }

int main(void) {
  float max = 0x1.fffffep127f;
  say("max+q rne", run(0, add, max, 0x1p102f));
  say("max+q up", run(1, add, max, 0x1p102f));
  say("max+q zero", run(3, add, max, 0x1p102f));
  say("max*e zero", run(3, mul, max, 0x1.000002p0f));
  // Just below the smallest normal, which rounding to nearest makes it: tiny before rounding, as Arm tells it.
  say("tiny rne", run(0, mul, 0x1.000002p-126f, 0x1.fffffcp-1f));
  say("sub", run(0, mul, 0x1p-130f, 0x1.000002p-1f));
  return 0;
}
