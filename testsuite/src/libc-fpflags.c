// What MXCSR says of results at the ends of float: overflow of the result in its own rounding mode, and underflow of what is tiny after
// rounding, as x86 tells it.
#include <unistd.h>

static void say(const char *label, unsigned flags) {
  char line[64];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  const char *names = "IDZOUP";
  line[n++] = ' ';
  for (int bit = 0; bit < 6; bit++) line[n++] = flags & (1u << bit) ? names[bit] : '.';
  line[n++] = '\n';
  write(1, line, n);
}

static unsigned run(unsigned rounding, float (*op)(float, float), float a, float b) {
  unsigned csr = 0x1f80 | (rounding << 13);
  __asm__ volatile("ldmxcsr %0" : : "m"(csr));
  volatile float r = op(a, b);
  (void)r;
  unsigned out;
  __asm__ volatile("stmxcsr %0" : "=m"(out));
  return out & 0x3f;
}

static float add(float a, float b) { volatile float x = a, y = b; return x + y; }
static float mul(float a, float b) { volatile float x = a, y = b; return x * y; }

int main(void) {
  float max = 0x1.fffffep127f;
  // Past the largest by a quarter of its last place: to nearest it is the largest, and up it overflows.
  say("max+q rne", run(0, add, max, 0x1p102f));
  say("max+q up", run(2, add, max, 0x1p102f));
  say("max+q zero", run(3, add, max, 0x1p102f));
  // Past it by nearly a place, which is past 2^128: it overflows whichever way it rounds.
  say("max*e rne", run(0, mul, max, 0x1.000002p0f));
  say("max*e zero", run(3, mul, max, 0x1.000002p0f));
  say("max*e down", run(1, mul, max, 0x1.000002p0f));
  // Just below the smallest normal, which rounding to nearest makes it: not tiny after rounding.
  say("tiny rne", run(0, mul, 0x1.000002p-126f, 0x1.fffffcp-1f));
  say("tiny zero", run(3, mul, 0x1.000002p-126f, 0x1.fffffcp-1f));
  // Of a subnormal result that isn't exact.
  say("sub", run(0, mul, 0x1p-130f, 0x1.000002p-1f));
  return 0;
}
