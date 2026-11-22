/* Of what Bap.Analysis.Frame finds of functions that do nothing with their arguments but move them: one that stores its argument
   to what isn't its stack, one that returns it, as it is in the result register or copied there, one that passes them on to
   what it calls, in its tail too, one that spills them to its stack and loads them again, as code that isn't optimized does,
   and one that calls through a pointer. `ident` and `second` are weak, so that the compiler doesn't take their callers to
   know what they return, which then wouldn't read it. It is never run: _start doesn't end. Built as frame.c is, see
   BapTests/Frame.lean, as ../bin/ARCH-linux-none-frame2. */

volatile long sink;

__attribute__((noinline)) void none(void) { sink = 1; }

__attribute__((noinline)) long three(long a, long b, long c) { return (a + sink) * (b - sink) + c; }

__attribute__((noinline)) void novalue(long a) { sink = a; }

__attribute__((noinline)) void setter(long *p, long v) { *p = v; }

__attribute__((noinline, weak)) long ident(long a) { return a; }

__attribute__((noinline, weak)) long second(long a, long b) { return b; }

__attribute__((noinline)) long through(long a, long b, long c) { return three(a, b, c) + 1; }

__attribute__((noinline)) long forward(long a, long b, long c) { return three(a, b, c); }

__attribute__((noinline, optnone)) long spilled(long a, long b) { return a + b * sink; }

__attribute__((noinline)) long apply(long (*f)(long), long a) { return f(a) + sink; }

__attribute__((noinline)) void calls(void) {
  none();
  sink = 2;
}

void _start(void) {
  long total = 0, v = 0;
  for (long i = 0; i < 10; i++) {
    none();
    calls();
    novalue(i);
    setter(&v, i);
    total += v + ident(i) + second(1, i) + through(i, 2, 3) + forward(i, 1, 2) + spilled(i, total) + apply(ident, i);
  }
  sink = total;
  for (;;) {
  }
}
