/* Of what Bap.Analysis.Values finds of a program without running it: an array of the stack, which a store through an index of a
   mask makes all of one variable, and a scalar beside it; an array of the program written at an index, and one of constants
   read at one; and a scalar that all write and read. It is never run: _start doesn't end. Built as partition.c is, see
   BapTests/Values.lean. */

volatile long sink;

long table[8];

const long weights[4] = {3, 1, 4, 1};

__attribute__((noinline)) long locals(long n) {
  volatile long buf[4];
  volatile long last;
  buf[0] = n;
  buf[1] = n + 1;
  buf[2] = n + 2;
  buf[3] = n + 3;
  last = n * 7;
  return buf[n & 3] + last;
}

__attribute__((noinline)) long globals(long i) {
  table[i & 7] = sink;
  return table[3] + weights[i & 3];
}

void _start(void) {
  long total = 0;
  for (long i = 0; i < 10; i++) total += locals(i) + globals(i);
  sink = total;
  for (;;) {
  }
}
