/* A switch in a loop, whose table, of code of PIE, is of offsets from a base that a register holds from before the loop: what
   Bap.Analysis.Partition doesn't go back over, which Bap.Analysis.Values knows. It is never run: _start doesn't end. Built
   freestanding as partition.c is, but with -fPIE, see BapTests/Values.lean. */

volatile int sink;

__attribute__((noinline)) int hoisted(const unsigned char *s, int n) {
  int total = 0;
  for (int i = 0; i < n; i++) {
    switch (s[i]) {
    case 'a': total += sink; break;
    case 'b': total ^= 3 * sink; break;
    case 'c': total -= sink; break;
    case 'd': total |= sink << 2; break;
    case 'e': total &= sink + 7; break;
    case 'f': total += 1000; break;
    case 'g': total *= sink; break;
    case 'h': total = sink % 7; break;
    default: total--; break;
    }
  }
  return total;
}

void _start(void) {
  static const unsigned char text[] = "abcdefgh";
  sink = hoisted(text, sizeof text - 1);
  for (;;) {
  }
}
