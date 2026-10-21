/* The control flow of steps is flattened, as the obfuscators flatten it:
   its blocks, the steps of the Collatz sequence, go through the
   dispatcher, which switches on the state, that the blocks set, in a
   variable on the stack, as the code is compiled without optimization.
   It prints 111, the number of the steps of 27, and 1, as steps calls
   print, so that the flattened blocks have calls. */

#include <stdio.h>

static void print(unsigned x) {
    char buf[16];
    int n = 0;
    do {
        buf[n++] = '0' + x % 10;
        x /= 10;
    } while (x);
    while (n) putchar(buf[--n]);
    putchar('\n');
}

__attribute__((noinline)) unsigned steps(unsigned n) {
    unsigned state = 0x3a1f, count = 0;
    for (;;) {
        switch (state) {
        case 0x3a1f: count = 0; state = 0x91c4; break;
        case 0x91c4: state = n == 1 ? 0x5e02 : 0x77b0; break;
        case 0x77b0: state = (n & 1) ? 0x1d6e : 0xc823; break;
        case 0x1d6e: n = 3 * n + 1; state = 0x4b19; break;
        case 0xc823: n = n / 2; state = 0x4b19; break;
        case 0x4b19: count++; state = count == 100 ? 0x0e55 : 0x91c4; break;
        case 0x0e55: print(n); state = 0x91c4; break;
        case 0x5e02: return count;
        }
    }
}

int main(void) {
    print(steps(27));
    return 0;
}
