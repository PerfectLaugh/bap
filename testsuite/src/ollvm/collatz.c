/* The program, whose functions Obfuscator-LLVM flattens, see build.sh.
   It prints 53, the number at the 100th step of the Collatz sequence of
   27, and 111, the number of its steps, as cff.c does, whose control flow
   is flattened by hand. */

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
    unsigned count = 0;
    while (n != 1) {
        if (n & 1)
            n = 3 * n + 1;
        else
            n = n / 2;
        count++;
        if (count == 100) print(n);
    }
    return count;
}

int main(void) {
    print(steps(27));
    return 0;
}
