/* Runs the code that it writes, after it makes it executable with
   mprotect, and prints its result, 42, then makes the code read-only and
   prints W, and writes to it, which is a segmentation fault, so X is
   never printed:

   gcc -O1 -fno-builtin mprotect.c -o ../bin/x86_64-linux-gnu-mprotect */

#include <stdio.h>
#include <sys/mman.h>

static unsigned char code[4096] __attribute__((aligned(4096)));

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

int main(int argc, char **argv) {
    /* mov eax, 42; ret */
    unsigned char insns[] = {0xb8, 42, 0, 0, 0, 0xc3};
    for (unsigned i = 0; i < sizeof(insns); i++) code[i] = insns[i];
    if (mprotect(code, sizeof(code), PROT_READ | PROT_EXEC)) return 1;
    print(((int (*)(void))code)());
    if (mprotect(code, sizeof(code), PROT_READ)) return 1;
    putchar('W');
    putchar('\n');
    code[0] = 0;
    putchar('X');
    putchar('\n');
    return 0;
}
