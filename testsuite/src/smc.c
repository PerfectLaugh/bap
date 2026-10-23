/* Runs the code, that patches the instruction after it, in the same
   block, in a loop, and prints the sum, that the code computes, and the
   sum, that C computes, which are the same, unless the instruction runs
   as it was, e.g., as the JIT of the lifted engine compiled it:

   gcc -O1 -fno-builtin smc.c -o ../bin/x86_64-linux-gnu-smc */

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
}

int main(void) {
    /* unsigned f(unsigned n, unsigned char *self), self is the code,
       whose bytes are the same, when the loop starts again, as it
       restores the instruction, that it patched:
          xor edx, edx
       L: mov eax, edi
          mov [rsi + 8], al      ; the immediate of the next mov
          mov ecx, 0
          mov byte [rsi + 8], 0  ; restores it
          add edx, ecx
          dec edi
          jnz L
          mov eax, edx
          ret */
    unsigned char insns[] = {0x31, 0xd2, 0x89, 0xf8, 0x88, 0x46, 0x08,
                             0xb9, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x46,
                             0x08, 0x00, 0x01, 0xca, 0xff, 0xcf, 0x75,
                             0xec, 0x89, 0xd0, 0xc3};
    for (unsigned i = 0; i < sizeof(insns); i++) code[i] = insns[i];
    if (mprotect(code, sizeof(code), PROT_READ | PROT_WRITE | PROT_EXEC))
        return 1;
    unsigned n = 2000, expected = 0;
    for (unsigned i = 1; i <= n; i++) expected += i & 0xff;
    unsigned (*f)(unsigned, unsigned char *) =
        (unsigned (*)(unsigned, unsigned char *))code;
    putchar('s');
    putchar(' ');
    print(f(n, code));
    putchar(' ');
    print(expected);
    putchar('\n');
    return 0;
}
