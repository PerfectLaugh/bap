/* Runs the code of the program, that patches the instruction after it,
   in the same basic block, in a loop, as smc.c does with the code, that
   it writes to its data, so that the block of the program, that the
   interpreter runs, changes, while it runs, and prints the sum, that the
   code computes, and the sum, that C computes, which are the same,
   unless the instruction runs as it was:

   gcc -O1 -fno-builtin -no-pie smc-text.c -o ../bin/x86_64-linux-gnu-smc-text */

#include <stdio.h>
#include <sys/mman.h>

/* unsigned f(unsigned n), whose bytes are the same, when the loop
   starts again, as it restores the immediate, that it patched */
unsigned f(unsigned n);
__asm__(".text\n"
        ".globl f\n"
        ".type f, @function\n"
        ".p2align 12\n"
        "f:\n"
        "    xor %edx, %edx\n"
        "1:  mov %edi, %eax\n"
        "    movb %al, 2f+1(%rip)\n"
        "2:  mov $0, %ecx\n"
        "    movb $0, 2b+1(%rip)\n"
        "    add %ecx, %edx\n"
        "    dec %edi\n"
        "    jnz 1b\n"
        "    mov %edx, %eax\n"
        "    ret\n"
        ".size f, .-f\n");

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
    if (mprotect((void *)f, 4096, PROT_READ | PROT_WRITE | PROT_EXEC))
        return 1;
    unsigned n = 2000, expected = 0;
    for (unsigned i = 1; i <= n; i++) expected += i & 0xff;
    putchar('s');
    putchar(' ');
    print(f(n));
    putchar(' ');
    print(expected);
    putchar('\n');
    return 0;
}
