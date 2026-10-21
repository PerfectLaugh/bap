/* Maps an anonymous page, writes the code there, makes it executable
   with mprotect, runs it, and prints its result, 42, then unmaps the
   page and prints U, and reads from it, which is a segmentation fault,
   so X is never printed:

   gcc -O1 -fno-builtin mmap.c -o ../bin/x86_64-linux-gnu-mmap */

#include <stdio.h>
#include <sys/mman.h>

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

int main(void) {
    unsigned char *code = mmap(0, 4096, PROT_READ | PROT_WRITE,
                               MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (code == MAP_FAILED) return 1;
    /* mov eax, 42; ret */
    unsigned char insns[] = {0xb8, 42, 0, 0, 0, 0xc3};
    for (unsigned i = 0; i < sizeof(insns); i++) code[i] = insns[i];
    if (mprotect(code, 4096, PROT_READ | PROT_EXEC)) return 1;
    print(((int (*)(void))code)());
    if (munmap(code, 4096)) return 1;
    putchar('U');
    putchar('\n');
    putchar(code[0]);
    putchar('X');
    putchar('\n');
    return 0;
}
