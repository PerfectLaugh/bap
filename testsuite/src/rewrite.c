/* Runs the code that it writes to its buffer at 0x405000, mov $42, %eax,
   which memcpy writes, then rewrites the code, that ran, to mov $7, %eax,
   with memcpy, and to mov $9, %eax, with its own store, and runs it after
   each of them, so the calls return 42, 7, and 9, and it exits with 7, if
   all of them did. It prints nothing, so that the scripts see the results
   in the registers:

   gcc -O1 -fno-builtin -no-pie rewrite.c -o ../bin/x86_64-linux-gnu-rewrite */

#include <string.h>
#include <sys/mman.h>

static unsigned char code[4096] __attribute__((aligned(4096)));

int main(void) {
    unsigned char a[] = {0xb8, 42, 0, 0, 0, 0xc3}; /* mov $42, %eax; ret */
    unsigned char b[] = {0xb8, 7, 0, 0, 0, 0xc3};  /* mov $7, %eax; ret */
    int (*f)(void) = (int (*)(void))code;
    if (mprotect(code, sizeof(code), PROT_READ | PROT_WRITE | PROT_EXEC))
        return 1;
    memcpy(code, a, sizeof(a));
    int r1 = f();
    memcpy(code, b, sizeof(b));
    int r2 = f();
    code[1] = 9;
    int r3 = f();
    return (r1 == 42) + 2 * (r2 == 7) + 4 * (r3 == 9);
}
