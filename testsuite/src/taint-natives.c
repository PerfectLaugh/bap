/* The copies of libc, whose taint emu/taint-natives/script.ml checks,
   which run natively, while the lifted engine propagates the taint, and
   as their Lisp stubs, else, with the same taint: of the copied bytes,
   of the byte of memset, and not of the terminator of strcpy:

   gcc -O1 -fno-builtin taint-natives.c -o ../bin/x86_64-linux-gnu-taint-natives */

#include <stdio.h>
#include <string.h>
volatile unsigned char src[64];
char dst[64], dst2[64], dst3[64], dst4[64];
__attribute__((noinline)) void mark(void *a, void *b, void *c, void *d) { __asm__ volatile("" ::"r"(a), "r"(b), "r"(c), "r"(d)); }
__attribute__((noinline)) void ready(void) { __asm__ volatile(""); }
int main(void) {
    for (int i = 0; i < 8; i++) src[i] = 'a' + i;
    src[8] = 0;
    ready();
    void *r1 = memcpy(dst, (void *)src, 16);
    memset(dst2, src[1], 8);
    strcpy(dst3, (char *)src);
    memmove(dst4, (void *)src, 4);
    mark(r1, dst2, dst3, dst4);
    printf("%s %d %zu\n", dst3, dst2[0], strlen(dst3));
    return 0;
}
