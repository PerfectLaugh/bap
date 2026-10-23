/* Prints the sum of the bytes, that malloc returns, which are any, the
   bits of the bytes, that calloc returns after it, in the same arena,
   which are zeros, the pointer, that calloc returns, whose size
   overflows, which is null, whether the chunks of malloc are aligned
   to 16 bytes, as of glibc, and whether realloc, which shrinks a
   chunk, keeps its bytes:

   gcc -O1 -fno-builtin calloc.c -o ../bin/x86_64-linux-gnu-calloc */

#include <stdio.h>
#include <stdlib.h>

int main(void) {
    unsigned char *p = malloc(64);
    unsigned s = 0;
    for (int i = 0; i < 64; i++) s += p[i];
    unsigned char *q = calloc(100, 1);
    unsigned z = 0;
    for (int i = 0; i < 100; i++) z |= q[i];
    volatile size_t n = (size_t)-1 / 2;
    printf("malloc %u calloc %u overflow %p\n", s, z, calloc(n, 4));
    unsigned misaligned = 0;
    for (int i = 1; i < 40; i++) misaligned |= (size_t)malloc(i) & 15;
    char *r = malloc(32);
    for (int i = 0; i < 32; i++) r[i] = i;
    r = realloc(r, 8);
    printf("misaligned %u realloc %d %d\n", misaligned, r[0], r[7]);
    return 0;
}
