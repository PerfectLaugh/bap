/* Prints the sum of the bytes, that malloc returns, which are any, the
   bits of the bytes, that calloc returns after it, in the same arena,
   which are zeros, and the pointer, that calloc returns, whose size
   overflows, which is null:

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
    return 0;
}
