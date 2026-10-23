/* The operations, through which the taint of in propagates, or not, to
   out, and to the arguments of mark, which emu/taint-ops/script.ml
   checks, in the interpreter and in the lifted engine, which propagates
   the taint itself, by the policy of the computations, or of the moves:

   gcc -O1 -fno-inline -fno-builtin taint-ops.c -o ../bin/x86_64-linux-gnu-taint-ops */

#include <stdio.h>

volatile unsigned char in[16];
unsigned char out[64];

__attribute__((noinline)) void mark(long moved, long computed, long clean,
                                    long branched) {
    __asm__ volatile("" ::"r"(moved), "r"(computed), "r"(clean),
                     "r"(branched));
}

__attribute__((noinline)) void copy(unsigned char *dst,
                                    volatile unsigned char *src, int n) {
    for (int i = 0; i < n; i++) dst[i] = src[i];
}

int main(void) {
    out[0] = in[0];
    out[1] = in[1] + 3;
    out[2] = 5;
    unsigned short h = in[2] | (in[3] << 8);
    out[4] = h;
    out[5] = h >> 8;
    long x = in[4];
    x <<= 8;
    for (int i = 0; i < 8; i++) out[8 + i] = x >> (8 * i);
    copy(out + 16, in + 8, 8);
    out[24] = out[16] ^ out[17];
    out[25] = out[24] - out[24];
    unsigned y = in[5] > 3 ? 10 : 20;
    out[26] = y;
    out[27] = in[6];
    out[27] = 9;
    mark(in[7], in[7] * 2 + 1, 7, y);
    printf("%d\n", out[0] + out[1] + out[24] + out[26]);
    return 0;
}
