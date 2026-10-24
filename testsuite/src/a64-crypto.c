/* Runs the cryptographic, CRC32, and saturating instructions of AArch64
   in loops, so that the lifted engine compiles them, and prints their
   checksum, which is the same in Unicorn, see emu/a64-crypto. It links
   the stand-in libc of stub-libc.c, as threads.c does:

   T="--target=aarch64-linux-gnu -fuse-ld=lld -nostdlib -O1 -fno-builtin \
      -march=armv8.2-a+crypto+crc+rdm -mno-outline-atomics"
   clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c -o libc.so.6
   clang $T -fno-pie -no-pie -Wl,-e,_start \
     -Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1 a64-crypto.c libc.so.6 \
     -o ../bin/aarch64-linux-gnu-a64-crypto */

#include <arm_acle.h>
#include <arm_neon.h>

int putchar(int);
int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

static void hex(unsigned long x) {
    for (int i = 60; i >= 0; i -= 4) putchar("0123456789abcdef"[(x >> i) & 15]);
    putchar('\n');
}

int main(void) {
    uint8x16_t s = vdupq_n_u8(0x42), k = vdupq_n_u8(0x17);
    uint32x4_t h = vdupq_n_u32(0x6a09e667), w = vdupq_n_u32(0x428a2f98);
    uint32_t crc = 0xffffffff;
    poly64_t p = 0x87;
    int16x8_t q = vdupq_n_s16(0x1234);
    for (int i = 0; i < 2000; i++) {
        s = vaesmcq_u8(vaeseq_u8(s, k));
        s = vaesimcq_u8(vaesdq_u8(s, vreinterpretq_u8_u32(h)));
        h = vsha256hq_u32(h, w, vreinterpretq_u32_u8(s));
        w = vsha1cq_u32(w, (uint32_t)i, h);
        crc = __crc32d(crc, vgetq_lane_u64(vreinterpretq_u64_u8(s), 0));
        crc = __crc32cb(crc, (uint8_t)i);
        p = (poly64_t)vgetq_lane_u64(vreinterpretq_u64_p128(vmull_p64(p, 0x1b + i)), 0);
        q = vqrdmulhq_s16(q, vdupq_n_s16((int16_t)(i * 37)));
        q = vqrshlq_s16(q, vdupq_n_s16((int16_t)(i % 9 - 4)));
        q = vaddq_s16(q, vdupq_n_s16(0x111));
    }
    hex(vgetq_lane_u64(vreinterpretq_u64_u8(s), 0) ^ vgetq_lane_u64(vreinterpretq_u64_u8(s), 1));
    hex(vgetq_lane_u64(vreinterpretq_u64_u32(h), 0) ^ vgetq_lane_u64(vreinterpretq_u64_u32(w), 1));
    hex(crc);
    hex((unsigned long)p);
    hex(vgetq_lane_u64(vreinterpretq_u64_s16(q), 0));
    return 0;
}

void _start(void) { __libc_start_main((int (*)(int, char **, char **))main, 0, 0, 0, 0, 0, 0); }
