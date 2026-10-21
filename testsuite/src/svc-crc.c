/* Computes the CRC of 100 bytes and prints it, 1489580789, with the write
   system call of Linux on AArch64. It links the stand-in libc of
   stub-libc.c, as thumb-crc-loop.c does:

   T="--target=aarch64-linux-gnu -fuse-ld=lld -nostdlib -O1 -fno-builtin \
      -fno-unwind-tables -fno-asynchronous-unwind-tables"
   clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c -o libc.so.6
   clang $T -fno-pie -no-pie -Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1 \
     -DITERATIONS=100 svc-crc.c libc.so.6 -o ../bin/aarch64-linux-gnu-svc-crc */

int __libc_start_main(int (*)(void), int, char **, void (*)(void),
                      void (*)(void), void (*)(void), void *);

static long sys_write(long fd, const char *buf, long len) {
    register long x0 __asm__("x0") = fd;
    register long x1 __asm__("x1") = (long)buf;
    register long x2 __asm__("x2") = len;
    register long x8 __asm__("x8") = 64;
    __asm__ volatile("svc #0" : "+r"(x0) : "r"(x1), "r"(x2), "r"(x8) : "memory");
    return x0;
}

int main(void) {
    unsigned crc = 0xFFFFFFFF;
    for (unsigned i = 0; i < ITERATIONS; i++) {
        crc ^= i & 0xff;
        for (int j = 0; j < 8; j++)
            crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
    }
    char buf[16];
    int n = sizeof(buf);
    buf[--n] = '\n';
    unsigned x = ~crc;
    do {
        buf[--n] = '0' + x % 10;
        x /= 10;
    } while (x);
    return sys_write(1, buf + n, sizeof(buf) - n) < 0;
}

void _start(void) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
