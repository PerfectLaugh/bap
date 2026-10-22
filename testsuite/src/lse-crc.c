/* Computes the CRC of ITERATIONS bytes, as thumb-crc-loop.c does, with
   the atomics of AArch64, the LSE ones of ARMv8.1, ldadd, ldeor, swp,
   and cas, and the exclusive pair, ldxr and stxr, and prints it with
   putchar, 1489580789. The default CPU of Unicorn lacks LSE. It links
   the stand-in libc of stub-libc.c:

   T="--target=aarch64-linux-gnu -fuse-ld=lld -nostdlib -O1 -fno-builtin \
      -fno-unwind-tables -fno-asynchronous-unwind-tables"
   clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c -o libc.so.6
   clang $T -march=armv8.1-a -fno-pie -no-pie \
     -Wl,--dynamic-linker=/lib/ld-linux-aarch64.so.1 -DITERATIONS=100 \
     lse-crc.c libc.so.6 -o ../bin/aarch64-linux-gnu-lse-crc */

int putchar(int);
int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

static unsigned crc = 0xFFFFFFFF;
static unsigned count;

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

/* the exclusive pair, retried until the store succeeds */
static void exclusive_shift(unsigned *p) {
    unsigned old, status;
    do {
        __asm__ volatile("ldxr %w0, [%2]\n"
                         "lsr %w0, %w0, #1\n"
                         "stxr %w1, %w0, [%2]"
                         : "=&r"(old), "=&r"(status)
                         : "r"(p)
                         : "memory");
    } while (status);
}

int main(int argc, char **argv, char **envp) {
    for (unsigned i = __atomic_fetch_add(&count, 0, __ATOMIC_SEQ_CST);
         i < ITERATIONS; i = __atomic_add_fetch(&count, 1, __ATOMIC_SEQ_CST)) {
        __atomic_fetch_xor(&crc, i & 0xff, __ATOMIC_SEQ_CST);
        for (int j = 0; j < 8; j++) {
            unsigned low = __atomic_load_n(&crc, __ATOMIC_RELAXED) & 1;
            exclusive_shift(&crc);
            unsigned expected = __atomic_load_n(&crc, __ATOMIC_RELAXED);
            while (!__atomic_compare_exchange_n(
                &crc, &expected, expected ^ (0xEDB88320 & -low), 0,
                __ATOMIC_SEQ_CST, __ATOMIC_SEQ_CST))
                ;
        }
    }
    print(~__atomic_exchange_n(&crc, 0, __ATOMIC_SEQ_CST));
    return 0;
}

void _start(void) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
