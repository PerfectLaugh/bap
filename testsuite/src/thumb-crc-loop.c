/* Computes the CRC of ITERATIONS bytes and prints it with putchar, in the
   Thumb code. The binaries link the stand-in libc of stub-libc.c, since
   Primus runs the Lisp stubs instead of libc:

   T="--target=armv7a-linux-gnueabihf -fuse-ld=lld -nostdlib -O1 \
      -fno-builtin -fno-unwind-tables -fno-exceptions \
      -fno-asynchronous-unwind-tables"
   clang $T -marm -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c \
     -o libc.so.6
   clang $T -mthumb -fno-pie -no-pie \
     -Wl,--dynamic-linker=/lib/ld-linux-armhf.so.3 -DITERATIONS=100 \
     thumb-crc-loop.c libc.so.6 -o ../bin/arm-linux-gnueabihf-thumb-crc
   clang $T -mthumb -fno-pie -no-pie \
     -Wl,--dynamic-linker=/lib/ld-linux-armhf.so.3 -DITERATIONS=1000000 \
     thumb-crc-loop.c libc.so.6 -o ../bin/arm-linux-gnueabihf-thumb-crc-loop

   They print 1489580789 and 1635920155. */

int putchar(int);
int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

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

int main(int argc, char **argv, char **envp) {
    unsigned crc = 0xFFFFFFFF;
    for (unsigned i = 0; i < ITERATIONS; i++) {
        crc ^= i & 0xff;
        for (int j = 0; j < 8; j++)
            crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
    }
    print(~crc);
    return 0;
}

void _start(void) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
