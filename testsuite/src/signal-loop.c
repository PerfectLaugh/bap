/* Copies two buffers to each other in a loop of stores, without calls,
   which runs long in Unicorn, so that the signals stop it, as a store
   is in progress, see the emu/signal cases, and prints the weighted sum
   of the bytes, 1080774656. It links the stand-in libc of stub-libc.c:

   T="--target=x86_64-linux-gnu -fuse-ld=lld -nostdlib -O1 -fno-builtin \
      -fno-unwind-tables -fno-asynchronous-unwind-tables"
   clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c -o libc.so.6
   clang $T -fno-pie -no-pie \
     -Wl,--dynamic-linker=/lib64/ld-linux-x86-64.so.2 \
     signal-loop.c libc.so.6 -o ../bin/x86_64-linux-gnu-signal-loop */

int putchar(int);
int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

static unsigned char a[4096], b[4096];

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
    for (int i = 0; i < 4096; i++) a[i] = i;
    /* the counters are in the memory, so the stores of each step are
       repeated, if they run again */
    for (volatile int round = 0; round < 1000; round++) {
        for (volatile int i = 0; i < 4096; i++) b[i] = a[i] + 1;
        for (volatile int i = 0; i < 4096; i++) a[i] = b[i];
    }
    /* weighted, so that it depends on each step of each round */
    unsigned sum = 0;
    for (int i = 0; i < 4096; i++) sum += a[i] * (i + 1);
    print(sum);
    return 0;
}

void _start(void) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
