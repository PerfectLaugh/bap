/* Checks the rules of Linux for the pages: prints the page size, 4096,
   the results and the errno of the calls with the arguments that are
   not aligned to the pages, which are -1 and EINVAL (22), and of a
   mapping of a file, which Primus does not map, -1 and ENODEV (19),
   instead of EBADF (9) on Linux, and protects the whole page of 10
   bytes, so the store after W is a segmentation fault:

   gcc -O1 -fno-builtin pages.c -o ../bin/x86_64-linux-gnu-pages */

#include <errno.h>
#include <stdio.h>
#include <sys/mman.h>
#include <unistd.h>

static void print(long x) {
    char buf[24];
    int n = 0;
    if (x < 0) {
        putchar('-');
        x = -x;
    }
    do {
        buf[n++] = '0' + x % 10;
        x /= 10;
    } while (x);
    while (n) putchar(buf[--n]);
    putchar('\n');
}

static void result(long r) {
    print(r);
    print(r < 0 ? errno : 0);
}

int main(void) {
    print(getpagesize());
    char *p = mmap(0, 100, PROT_READ | PROT_WRITE,
                   MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    print(p == MAP_FAILED);
    result(mprotect(p + 1, 10, PROT_READ));                /* EINVAL */
    result(munmap(p, 0));                                  /* EINVAL */
    result((long)mmap(p + 1, 10, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0)); /* EINVAL */
    result((long)mmap(0, 10, PROT_READ, MAP_PRIVATE, 3, 0)); /* a file */
    result(mprotect(p, 10, PROT_READ));                    /* the whole page */
    putchar('W');
    putchar('\n');
    p[4000] = 1;
    putchar('X');
    putchar('\n');
    return 0;
}
