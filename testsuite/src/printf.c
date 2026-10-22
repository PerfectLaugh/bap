/* Prints the conversions of printf, with more arguments, than the
   registers pass, to stdout, and one line to stderr, formats strings
   with sprintf and snprintf, and exits with 3, so that the stubs of the
   printf family, the streams, and the exit code are tested:

   gcc -O0 -fno-builtin -no-pie printf.c -o ../bin/x86_64-linux-gnu-printf

   which refers to stdout with a copy relocation, and the fortified one,
   which calls __printf_chk, and refers to stdout through the GOT:

   gcc -O2 -D_FORTIFY_SOURCE=2 -fPIC -pie printf.c \
       -o ../bin/x86_64-linux-gnu-printf-chk */

#include <stdio.h>

int main(void) {
    char buf[64], small[8];
    printf("int %d neg %d unsigned %u hex %x HEX %#X oct %o\n", 42, -7,
           3000000000u, 255, 255, 8);
    printf("long %ld %lu %lx char %c str [%s] [%5s] [%-5s|] [%.2s]\n",
           -1234567890123L, 18446744073709551615UL, 0xdeadbeefcafeL, 'Z',
           "hi", "ab", "ab", "abcdef");
    printf("pad [%5d] [%-5d|] [%05d] [%+d] [% d] [%.3d] [%*d] %%\n", 12, 12,
           -12, 5, 5, 7, 4, 9);
    printf("stack %d %d %d %d %d %d %d %d\n", 1, 2, 3, 4, 5, 6, 7, 8);
    printf("ptr %p null %p %s\n", (void *)0x1234, (void *)0, (char *)0);
    fprintf(stderr, "err %d\n", 99);
    int n = sprintf(buf, "s%dx%s", 10, "yz");
    int m = snprintf(small, sizeof(small), "%s", "truncated-string");
    printf("sprintf [%s] %d snprintf [%s] %d\n", buf, n, small, m);
    return 3;
}
