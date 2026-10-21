/* Computes the CRC of a million bytes and prints it, 1635920155, with
   putchar. It takes hours in the interpreter of Primus and a fraction
   of a second in Unicorn. */

#include <stdio.h>

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

int main(void) {
    unsigned crc = 0xFFFFFFFF;
    for (unsigned i = 0; i < 1000000; i++) {
        crc ^= i & 0xff;
        for (int j = 0; j < 8; j++)
            crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
    }
    print(~crc);
    return 0;
}
