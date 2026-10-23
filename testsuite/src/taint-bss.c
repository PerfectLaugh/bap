/* The CRC of a million bytes, that aren't tainted, which runs in the
   engine, as the observers of the taint see the tainted values only,
   and the CRC of the bytes of buf, and the number of its odd bytes,
   whose page is tainted, see emu/taint-bss/script.ml, whose zeros are
   generated, when they are read first, which keeps them tainted:

   gcc -O1 -fno-inline taint-bss.c -o ../bin/x86_64-linux-gnu-taint-bss */

#include <stdio.h>

volatile unsigned char buf[256];

static unsigned step(unsigned crc, unsigned char b) {
    crc ^= b;
    for (int j = 0; j < 8; j++) crc = (crc >> 1) ^ (0xEDB88320 & -(crc & 1));
    return crc;
}

int main(void) {
    unsigned crc = 0xFFFFFFFF, t = 0xFFFFFFFF, n = 0;
    for (unsigned i = 0; i < 1000000; i++) crc = step(crc, i & 0xff);
    for (int i = 0; i < 256; i++) t = step(t, buf[i]);
    for (int i = 0; i < 256; i++)
        if (buf[i] & 1) n++;
    printf("%u %u %u\n", ~crc, ~t, n);
    return 0;
}
