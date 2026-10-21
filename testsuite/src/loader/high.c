/* the image at the top of the address space, see high.ld */
#include "common.h"

int value = 0x1234;
static int zeroes[1024];

int main(void) {
    zeroes[1023] = value;
    line("high", zeroes[1023] + zeroes[0]);
    line("address", (unsigned long)&value >> 20);
    return 0;
}

void _start(void) { exit(main()); }
