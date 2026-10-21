/* the data, that ends in the middle of a page, and the bss of several
   pages after it, in the same segment, whose memory is larger than its
   contents in the file */
#include "common.h"

char data[37] = "the data before the bss";
static char bss[3 * 4096 + 17];

int main(void) {
    unsigned long sum = 0;
    for (unsigned i = 0; i < sizeof(bss); i++) sum += bss[i];
    line("bss is zero", sum);
    bss[sizeof(bss) - 1] = 0x5a;
    line("bss end", bss[sizeof(bss) - 1]);
    line("data", data[4]);
    return 0;
}

void _start(void) { exit(main()); }
