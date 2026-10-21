/* the code, the constants, and the data in the same page, see packed.ld,
   which have different permissions */
#include "common.h"

static const char text[] = "constant";
int counter = 41;

__attribute__((noinline)) int bump(void) { return ++counter; }

int main(void) {
    line("counter", bump());
    line("constant", text[0]);
    return 0;
}

void _start(void) { exit(main()); }
