/* the thread-local variables, which are initialized, and zeroed */
#include "common.h"

__thread int initialized = 0x77;
__thread int zeroed;
__thread char buffer[64];

int main(void) {
    line("initialized", initialized);
    line("zeroed", zeroed);
    zeroed = initialized + 1;
    buffer[63] = 9;
    line("written", zeroed + buffer[63]);
    return 0;
}

void _start(void) { exit(main()); }
