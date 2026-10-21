/* the data in the section of the code, in the one segment, that is
   readable, writable, and executable, see rwx.ld */
#include "common.h"

__attribute__((section(".text.data"))) volatile int in_code = 5;

__attribute__((noinline)) int answer(void) { return in_code * 2; }

int main(void) {
    line("before", answer());
    in_code = in_code + 1;
    line("after", answer());
    return 0;
}

void _start(void) { exit(main()); }
