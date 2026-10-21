/* the entry point is after the other functions, in a section of its
   own, see entry.ld */
#include "common.h"

__attribute__((noinline)) int helper(int x) { return x * 3; }

int main(void) {
    line("entry", helper(14));
    return 0;
}

__attribute__((section(".text.zstart"))) void _start(void) { exit(main()); }
