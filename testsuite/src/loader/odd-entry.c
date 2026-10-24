/* the entry point is at an odd address, after a function of one byte,
   whose subroutine is not the entry point, as the entry is odd for the
   Thumb state of ARM only, see Bap_project */
#include "common.h"

__attribute__((noinline)) int helper(int x) { return x * 3; }

int main(void) {
    line("odd entry", helper(14));
    return 0;
}

void start(void) { exit(main()); }

__asm__(".text\n"
        ".p2align 4\n"
        ".globl pad\n"
        ".type pad, @function\n"
        "pad:\n"
        "    ret\n"
        ".size pad, 1\n"
        ".globl _start\n"
        ".type _start, @function\n"
        "_start:\n"
        "    jmp start\n"
        ".size _start, .-_start\n");
