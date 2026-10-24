/* the loop of MIPS, whose block stores to the code of the next block,
   the instruction after the loop, and ends with a branch, whose delay
   slot runs before it, so that the interpreter doesn't run the branch
   anew, as the code, that may be changed, after its delay slot, which
   would run the delay slot again, when the branch isn't taken: the sum
   counts 2 per iteration */
#include "common.h"

unsigned loop(unsigned n);
__asm__(".text\n"
        ".set noreorder\n"
        ".globl loop\n"
        ".type loop, @function\n"
        "loop:\n"
        "    li $v0, 0\n"
        "    la $t0, 2f\n"
        "    lw $t1, 0($t0)\n"
        "1:  addiu $v0, $v0, 1\n"
        "    sw $t1, 0($t0)\n"
        "    addiu $a0, $a0, -1\n"
        "    bne $a0, $zero, 1b\n"
        "    addiu $v0, $v0, 1\n"
        "2:  addiu $v0, $v0, 0\n"
        "    jr $ra\n"
        "    nop\n"
        ".set reorder\n"
        ".size loop, .-loop\n");

int main(void) {
    line("delay", loop(10));
    return 0;
}

void _start(void) { exit(main()); }
