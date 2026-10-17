/* MIPS: the system calls, the entry point, run_code and the epilogue, see
   runner.c */
#include "arch-mips.h"

#if WORD_SIZE == 8
#define LOAD ld
#define STORE sd
#define ADDIU daddiu
#define MOVE move
#else
#define LOAD lw
#define STORE sw
#define ADDIU addiu
#define MOVE move
#endif

/* the frame of run_code: ra, s0-s7, fp and gp */
#define FRAME (12 * WORD_SIZE)

        .set noreorder
        .set noat
        .text

/* long sys(long n, long a, long b, long c, long d, long e, long f) returns
   the result or the negated error */
        .globl sys
sys:
#if WORD_SIZE == 8
        move $2, $4
        move $4, $5
        move $5, $6
        move $6, $7
        move $7, $8
        move $8, $9
        move $9, $10
        syscall
#else
        addiu $sp, $sp, -32
        move $2, $4
        move $4, $5
        move $5, $6
        move $6, $7
        lw $7, 48($sp)
        lw $1, 52($sp)
        sw $1, 16($sp)
        lw $1, 56($sp)
        sw $1, 20($sp)
        syscall
        addiu $sp, $sp, 32
#endif
        beqz $7, 1f
        nop
        subu $2, $0, $2
1:      jr $31
        nop

        .globl __start
__start:
        ADDIU $sp, $sp, -32
        jal main
        nop
        move $5, $2
        li $4, SYS_exit_group
        jal sys
        nop

/* void run_code(word *state) */
        .globl run_code
run_code:
        ADDIU $sp, $sp, -FRAME
        STORE $31, SLOT(0)($sp)
        STORE $16, SLOT(1)($sp)
        STORE $17, SLOT(2)($sp)
        STORE $18, SLOT(3)($sp)
        STORE $19, SLOT(4)($sp)
        STORE $20, SLOT(5)($sp)
        STORE $21, SLOT(6)($sp)
        STORE $22, SLOT(7)($sp)
        STORE $23, SLOT(8)($sp)
        STORE $30, SLOT(9)($sp)
        STORE $28, SLOT(10)($sp)
        STORE $sp, SLOT(SLOT_NSP)($4)
        move $sp, $4
#if __mips_isa_rev < 6
        LOAD $1, SLOT(SLOT_HI)($sp)
        mthi $1
        LOAD $1, SLOT(SLOT_LO)($sp)
        mtlo $1
#endif
        .irp r, 2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31
        LOAD $\r, SLOT(\r)($sp)
        .endr
        /* R1 is loaded in the delay slot of the jump */
        LOAD $1, SLOT(SLOT_CODE)($sp)
        jr $1
        LOAD $1, SLOT(1)($sp)

/* the epilogue, copied after the instruction and at the landings */
        .globl epi_start, epi_mark, epi_end
epi_start:
        .irp r, 1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,30,31
        STORE $\r, SLOT(\r)($sp)
        .endr
#if __mips_isa_rev < 6
        mfhi $1
        STORE $1, SLOT(SLOT_HI)($sp)
        mflo $1
        STORE $1, SLOT(SLOT_LO)($sp)
#endif
        bal epi_mark
        nop
epi_mark:
        STORE $31, SLOT(SLOT_LAND)($sp)
        LOAD $sp, SLOT(SLOT_NSP)($sp)
        LOAD $31, SLOT(0)($sp)
        LOAD $16, SLOT(1)($sp)
        LOAD $17, SLOT(2)($sp)
        LOAD $18, SLOT(3)($sp)
        LOAD $19, SLOT(4)($sp)
        LOAD $20, SLOT(5)($sp)
        LOAD $21, SLOT(6)($sp)
        LOAD $22, SLOT(7)($sp)
        LOAD $23, SLOT(8)($sp)
        LOAD $30, SLOT(9)($sp)
        LOAD $28, SLOT(10)($sp)
        jr $31
        ADDIU $sp, $sp, FRAME
epi_end:
