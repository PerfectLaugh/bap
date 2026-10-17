/* PowerPC: the system calls, the entry point, run_code and the epilogue, see
   runner.c */
#include "arch-ppc.h"

#if WORD_SIZE == 8
#define LOAD ld
#define STORE std
#define STOREU stdu
        .abiversion 2
#else
#define LOAD lwz
#define STORE stw
#define STOREU stwu
#endif

/* the address of the instruction, INSN_ADDR of runner.c */
#define INSN_ADDR 0x20000

/* the frame of run_code: the back chain, LR, CR, r2, r13-r31 */
#define FRAME (24 * WORD_SIZE)
#define F_LR SLOT(1)
#define F_CR SLOT(2)
#define F_R(n) SLOT((n) - 10)
#define F_R2 SLOT(22)

        .text

/* long sys(long n, long a, long b, long c, long d, long e, long f) returns
   the result or the negated error */
        .globl sys
sys:
        mr 0, 3
        mr 3, 4
        mr 4, 5
        mr 5, 6
        mr 6, 7
        mr 7, 8
        mr 8, 9
        sc
        bnslr
        neg 3, 3
        blr

        .globl _start
_start:
#if WORD_SIZE == 8
        bl 1f
1:      mflr 2
        addis 2, 2, (.TOC. - 1b)@ha
        addi 2, 2, (.TOC. - 1b)@l
        clrrdi 1, 1, 4
#else
        clrrwi 1, 1, 4
#endif
        li 0, 0
        STOREU 0, -64(1)
        bl main
        nop
        mr 4, 3
        li 3, SYS_exit_group
        bl sys
        nop

/* void run_code(word *state) */
        .globl run_code
run_code:
        STOREU 1, -FRAME(1)
        mflr 0
        STORE 0, F_LR(1)
        mfcr 0
        STORE 0, F_CR(1)
        STORE 2, F_R2(1)
        .irp r, 13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
        STORE \r, F_R(\r)(1)
        .endr
        STORE 1, SLOT(SLOT_NSP)(3)
        mr 1, 3
        LOAD 0, SLOT(SLOT_CR)(1)
        mtcrf 0xff, 0
        LOAD 0, SLOT(SLOT_XER)(1)
        mtxer 0
        LOAD 0, SLOT(SLOT_LR)(1)
        mtlr 0
        LOAD 0, SLOT(SLOT_CTR)(1)
        mtctr 0
        .irp r, 0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
        LOAD \r, SLOT(\r)(1)
        .endr
        ba INSN_ADDR

/* the epilogue, copied after the instruction and at the landings */
        .globl epi_start, epi_mark, epi_end
epi_start:
        .irp r, 0,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
        STORE \r, SLOT(\r)(1)
        .endr
        mfcr 0
        STORE 0, SLOT(SLOT_CR)(1)
        mfxer 0
        STORE 0, SLOT(SLOT_XER)(1)
        mflr 0
        STORE 0, SLOT(SLOT_LR)(1)
        mfctr 0
        STORE 0, SLOT(SLOT_CTR)(1)
        bl epi_mark
epi_mark:
        mflr 0
        STORE 0, SLOT(SLOT_LAND)(1)
        LOAD 1, SLOT(SLOT_NSP)(1)
        LOAD 2, F_R2(1)
        .irp r, 13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
        LOAD \r, F_R(\r)(1)
        .endr
        LOAD 0, F_CR(1)
        mtcrf 0xff, 0
        LOAD 0, F_LR(1)
        mtlr 0
        addi 1, 1, FRAME
        blr
epi_end:
