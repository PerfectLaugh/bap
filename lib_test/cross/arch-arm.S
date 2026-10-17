/* ARM: the system calls, the entry point, run_code and the epilogue, see
   runner.c */
#include "arch-arm.h"

        .syntax unified
        .arm
        .text

/* long sys(long n, long a, long b, long c, long d, long e, long f) returns
   the result or the negated error */
        .globl sys
sys:
        push {r4, r5, r7, lr}
        mov r7, r0
        mov r0, r1
        mov r1, r2
        mov r2, r3
        ldr r3, [sp, #16]
        ldr r4, [sp, #20]
        ldr r5, [sp, #24]
        svc #0
        pop {r4, r5, r7, pc}

        .globl _start
_start:
        bl main
        mov r1, r0
        mov r0, #SYS_exit_group
        bl sys

/* void run_code(word *state) */
        .globl run_code
run_code:
        push {r4-r11, lr}
        str sp, [r0, #SLOT(SLOT_NSP)]
        mov sp, r0
        ldr r0, [sp, #SLOT(SLOT_APSR)]
        msr APSR_nzcvq, r0
        ldr lr, [sp, #SLOT(SLOT_LR)]
        ldm sp, {r0-r12}
        ldr pc, [sp, #SLOT(SLOT_CODE)]

/* the epilogue, copied after the instruction and at the landings */
        .globl epi_start, epi_mark, epi_end
epi_start:
        stm sp, {r0-r12}
        str lr, [sp, #SLOT(SLOT_LR)]
        mrs r0, APSR
        str r0, [sp, #SLOT(SLOT_APSR)]
        bl epi_mark
epi_mark:
        str lr, [sp, #SLOT(SLOT_LAND)]
        ldr sp, [sp, #SLOT(SLOT_NSP)]
        pop {r4-r11, pc}
epi_end:

/* the alternative epilogue, in the T32 state, for the branches to it,
   PC reads as the address of the instruction plus 4, the mark is at the
   offset of epi_mark and the return to run_code leaves the T32 state */
        .thumb
        .globl alt_start, alt_end
alt_start:
        stm.w sp, {r0-r12}
        str.w lr, [sp, #SLOT(SLOT_LR)]
        mrs r0, APSR
        str.w r0, [sp, #SLOT(SLOT_APSR)]
        mov lr, pc
        nop
alt_mark:
        str.w lr, [sp, #SLOT(SLOT_LAND)]
        ldr.w sp, [sp, #SLOT(SLOT_NSP)]
        pop {r4-r11, pc}
alt_end:
        .if (alt_mark - alt_start) - (epi_mark - epi_start)
        .error "the marks of the epilogues are at different offsets"
        .endif
