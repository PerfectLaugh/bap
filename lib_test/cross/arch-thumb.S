/* ARM: the system calls, the entry point and run_code, as in arch-arm.S,
   run_code enters the instruction in the T32 state, and the epilogue is
   in the T32 state, see runner.c */
#include "arch-thumb.h"

        .syntax unified
        .arm
        .text

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

/* void run_code(word *state), a load to PC with the bit 0 set enters the
   T32 state */
        .globl run_code
run_code:
        push {r4-r11, lr}
        str sp, [r0, #SLOT(SLOT_NSP)]
        mov sp, r0
        ldr r0, [sp, #SLOT(SLOT_CODE)]
        orr r0, r0, #1
        str r0, [sp, #SLOT(SLOT_CODE)]
        ldr r0, [sp, #SLOT(SLOT_APSR)]
        msr APSR_nzcvq, r0
        ldr lr, [sp, #SLOT(SLOT_LR)]
        ldm sp, {r0-r12}
        ldr pc, [sp, #SLOT(SLOT_CODE)]

/* the epilogue, copied after the instruction and at the landings, the
   link of bl has the bit 0 set, and the return to run_code leaves the
   T32 state */
        .thumb
        .globl epi_start, epi_mark, epi_end
epi_start:
        stm sp, {r0-r12}
        str lr, [sp, #SLOT(SLOT_LR)]
        mrs r0, APSR
        str r0, [sp, #SLOT(SLOT_APSR)]
        mov lr, pc @ reads as the address of the mov plus 4
        nop
epi_mark:
        str lr, [sp, #SLOT(SLOT_LAND)]
        ldr sp, [sp, #SLOT(SLOT_NSP)]
        pop {r4-r11, pc}
epi_end:
