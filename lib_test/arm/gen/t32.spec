# shifted register operands and the shifter carry
T32 | ands.w r0, r1, r2, lsr #1 | R1=0xffffffff R2=3 CF=0 | R0=1 CF=1
T32 | orr.w r0, r1, r2, lsr #32 | R1=0 R2=0xffffffff | R0=0
T32 | sub.w r0, r1, r2, asr #31 | R1=0 R2=0x80000000 | R0=1
T32 | adds.w r0, r1, r2, lsl #1 | R1=0x80000000 R2=0x40000000 | R0=0 NF=0 ZF=1 CF=1 VF=1
T32 | mvns.w r0, r1, lsl #4 | R1=0x10000000 CF=0 | R0=0xffffffff NF=1 CF=1
T32 | tst.w r1, r2, ror #31 | R1=2 R2=1 CF=1 | NF=0 ZF=0 CF=0
T32 | cmp.w r1, r2, ror #16 | R1=0x10000 R2=1 | ZF=1 CF=1
T32 | orn r0, r1, r2 | R1=0 R2=0xffff0000 | R0=0xffff
# shifts
T32 | lsls.w r0, r1, r2 | R1=1 R2=0x80000000 CF=1 | R0=1 CF=1
T32 | asrs.w r0, r1, r2 | R1=0x80000000 R2=40 CF=0 | R0=0xffffffff CF=1
T32 | rors.w r0, r1, #1 | R1=1 CF=0 | R0=0x80000000 NF=1 CF=1
T32 | rrxs r0, r1 | R1=1 CF=1 | R0=0x80000000 CF=1
T32 | asrs r1, r2 | R1=0x80000000 R2=31 CF=1 | R1=0xffffffff NF=1 CF=0
T32 | rors r1, r2 | R1=1 R2=1 | R1=0x80000000 NF=1 CF=1
T32 | cmn r1, r2 | R1=0xffffffff R2=1 | ZF=1 CF=1
# miscellaneous
T32 | clz r0, r1 | R1=0x00010000 | R0=15
T32 | mrs r0, apsr | NF=1 ZF=0 CF=1 VF=1 QF=0 | R0=0xb0000000
T32 | qadd r0, r1, r2 | R1=0x80000000 R2=0xffffffff | R0=0x80000000 QF=1
T32 | sdiv r0, r1, r2 | R1=100 R2=0xfffffffd | R0=0xffffffdf
T32 | udiv r0, r1, r2 | R1=1 R2=0 | R0=0
T32 | bfi r0, r1, #28, #4 | R0=0xffffffff R1=0 | R0=0x0fffffff
# loads and stores
T32 | ldrd r0, r1, [r0, #4] | R0=0x2000 M4@0x2004=0x3000 M4@0x2008=7 | R0=0x3000 R1=7
T32 | ldr r0, [r1, #4]! | R1=0x2000 M4@0x2004=9 | R0=9 R1=0x2004
T32 | ldrb r0, [r1], #-1 | R1=0x2001 M1@0x2001=0x80 | R0=0x80 R1=0x2000
T32 | str r0, [r1], #-4 | R0=5 R1=0x2004 | M4@0x2004=5 R1=0x2000
T32 | ldrex r0, [r1] | R1=0x2000 M4@0x2000=3 | R0=3
T32 | strex r0, r2, [r1] | R0=9 R1=0x2000 R2=4 | R0=0 M4@0x2000=4
# branches
T32 | pop {r7, pc} | SP=0x3000 M4@0x3000=7 M4@0x3004=0x4001 | R7=7 SP=0x3008 PC=0x4001
T32 | bl .+0x40 | | PC=0x10040
