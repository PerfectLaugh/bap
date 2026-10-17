# shifts by a register use its lowest byte
A32 | lsl r0, r1, r2 | R1=1 R2=0x80000000 | R0=1
A32 | lsl r0, r1, r2 | R1=1 R2=32 | R0=0
A32 | lsr r0, r1, r2 | R1=0x80000000 R2=31 | R0=1
A32 | asr r0, r1, r2 | R1=0x80000000 R2=64 | R0=0xffffffff
A32 | ror r0, r1, r2 | R1=1 R2=33 | R0=0x80000000
A32 | lsls r0, r1, r2 | R1=1 R2=32 CF=0 | R0=0 ZF=1 CF=1
A32 | lsls r0, r1, r2 | R1=1 R2=0x100 CF=1 | R0=1 ZF=0 CF=1
A32 | lsrs r0, r1, r2 | R1=0x80000000 R2=33 CF=1 | R0=0 ZF=1 CF=0
A32 | asrs r0, r1, r2 | R1=0x80000000 R2=40 CF=0 | R0=0xffffffff NF=1 CF=1
A32 | rors r0, r1, r2 | R1=0x80000000 R2=32 CF=0 | R0=0x80000000 CF=1
A32 | add r0, r1, r2, lsl r3 | R1=1 R2=1 R3=0x101 | R0=3
# immediate shifts by 32 and the shifter carry
A32 | movs r0, r1, lsr #32 | R1=0x80000000 CF=0 | R0=0 ZF=1 CF=1
A32 | orr r0, r1, r2, lsr #32 | R1=0 R2=0xffffffff | R0=0
A32 | eor r0, r1, r2, asr #32 | R1=0 R2=0x80000000 | R0=0xffffffff
A32 | movs r0, r1, rrx | R1=1 CF=1 | R0=0x80000000 NF=1 CF=1
A32 | ands r0, r1, #0xff000000 | R1=0xff000000 CF=0 | R0=0xff000000 NF=1 CF=1
A32 | ands r0, r1, #0xff | R1=0xff CF=1 | R0=0xff CF=1
A32 | movs r0, #0x80000000 | CF=0 | R0=0x80000000 NF=1 CF=1
# division
A32 | udiv r0, r1, r2 | R1=7 R2=2 | R0=3
A32 | udiv r0, r1, r2 | R1=7 R2=0 | R0=0
A32 | sdiv r0, r1, r2 | R1=0x80000000 R2=0xffffffff | R0=0x80000000
A32 | sdiv r0, r1, r2 | R1=0xfffffff9 R2=2 | R0=0xfffffffd
# saturating arithmetic
A32 | qadd r0, r1, r2 | R1=0x7fffffff R2=1 | R0=0x7fffffff QF=1
A32 | qadd r0, r1, r2 | R1=1 R2=2 | R0=3 QF=0
A32 | qsub r0, r1, r2 | R1=0 R2=0x80000000 | R0=0x7fffffff QF=1
A32 | ssat r0, #8, r1 | R1=0xffffff00 | R0=0xffffff80 QF=1
A32 | usat r0, #8, r1 | R1=0x100 | R0=0xff QF=1
A32 | ssat r0, #16, r1, lsl #4 | R1=0x1000 | R0=0x7fff QF=1
A32 | usat r0, #8, r1, asr #4 | R1=0x7f0 | R0=0x7f QF=0
# multiplication
A32 | smultt r0, r1, r2 | R1=0xffff0000 R2=0x00030000 | R0=0xfffffffd
A32 | smulbt r0, r1, r2 | R1=0x0000fffe R2=0x00050000 | R0=0xfffffff6
A32 | smmul r0, r1, r2 | R1=0x80000000 R2=0x80000000 | R0=0x40000000
A32 | smmla r0, r1, r2, r3 | R1=0x80000000 R2=2 R3=5 | R0=4
A32 | revsh r0, r1 | R1=0x12340080 | R0=0xffff8000
# bitfields and double words
A32 | bfi r0, r1, #28, #4 | R0=0xffffffff R1=0 | R0=0x0fffffff
A32 | bfc r0, #4, #20 | R0=0xffffffff | R0=0xff00000f
A32 | ldrd r0, r1, [r0, #4] | R0=0x2000 M4@0x2004=0x3000 M4@0x2008=7 | R0=0x3000 R1=7
