# the logical operations, the carry of the modified immediates
and.w r0, r1, r2 | R1 R2 | R0
ands.w r0, r1, r2 | R1 R2 CF VF=1 | R0 NF ZF CF VF
ands.w r0, r1, #0xff | R1 CF | R0 NF ZF CF
ands.w r0, r1, #0xff000000 | R1 CF | R0 NF ZF CF
ands.w r0, r1, #0x00ff00ff | R1 CF | R0 NF ZF CF
ands.w r0, r1, #0xff00ff00 | R1 CF | R0 NF ZF CF
ands.w r0, r1, #0x80808080 | R1 CF | R0 NF ZF CF
ands.w r0, r1, #0x3fc | R1 CF | R0 NF ZF CF
orr.w r0, r1, r2 | R1 R2 | R0
orrs.w r0, r1, #0x80000000 | R1 CF | R0 NF ZF CF
eor.w r0, r1, r2 | R1 R2 | R0
eors.w r0, r1, #0x7f00 | R1 CF | R0 NF ZF CF
bic.w r0, r1, r2 | R1 R2 | R0
bics.w r0, r1, #0xf0000000 | R1 CF | R0 NF ZF CF
mov.w r0, r1 | R1 | R0
movs.w r0, r1 | R1 CF VF=1 | R0 NF ZF CF VF
mov.w r0, #0x80000000 | | R0
movs.w r0, #0xff000000 | CF | R0 NF ZF CF
movs.w r0, #0x7f | CF | R0 NF ZF CF
mvn.w r0, r1 | R1 | R0
mvns.w r0, r1 | R1 CF | R0 NF ZF CF
mvn r0, #0xff | | R0
mvns r0, #0x80000000 | CF | R0 NF ZF CF
tst.w r1, r2 | R1 R2 CF VF=1 | NF ZF CF VF
tst.w r1, #0x80000000 | R1 CF | NF ZF CF
teq.w r1, r2 | R1 R2 CF | NF ZF CF
teq.w r1, #0xff | R1 CF | NF ZF CF
# the arithmetic
add.w r0, r1, r2 | R1 R2 | R0
adds.w r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
adds.w r0, r1, #0xff000000 | R1 | R0 NF ZF CF VF
sub.w r0, r1, r2 | R1 R2 | R0
subs.w r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
subs.w r0, r1, #1 | R1 | R0 NF ZF CF VF
rsb r0, r1, r2 | R1 R2 | R0
rsbs r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
rsbs.w r0, r1, #0 | R1 | R0 NF ZF CF VF
adc.w r0, r1, r2 | R1 R2 CF | R0
adcs.w r0, r1, r2 | R1 R2 CF | R0 NF ZF CF VF
adcs r0, r1, #0x80000000 | R1 CF | R0 NF ZF CF VF
sbc.w r0, r1, r2 | R1 R2 CF | R0
sbcs.w r0, r1, r2 | R1 R2 CF | R0 NF ZF CF VF
sbcs r0, r1, #0x3fc | R1 CF | R0 NF ZF CF VF
cmp.w r1, r2 | R1 R2 | NF ZF CF VF
cmp.w r1, #0x100 | R1 | NF ZF CF VF
cmn.w r1, r2 | R1 R2 | NF ZF CF VF
cmn.w r1, #1 | R1 | NF ZF CF VF
movw r0, #0xabcd | R0 | R0
movt r0, #0xabcd | R0 | R0
# the bit fields, extensions and reversals
bfc r0, #4, #8 | R0 | R0
bfi r0, r1, #4, #8 | R0=0x12345678 R1 | R0
ubfx r0, r1, #4, #8 | R1 | R0
sbfx r0, r1, #4, #8 | R1 | R0
rbit r0, r1 | R1 | R0
rev.w r0, r1 | R1 | R0
rev16.w r0, r1 | R1 | R0
pkhtb r0, r1, r2, asr #8 | R1 R2 | R0
pkhbt r0, r1, r2, lsl #8 | R1 R2 | R0
uxtb.w r0, r1 | R1 | R0
uxth.w r0, r1, ror #8 | R1 | R0
sxtb.w r0, r1, ror #16 | R1 | R0
sxth.w r0, r1 | R1 | R0
uxtab r0, r1, r2 | R1 R2 | R0
uxtah r0, r1, r2, ror #24 | R1 R2 | R0
sxtab r0, r1, r2, ror #8 | R1 R2 | R0
sxtah r0, r1, r2 | R1 R2 | R0
# the multiplications
mul r0, r1, r2 | R1 R2 | R0
mla r0, r1, r2, r3 | R1 R2 R3=0x12345678 | R0
mls r0, r1, r2, r3 | R1 R2 R3=0x12345678 | R0
umull r0, r1, r2, r3 | R2 R3 | R0 R1
smull r0, r1, r2, r3 | R2 R3 | R0 R1
umlal r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
smlal r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
smulbb r0, r1, r2 | R1 R2 | R0
smultb r0, r1, r2 | R1 R2 | R0
smlabb r0, r1, r2, r3 | R1 R2 R3=0x7fffffff QF=0 | R0 QF
smlawb r0, r1, r2, r3 | R1 R2 R3=0x7fffffff QF=0 | R0 QF
smlad r0, r1, r2, r3 | R1 R2 R3=0x12345678 QF=0 | R0 QF
smuad r0, r1, r2 | R1 R2 QF=0 | R0 QF
smlalbt r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
# the loads and stores
ldr.w r0, [r1, #4] | R1=0x200000 M4@0x200004=0x11223344 | R0
ldrb.w r0, [r1, #3] | R1=0x200000 M4@0x200000=0x112233f4 | R0
str.w r0, [r1, #4] | R0=0x11223344 R1=0x200000 | M4@0x200004
strb.w r0, [r1, #1] | R0=0x11223344 R1=0x200000 | M4@0x200000
ldr.w pc, [r1, #4] | R1=0x200000 M4@0x200004=0x20101 | PC | 0x100
ldrh r0, [r1], #2 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrh r0, [r1, #-2]! | R1=0x200004 M4@0x200000=0x8899aabb | R0 R1
ldrsh r0, [r1, #2]! | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsh r0, [r1], #-2 | R1=0x200002 M4@0x200000=0x8899aabb | R0 R1
ldrsb r0, [r1], #1 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsb r0, [r1, #3]! | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
strh r0, [r1], #2 | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
strh r0, [r1, #-2]! | R0=0x11223344 R1=0x200002 | M4@0x200000 R1
ldrd r2, r3, [r1], #-8 | R1=0x200008 M8@0x200008=0x1122334455667788 | R2 R3 R1
ldrd r2, r3, [r1, #8]! | R1=0x200000 M8@0x200008=0x1122334455667788 | R2 R3 R1
strd r2, r3, [r1], #8 | R1=0x200000 R2=0x55667788 R3=0x11223344 | M8@0x200000 R1
strd r2, r3, [r1, #-8]! | R1=0x200008 R2=0x55667788 R3=0x11223344 | M8@0x200000 R1
ldrex r0, [r1, #4] | R1=0x200000 M4@0x200004=0x11223344 | R0
ldrexb r0, [r1] | R1=0x200000 M4@0x200000=0x112233f4 | R0
ldrexh r0, [r1] | R1=0x200000 M4@0x200000=0x8899aabb | R0
ldrexd r2, r3, [r1] | R1=0x200000 M8@0x200000=0x1122334455667788 | R2 R3
# the multiple loads and stores
ldm.w r1, {r2, r3, r4} | R1=0x200000 M4@0x200000=1 M4@0x200004=2 M4@0x200008=3 | R2 R3 R4 R1
ldm.w r1!, {r2, r3} | R1=0x200000 M4@0x200000=1 M4@0x200004=2 | R2 R3 R1
ldmdb r1, {r2, r3} | R1=0x200008 M4@0x200000=1 M4@0x200004=2 | R2 R3 R1
ldmdb r1!, {r2, r3} | R1=0x200008 M4@0x200000=1 M4@0x200004=2 | R2 R3 R1
ldm.w r1!, {r2, pc} | R1=0x200000 M4@0x200000=1 M4@0x200004=0x20101 | R2 R1 PC | 0x100
stm.w r1, {r2, r3} | R1=0x200000 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stm.w r1!, {r2, r3} | R1=0x200000 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stmdb r1, {r2, r3} | R1=0x200008 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stmdb r1!, {r2, r3, r4} | R1=0x20000c R2=1 R3=2 R4=3 | M4@0x200000 M4@0x200004 M4@0x200008 R1
# the hints and the barriers
nop.w | R0=1 | R0
dmb ish | R0=1 | R0
dsb sy | R0=1 | R0
pld [r1, #4] | R0=1 R1=0x200000 | R0
