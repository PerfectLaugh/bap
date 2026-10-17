# the conditions
moveq r0, #1 | R0=0 NF ZF CF VF | R0
movne r0, #1 | R0=0 NF ZF CF VF | R0
movcs r0, #1 | R0=0 NF ZF CF VF | R0
movcc r0, #1 | R0=0 NF ZF CF VF | R0
movmi r0, #1 | R0=0 NF ZF CF VF | R0
movpl r0, #1 | R0=0 NF ZF CF VF | R0
movvs r0, #1 | R0=0 NF ZF CF VF | R0
movvc r0, #1 | R0=0 NF ZF CF VF | R0
movhi r0, #1 | R0=0 NF ZF CF VF | R0
movls r0, #1 | R0=0 NF ZF CF VF | R0
movge r0, #1 | R0=0 NF ZF CF VF | R0
movlt r0, #1 | R0=0 NF ZF CF VF | R0
movgt r0, #1 | R0=0 NF ZF CF VF | R0
movle r0, #1 | R0=0 NF ZF CF VF | R0
addseq r0, r1, r2 | R0=5 R1=0xffffffff R2=1 NF=1 ZF CF=0 VF=1 | R0 NF ZF CF VF
# the logical operations, with the shifter carry
and r0, r1, r2 | R1 R2 | R0
ands r0, r1, r2 | R1 R2 CF VF=1 | R0 NF ZF CF VF
eor r0, r1, r2 | R1 R2 | R0
eors r0, r1, r2 | R1 R2 CF VF=1 | R0 NF ZF CF VF
orr r0, r1, r2 | R1 R2 | R0
orrs r0, r1, r2 | R1 R2 CF VF=1 | R0 NF ZF CF VF
bic r0, r1, r2 | R1 R2 | R0
bics r0, r1, r2 | R1 R2 CF VF=1 | R0 NF ZF CF VF
and r0, r1, #0xff | R1 | R0
ands r0, r1, #0xff | R1 CF | R0 NF ZF CF
ands r0, r1, #0xff000000 | R1 CF | R0 NF ZF CF
ands r0, r1, #0x3fc | R1 CF | R0 NF ZF CF
eors r0, r1, #0x80000001 | R1 CF | R0 NF ZF CF
orrs r0, r1, #0xf0000000 | R1 CF | R0 NF ZF CF
bics r0, r1, #0x7f00 | R1 CF | R0 NF ZF CF
orr r0, r1, r2, lsl #3 | R1 R2 | R0
orrs r0, r1, r2, lsl #1 | R1 R2 CF | R0 NF ZF CF
eors r0, r1, r2, lsr #1 | R1 R2 CF | R0 NF ZF CF
eors r0, r1, r2, lsr #32 | R1 R2 CF | R0 NF ZF CF
ands r0, r1, r2, asr #7 | R1 R2 CF | R0 NF ZF CF
ands r0, r1, r2, asr #32 | R1 R2 CF | R0 NF ZF CF
bics r0, r1, r2, ror #5 | R1 R2 CF | R0 NF ZF CF
orrs r0, r1, r2, rrx | R1 R2 CF | R0 NF ZF CF
and r0, r1, r2, lsl r3 | R1=0xffffffff R2 R3@count | R0
ands r0, r1, r2, lsl r3 | R1=0xffffffff R2 R3@count CF | R0 NF ZF CF
eors r0, r1, r2, lsr r3 | R1=0 R2 R3@count CF | R0 NF ZF CF
orrs r0, r1, r2, asr r3 | R1=0 R2 R3@count CF | R0 NF ZF CF
bics r0, r1, r2, ror r3 | R1=0xffffffff R2 R3@count CF | R0 NF ZF CF
# the moves
mov r0, r1 | R1 | R0
movs r0, r1 | R1 CF VF=1 | R0 NF ZF CF VF
mov r0, #0x3fc | | R0
movs r0, #0x80000000 | CF | R0 NF ZF CF
movs r0, #0x7f | CF | R0 NF ZF CF
mvn r0, r1 | R1 | R0
mvns r0, r1 | R1 CF | R0 NF ZF CF
mvn r0, #0xff | | R0
mvns r0, #0x80000000 | CF | R0 NF ZF CF
mvns r0, r1, lsl #4 | R1 CF | R0 NF ZF CF
mvns r0, r1, asr r2 | R1 R2@count CF | R0 NF ZF CF
lsl r0, r1, #5 | R1 | R0
lsls r0, r1, #1 | R1 CF | R0 NF ZF CF
lsrs r0, r1, #1 | R1 CF | R0 NF ZF CF
lsrs r0, r1, #32 | R1 CF | R0 NF ZF CF
asrs r0, r1, #31 | R1 CF | R0 NF ZF CF
asrs r0, r1, #32 | R1 CF | R0 NF ZF CF
rors r0, r1, #8 | R1 CF | R0 NF ZF CF
rrxs r0, r1 | R1 CF | R0 NF ZF CF
lsls r0, r1, r2 | R1 R2@count CF | R0 NF ZF CF
lsrs r0, r1, r2 | R1 R2@count CF | R0 NF ZF CF
asrs r0, r1, r2 | R1 R2@count CF | R0 NF ZF CF
rors r0, r1, r2 | R1 R2@count CF | R0 NF ZF CF
movw r0, #0xabcd | R0 | R0
movt r0, #0xabcd | R0 | R0
movweq r0, #0x1234 | R0=0xffffffff ZF | R0
movtne r0, #0x1234 | R0=0xffffffff ZF | R0
# the arithmetic
add r0, r1, r2 | R1 R2 | R0
adds r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
sub r0, r1, r2 | R1 R2 | R0
subs r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
rsb r0, r1, r2 | R1 R2 | R0
rsbs r0, r1, r2 | R1 R2 | R0 NF ZF CF VF
adc r0, r1, r2 | R1 R2 CF | R0
adcs r0, r1, r2 | R1 R2 CF | R0 NF ZF CF VF
sbc r0, r1, r2 | R1 R2 CF | R0
sbcs r0, r1, r2 | R1 R2 CF | R0 NF ZF CF VF
rsc r0, r1, r2 | R1 R2 CF | R0
rscs r0, r1, r2 | R1 R2 CF | R0 NF ZF CF VF
adds r0, r1, #0xff000000 | R1 | R0 NF ZF CF VF
subs r0, r1, #1 | R1 | R0 NF ZF CF VF
rsbs r0, r1, #0 | R1 | R0 NF ZF CF VF
adcs r0, r1, #0x80000000 | R1 CF | R0 NF ZF CF VF
sbcs r0, r1, #0x3fc | R1 CF | R0 NF ZF CF VF
rscs r0, r1, #0x7f | R1 CF | R0 NF ZF CF VF
adds r0, r1, r2, lsl #31 | R1 R2 | R0 NF ZF CF VF
subs r0, r1, r2, asr #32 | R1 R2 | R0 NF ZF CF VF
rsbs r0, r1, r2, lsr #4 | R1 R2 | R0 NF ZF CF VF
adcs r0, r1, r2, ror #16 | R1 R2 CF | R0 NF ZF CF VF
sbcs r0, r1, r2, rrx | R1 R2 CF | R0 NF ZF CF VF
add r0, r1, r2, lsl r3 | R1=1 R2 R3@count | R0
subs r0, r1, r2, lsr r3 | R1=0x80000000 R2 R3@count | R0 NF ZF CF VF
rscs r0, r1, r2, asr r3 | R1=1 R2 R3@count CF | R0 NF ZF CF VF
# the comparisons and the tests
cmp r1, r2 | R1 R2 | NF ZF CF VF
cmn r1, r2 | R1 R2 | NF ZF CF VF
tst r1, r2 | R1 R2 CF VF=1 | NF ZF CF VF
teq r1, r2 | R1 R2 CF VF=1 | NF ZF CF VF
cmp r1, #0x80 | R1 | NF ZF CF VF
cmn r1, #1 | R1 | NF ZF CF VF
tst r1, #0x80000000 | R1 CF | NF ZF CF
teq r1, #0xff | R1 CF | NF ZF CF
cmp r1, r2, lsl #1 | R1 R2 | NF ZF CF VF
cmn r1, r2, asr #32 | R1 R2 | NF ZF CF VF
tst r1, r2, lsr #1 | R1 R2 CF | NF ZF CF
teq r1, r2, ror #31 | R1 R2 CF | NF ZF CF
cmp r1, r2, lsl r3 | R1=0 R2 R3@count | NF ZF CF VF
cmn r1, r2, lsr r3 | R1=1 R2 R3@count | NF ZF CF VF
tst r1, r2, asr r3 | R1=1 R2 R3@count CF | NF ZF CF
teq r1, r2, ror r3 | R1=0 R2 R3@count CF | NF ZF CF
# the program counter reads as the address of the instruction plus 8
add r0, pc, #4 | | R0
sub r0, pc, #8 | | R0
mov r0, pc | | R0
add r0, r1, pc | R1=1 | R0
add r0, pc, r1, lsl #2 | R1=1 | R0
# the writes to the program counter are branches
mov pc, lr | LR=0x20100 | PC | 0x100
add pc, pc, #0xf8 | | PC | 0x100
add pc, r1, r2 | R1=0x20000 R2=0x100 | PC | 0x100
sub pc, r1, #0x400 | R1=0x20000 | PC | -0x400
moveq pc, lr | LR=0x20100 ZF | PC | 0x100
# the bit field operations
bfc r0, #4, #8 | R0 | R0
bfc r0, #0, #32 | R0 | R0
bfi r0, r1, #4, #8 | R0=0x12345678 R1 | R0
bfi r0, r1, #31, #1 | R0=0 R1 | R0
ubfx r0, r1, #4, #8 | R1 | R0
ubfx r0, r1, #0, #32 | R1 | R0
sbfx r0, r1, #4, #8 | R1 | R0
sbfx r0, r1, #31, #1 | R1 | R0
rbit r0, r1 | R1 | R0
rev r0, r1 | R1 | R0
rev16 r0, r1 | R1 | R0
pkhtb r0, r1, r2, asr #8 | R1 R2 | R0
pkhtb r0, r1, r2, asr #31 | R1 R2 | R0
# the extensions, with the rotations
uxtb r0, r1 | R1 | R0
uxtb r0, r1, ror #8 | R1 | R0
uxth r0, r1, ror #16 | R1 | R0
sxtb r0, r1, ror #24 | R1 | R0
sxth r0, r1 | R1 | R0
sxth r0, r1, ror #8 | R1 | R0
uxtab r0, r1, r2 | R1 R2 | R0
uxtah r0, r1, r2, ror #8 | R1 R2 | R0
sxtab r0, r1, r2, ror #16 | R1 R2 | R0
sxtah r0, r1, r2, ror #24 | R1 R2 | R0
# the multiplications
mul r0, r1, r2 | R1 R2 | R0
muls r0, r1, r2 | R1 R2 CF VF | R0 NF ZF CF VF
mla r0, r1, r2, r3 | R1 R2 R3=0x12345678 | R0
mlas r0, r1, r2, r3 | R1 R2 R3=0x80000000 | R0 NF ZF
mls r0, r1, r2, r3 | R1 R2 R3=0x12345678 | R0
umull r0, r1, r2, r3 | R2 R3 | R0 R1
umulls r0, r1, r2, r3 | R2 R3 CF VF | R0 R1 NF ZF CF VF
smull r0, r1, r2, r3 | R2 R3 | R0 R1
smulls r0, r1, r2, r3 | R2 R3 | R0 R1 NF ZF
umlal r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
umlals r0, r1, r2, r3 | R0=0 R1=0 R2 R3 | R0 R1 NF ZF
smlal r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
smlals r0, r1, r2, r3 | R0=1 R1=0xffffffff R2 R3 | R0 R1 NF ZF
smulbb r0, r1, r2 | R1 R2 | R0
smultb r0, r1, r2 | R1 R2 | R0
smlabb r0, r1, r2, r3 | R1 R2 R3=0x7fffffff QF=0 | R0 QF
smlawb r0, r1, r2, r3 | R1 R2 R3=0x7fffffff QF=0 | R0 QF
smlad r0, r1, r2, r3 | R1 R2 R3=0x12345678 QF=0 | R0 QF
smuad r0, r1, r2 | R1 R2 QF=0 | R0 QF
smlalbt r0, r1, r2, r3 | R0=0xffffffff R1=0x12345678 R2 R3 | R0 R1
# the word and byte loads and stores
ldr r0, [r1] | R1=0x200000 M4@0x200000=0x11223344 | R0
ldr r0, [r1, #4] | R1=0x200000 M4@0x200004=0x11223344 | R0
ldr r0, [r1, #-4] | R1=0x200008 M4@0x200004=0x11223344 | R0
ldr r0, [r1, r2] | R1=0x200000 R2=8 M4@0x200008=0x11223344 | R0
ldr r0, [r1, -r2] | R1=0x200010 R2=8 M4@0x200008=0x11223344 | R0
ldr r0, [r1, r2, lsl #2] | R1=0x200000 R2=2 M4@0x200008=0x11223344 | R0
ldr r0, [r1, -r2, asr #1] | R1=0x200000 R2=0xfffffff0 M4@0x200008=0x11223344 | R0
ldr r0, [r1, #4]! | R1=0x200000 M4@0x200004=0x11223344 | R0 R1
ldr r0, [r1, #-4]! | R1=0x200008 M4@0x200004=0x11223344 | R0 R1
ldr r0, [r1, r2, lsl #1]! | R1=0x200000 R2=2 M4@0x200004=0x11223344 | R0 R1
ldr r0, [r1, -r2]! | R1=0x200008 R2=4 M4@0x200004=0x11223344 | R0 R1
ldr r0, [r1], #4 | R1=0x200000 M4@0x200000=0x11223344 | R0 R1
ldr r0, [r1], #-4 | R1=0x200000 M4@0x200000=0x11223344 | R0 R1
ldr r0, [r1], r2, lsl #3 | R1=0x200000 R2=1 M4@0x200000=0x11223344 | R0 R1
ldr r0, [r1], -r2 | R1=0x200000 R2=4 M4@0x200000=0x11223344 | R0 R1
ldr r0, [pc, #0x100] | M4@0x20108=0x11223344 | R0
ldrb r0, [r1] | R1=0x200000 M4@0x200000=0x112233f4 | R0
ldrb r0, [r1, #-1] | R1=0x200004 M4@0x200000=0x112233f4 | R0
ldrb r0, [r1, r2, lsr #1] | R1=0x200000 R2=6 M4@0x200000=0x112233f4 | R0
ldrb r0, [r1, #1]! | R1=0x200000 M4@0x200000=0x112233f4 | R0 R1
ldrb r0, [r1, r2]! | R1=0x200000 R2=2 M4@0x200000=0x112233f4 | R0 R1
ldrb r0, [r1], #3 | R1=0x200000 M4@0x200000=0x112233f4 | R0 R1
ldrb r0, [r1], -r2 | R1=0x200000 R2=3 M4@0x200000=0x112233f4 | R0 R1
ldrt r0, [r1], r2 | R1=0x200000 R2=8 M4@0x200000=0x11223344 | R0 R1
ldrbt r0, [r1], #1 | R1=0x200000 M4@0x200000=0x112233f4 | R0 R1
ldrbt r0, [r1], -r2 | R1=0x200000 R2=8 M4@0x200000=0x112233f4 | R0 R1
str r0, [r1] | R0=0x11223344 R1=0x200000 | M4@0x200000
str r0, [r1, #-4] | R0=0x11223344 R1=0x200008 | M4@0x200004
str r0, [r1, r2, lsl #2] | R0=0x11223344 R1=0x200000 R2=1 | M4@0x200004
str r0, [r1, #4]! | R0=0x11223344 R1=0x200000 | M4@0x200004 R1
str r0, [r1, -r2]! | R0=0x11223344 R1=0x200008 R2=4 | M4@0x200004 R1
str r0, [r1], #4 | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
str r0, [r1], r2 | R0=0x11223344 R1=0x200000 R2=8 | M4@0x200000 R1
strt r0, [r1], r2 | R0=0x11223344 R1=0x200000 R2=8 | M4@0x200000 R1
str pc, [r1] | R1=0x200000 | M4@0x200000
strb r0, [r1] | R0=0x11223344 R1=0x200000 | M4@0x200000
strb r0, [r1, #3] | R0=0x11223344 R1=0x200000 | M4@0x200000
strb r0, [r1, -r2] | R0=0x11223344 R1=0x200004 R2=2 | M4@0x200000
strb r0, [r1, #1]! | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
strb r0, [r1, r2]! | R0=0x11223344 R1=0x200000 R2=3 | M4@0x200000 R1
strb r0, [r1], #-1 | R0=0x11223344 R1=0x200002 | M4@0x200000 R1
strb r0, [r1], r2 | R0=0x11223344 R1=0x200001 R2=2 | M4@0x200000 R1
strbt r0, [r1], #1 | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
strbt r0, [r1], -r2 | R0=0x11223344 R1=0x200002 R2=1 | M4@0x200000 R1
ldr pc, [r1] | R1=0x200000 M4@0x200000=0x20100 | PC | 0x100
ldr pc, [r1], #4 | R1=0x200000 M4@0x200000=0x1fc00 | PC R1 | -0x400
# the halfword, signed and doubleword loads and stores
ldrh r0, [r1] | R1=0x200000 M4@0x200000=0x8899aabb | R0
ldrh r0, [r1, #-2] | R1=0x200004 M4@0x200000=0x8899aabb | R0
ldrh r0, [r1, r2] | R1=0x200000 R2=2 M4@0x200000=0x8899aabb | R0
ldrh r0, [r1, -r2] | R1=0x200004 R2=2 M4@0x200000=0x8899aabb | R0
ldrh r0, [r1, #2]! | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrh r0, [r1, -r2]! | R1=0x200004 R2=4 M4@0x200000=0x8899aabb | R0 R1
ldrh r0, [r1], #2 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrh r0, [r1], -r2 | R1=0x200000 R2=6 M4@0x200000=0x8899aabb | R0 R1
ldrht r0, [r1], #-2 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrht r0, [r1], r2 | R1=0x200000 R2=6 M4@0x200000=0x8899aabb | R0 R1
ldrsh r0, [r1] | R1=0x200000 M4@0x200000=0x8899aabb | R0
ldrsh r0, [r1, #2] | R1=0x200000 M4@0x200000=0x7899aabb | R0
ldrsh r0, [r1, -r2] | R1=0x200002 R2=2 M4@0x200000=0x8899aabb | R0
ldrsh r0, [r1, #2]! | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsh r0, [r1], r2 | R1=0x200000 R2=2 M4@0x200000=0x8899aabb | R0 R1
ldrsht r0, [r1], #2 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsht r0, [r1], -r2 | R1=0x200000 R2=2 M4@0x200000=0x8899aabb | R0 R1
ldrsb r0, [r1] | R1=0x200000 M4@0x200000=0x8899aabb | R0
ldrsb r0, [r1, #3] | R1=0x200000 M4@0x200000=0x7899aabb | R0
ldrsb r0, [r1, r2] | R1=0x200000 R2=1 M4@0x200000=0x8899aabb | R0
ldrsb r0, [r1, #-1]! | R1=0x200004 M4@0x200000=0x8899aabb | R0 R1
ldrsb r0, [r1], #1 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsbt r0, [r1], #1 | R1=0x200000 M4@0x200000=0x8899aabb | R0 R1
ldrsbt r0, [r1], -r2 | R1=0x200000 R2=1 M4@0x200000=0x8899aabb | R0 R1
strh r0, [r1] | R0=0x11223344 R1=0x200000 | M4@0x200000
strh r0, [r1, #2] | R0=0x11223344 R1=0x200000 | M4@0x200000
strh r0, [r1, -r2] | R0=0x11223344 R1=0x200004 R2=2 | M4@0x200000
strh r0, [r1, #2]! | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
strh r0, [r1], #-2 | R0=0x11223344 R1=0x200002 | M4@0x200000 R1
strh r0, [r1], r2 | R0=0x11223344 R1=0x200000 R2=2 | M4@0x200000 R1
strht r0, [r1], #2 | R0=0x11223344 R1=0x200000 | M4@0x200000 R1
strht r0, [r1], -r2 | R0=0x11223344 R1=0x200002 R2=2 | M4@0x200000 R1
ldrd r2, r3, [r1] | R1=0x200000 M8@0x200000=0x1122334455667788 | R2 R3
ldrd r2, r3, [r1, #-8] | R1=0x200008 M8@0x200000=0x1122334455667788 | R2 R3
ldrd r2, r3, [r1, r4] | R1=0x200000 R4=8 M8@0x200008=0x1122334455667788 | R2 R3
ldrd r2, r3, [r1, -r4] | R1=0x200010 R4=8 M8@0x200008=0x1122334455667788 | R2 R3
ldrd r2, r3, [r1, #8]! | R1=0x200000 M8@0x200008=0x1122334455667788 | R2 R3 R1
ldrd r2, r3, [r1, r4]! | R1=0x200000 R4=8 M8@0x200008=0x1122334455667788 | R2 R3 R1
ldrd r2, r3, [r1], #8 | R1=0x200000 M8@0x200000=0x1122334455667788 | R2 R3 R1
ldrd r2, r3, [r1], -r4 | R1=0x200008 R4=8 M8@0x200008=0x1122334455667788 | R2 R3 R1
strd r2, r3, [r1] | R1=0x200000 R2=0x55667788 R3=0x11223344 | M8@0x200000
strd r2, r3, [r1, #-8] | R1=0x200008 R2=0x55667788 R3=0x11223344 | M8@0x200000
strd r2, r3, [r1, r4] | R1=0x200000 R4=8 R2=0x55667788 R3=0x11223344 | M8@0x200008
strd r2, r3, [r1, #8]! | R1=0x200000 R2=0x55667788 R3=0x11223344 | M8@0x200008 R1
strd r2, r3, [r1, -r4]! | R1=0x200010 R4=8 R2=0x55667788 R3=0x11223344 | M8@0x200008 R1
strd r2, r3, [r1], #8 | R1=0x200000 R2=0x55667788 R3=0x11223344 | M8@0x200000 R1
strd r2, r3, [r1], r4 | R1=0x200000 R4=8 R2=0x55667788 R3=0x11223344 | M8@0x200000 R1
# the exclusive loads, an exclusive store fails without a monitor
ldrex r0, [r1] | R1=0x200000 M4@0x200000=0x11223344 | R0
ldrexb r0, [r1] | R1=0x200000 M4@0x200000=0x112233f4 | R0
ldrexh r0, [r1] | R1=0x200000 M4@0x200000=0x8899aabb | R0
ldrexd r2, r3, [r1] | R1=0x200000 M8@0x200000=0x1122334455667788 | R2 R3
# the multiple loads and stores
ldm r1, {r2, r3, r4} | R1=0x200000 M4@0x200000=1 M4@0x200004=2 M4@0x200008=3 | R2 R3 R4 R1
ldm r1!, {r2, r3, r4} | R1=0x200000 M4@0x200000=1 M4@0x200004=2 M4@0x200008=3 | R2 R3 R4 R1
ldmib r1, {r2, r3} | R1=0x200000 M4@0x200004=1 M4@0x200008=2 | R2 R3 R1
ldmib r1!, {r2, r3} | R1=0x200000 M4@0x200004=1 M4@0x200008=2 | R2 R3 R1
ldmda r1, {r2, r3} | R1=0x200008 M4@0x200004=1 M4@0x200008=2 | R2 R3 R1
ldmda r1!, {r2, r3} | R1=0x200008 M4@0x200004=1 M4@0x200008=2 | R2 R3 R1
ldmdb r1, {r2, r3} | R1=0x200008 M4@0x200000=1 M4@0x200004=2 | R2 R3 R1
ldmdb r1!, {r2, r3} | R1=0x200008 M4@0x200000=1 M4@0x200004=2 | R2 R3 R1
ldm r1, {r1, r2} | R1=0x200000 M4@0x200000=1 M4@0x200004=2 | R1 R2
ldm r1!, {r2, pc} | R1=0x200000 M4@0x200000=1 M4@0x200004=0x20100 | R2 R1 PC | 0x100
ldmdb r1, {r2, lr, pc} | R1=0x20000c M4@0x200000=1 M4@0x200004=2 M4@0x200008=0x1fc00 | R2 LR PC | -0x400
stm r1, {r2, r3, r4} | R1=0x200000 R2=1 R3=2 R4=3 | M4@0x200000 M4@0x200004 M4@0x200008 R1
stm r1!, {r2, r3} | R1=0x200000 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stmib r1, {r2, r3} | R1=0x200000 R2=1 R3=2 | M4@0x200004 M4@0x200008 R1
stmib r1!, {r2, r3} | R1=0x200000 R2=1 R3=2 | M4@0x200004 M4@0x200008 R1
stmda r1, {r2, r3} | R1=0x200008 R2=1 R3=2 | M4@0x200004 M4@0x200008 R1
stmda r1!, {r2, r3} | R1=0x200008 R2=1 R3=2 | M4@0x200004 M4@0x200008 R1
stmdb r1, {r2, r3} | R1=0x200008 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stmdb r1!, {r2, r3} | R1=0x200008 R2=1 R3=2 | M4@0x200000 M4@0x200004 R1
stm r1, {r1, r2} | R1=0x200000 R2=2 | M4@0x200000 M4@0x200004
stm r1, {r2, lr} | R1=0x200000 R2=2 LR=0x12345678 | M4@0x200000 M4@0x200004
# the branches
b .+0x100 | | PC | 0x100
b .-0x400 | | PC | -0x400
beq .+0x100 | ZF | PC | 0x100
bgt .-0x400 | NF ZF VF | PC | -0x400
bl .+0x100 | | PC LR | 0x100
blne .-0x400 | ZF LR=0x55 | PC LR | -0x400
bx r1 | R1=0x20100 | PC | 0x100
bxeq r1 | R1=0x1fc00 ZF | PC | -0x400
bx lr | LR=0x20100 | PC | 0x100
bxne lr | LR=0x20100 ZF | PC | 0x100
blx r1 | R1=0x20100 | PC LR | 0x100
blxeq r1 | R1=0x1fc00 ZF LR=0x55 | PC LR | -0x400
# the branches to the T32 state, the bit 0 of the destination is not a
# part of the address
bx r1 | R1=0x20101 | PC | *0x100
bxeq r1 | R1=0x1fc01 ZF | PC | *-0x400
bx lr | LR=0x20101 | PC | *0x100
blx r1 | R1=0x20101 | PC LR | *0x100
blxne r1 | R1=0x1fc01 ZF LR=0x55 | PC LR | *-0x400
blx .+0x100 | | PC LR | *0x100
mov pc, lr | LR=0x20101 | PC | *0x100
mov pc, r1 | R1=0x1fc01 | PC | *-0x400
ldr pc, [r1] | R1=0x200000 M4@0x200000=0x20101 | PC | *0x100
ldm r1, {r2, pc} | R1=0x200000 M4@0x200000=1 M4@0x200004=0x1fc01 | R2 PC | *-0x400
# the status register and the other system instructions
mrs r0, apsr | NF ZF CF VF QF | R0
msr apsr_nzcvq, r0 | R0@flags | NF ZF CF VF QF
msr apsr_nzcvq, #0xa0000000 | | NF ZF CF VF QF
dmb ish | R0=1 | R0
dsb sy | R0=1 | R0
nop | R0=1 | R0
pld [r1, #4] | R0=1 R1=0x200000 | R0
