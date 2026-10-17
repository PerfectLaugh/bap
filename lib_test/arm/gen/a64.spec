# arithmetic with carry
A64 | adc x0, x1, x2 | R1=0xffffffffffffffff R2=0 CF=1 | R0=0
A64 | adcs x0, x1, x2 | R1=0xffffffffffffffff R2=0 CF=1 | R0=0 NF=0 ZF=1 CF=1 VF=0
A64 | adcs x0, x1, x2 | R1=0x7fffffffffffffff R2=0 CF=1 | R0=0x8000000000000000 NF=1 ZF=0 CF=0 VF=1
A64 | adcs w0, w1, w2 | R1=0xffffffff R2=0 CF=1 | R0=0 ZF=1 CF=1
A64 | sbc x0, x1, x2 | R1=5 R2=3 CF=0 | R0=1
A64 | sbcs x0, x1, x2 | R1=0 R2=0 CF=0 | R0=0xffffffffffffffff NF=1 ZF=0 CF=0 VF=0
A64 | sbcs w0, w1, w2 | R1=0x80000000 R2=0 CF=0 | R0=0x7fffffff NF=0 ZF=0 CF=1 VF=1
A64 | ngc x0, x1 | R1=1 CF=1 | R0=0xffffffffffffffff
# extended register operands
A64 | adds x0, x1, w2, uxtw | R1=1 R2=0xffffffff80000000 | R0=0x80000001 NF=0 ZF=0 CF=0 VF=0
A64 | subs x0, x1, w2, sxtw #1 | R1=0 R2=0x80000000 | R0=0x100000000 NF=0 ZF=0 CF=0 VF=0
A64 | cmp x1, w2, sxtb | R1=0xffffffffffffffff R2=0xff | NF=0 ZF=1 CF=1 VF=0
A64 | sub w0, w1, w2, sxth | R1=0 R2=0x8000 | R0=0x8000
# bit counting and reversal
A64 | cls x0, x1 | R1=0xffff000000000000 | R0=15
A64 | cls w0, w1 | R1=1 | R0=30
A64 | rev x0, x1 | R1=0x0123456789abcdef | R0=0xefcdab8967452301
A64 | rev w0, w1 | R1=0xffffffff12345678 | R0=0x78563412
A64 | rev16 x0, x1 | R1=0x0123456789abcdef | R0=0x23016745ab89efcd
A64 | rev32 x0, x1 | R1=0x0123456789abcdef | R0=0x67452301efcdab89
A64 | extr x0, x1, x2, #8 | R1=0x11 R2=0x2233445566778899 | R0=0x1122334455667788
A64 | extr w0, w1, w2, #4 | R1=0xa R2=0x12345678 | R0=0xa1234567
# long and high multiplication
A64 | smulh x0, x1, x2 | R1=0xffffffffffffffff R2=2 | R0=0xffffffffffffffff
A64 | umulh x0, x1, x2 | R1=0xffffffffffffffff R2=2 | R0=1
A64 | smaddl x0, w1, w2, x3 | R1=0xffffffff R2=3 R3=10 | R0=7
A64 | umsubl x0, w1, w2, x3 | R1=0xffffffff R2=2 R3=0 | R0=0xfffffffe00000002
# the W-register writes clear the upper half
A64 | sub w0, w1, #4095 | R0=0xffffffffffffffff R1=0 | R0=0xfffff001
A64 | movn w0, #1 | R0=0xffffffffffffffff | R0=0xfffffffe
A64 | add w0, w1, #1 | R1=0xffffffff | R0=0
# extracts of the high bits
A64 | asr w0, w1, #31 | R1=0x80000000 | R0=0xffffffff
A64 | lsr x0, x1, #63 | R1=0x8000000000000000 | R0=1
A64 | ubfx x0, x1, #62, #2 | R1=0xc000000000000000 | R0=3
# bitfield moves
A64 | bfi x0, x1, #8, #16 | R0=0xffffffffffffffff R1=0 | R0=0xffffffffff0000ff
A64 | bfi w0, w1, #28, #4 | R0=0xffffffff R1=0 | R0=0x0fffffff
A64 | bfxil x0, x1, #20, #12 | R0=0 R1=0xfff00000 | R0=0xfff
A64 | bfc x0, #4, #40 | R0=0xffffffffffffffff | R0=0xfffff0000000000f
# conditional comparison
A64 | ccmp w1, w2, #0, eq | R1=0 R2=0x80000000 ZF=1 | NF=1 ZF=0 CF=0 VF=1
A64 | ccmp x1, #3, #5, ne | R1=0 ZF=1 | NF=0 ZF=1 CF=0 VF=1
A64 | ccmn w1, w2, #0, eq | R1=0x7fffffff R2=1 ZF=1 | NF=1 ZF=0 CF=0 VF=1
# logical operations with shifted operands
A64 | orn x0, x1, x2, asr #4 | R1=0 R2=0x8000000000000000 | R0=0x07ffffffffffffff
A64 | eon w0, w1, w2, ror #8 | R1=0 R2=0xff | R0=0x00ffffff
A64 | bics x0, x1, x2, lsr #60 | R1=0xf R2=0xf000000000000000 | R0=0 NF=0 ZF=1 CF=0 VF=0
# rotations by a register
A64 | ror x0, x1, x2 | R1=1 R2=65 | R0=0x8000000000000000
A64 | ror w0, w1, w2 | R1=0x80000001 R2=32 | R0=0x80000001
# loads and stores
A64 | ldrsb w0, [x1, #1] | R1=0x2000 M2@0x2000=0x8000 | R0=0xffffff80
A64 | ldrsh x0, [x1, #2] | R1=0x2000 M4@0x2000=0x80000000 | R0=0xffffffffffff8000
A64 | ldursw x0, [x1, #-4] | R1=0x2004 M4@0x2000=0xfffffffe | R0=0xfffffffffffffffe
A64 | ldr x0, [x1], #16 | R1=0x2000 M8@0x2000=0x1122334455667788 | R0=0x1122334455667788 R1=0x2010
A64 | ldr x0, [x1, #8]! | R1=0x2000 M8@0x2008=42 | R0=42 R1=0x2008
A64 | ldrh w0, [x1, #2]! | R1=0x2000 M4@0x2000=0xbeef0000 | R0=0xbeef R1=0x2002
A64 | ldrsw x0, [x1], #-4 | R1=0x2000 M4@0x2000=0x80000000 | R0=0xffffffff80000000 R1=0x1ffc
A64 | str x1, [x2], #8 | R1=7 R2=0x2000 | M8@0x2000=7 R2=0x2008
A64 | strh w1, [x2, #-2]! | R1=0x12345678 R2=0x2002 | M2@0x2000=0x5678 R2=0x2000
A64 | ldpsw x0, x1, [x2] | R2=0x2000 M8@0x2000=0x7fffffff80000000 | R0=0xffffffff80000000 R1=0x7fffffff
A64 | ldp w0, w1, [x2], #8 | R2=0x2000 M8@0x2000=0x0000000200000001 | R0=1 R1=2 R2=0x2008
A64 | ldp x0, x1, [x2, #16]! | R2=0x2000 M8@0x2010=1 M8@0x2018=2 | R0=1 R1=2 R2=0x2010
A64 | ldp x0, x1, [x0] | R0=0x2000 M8@0x2000=0x3000 M8@0x2008=7 | R0=0x3000 R1=7
A64 | stp x0, x1, [x2], #16 | R0=1 R1=2 R2=0x2000 | M8@0x2000=1 M8@0x2008=2 R2=0x2010
A64 | ldr x0, .+8 | M8@0x10008=0x123 | R0=0x123
A64 | ldrsw x0, .+4 | M4@0x10004=0x80000000 | R0=0xffffffff80000000
# exclusive and acquire-release loads and stores
A64 | ldxr x0, [x1] | R1=0x2000 M8@0x2000=5 | R0=5
A64 | stxr w0, x1, [x2] | R0=7 R1=9 R2=0x2000 | R0=0 M8@0x2000=9
A64 | ldaxr w0, [x1] | R1=0x2000 M4@0x2000=0x80000000 | R0=0x80000000
A64 | stlr w1, [x2] | R1=0xffffffff12345678 R2=0x2000 | M8@0x2000=0x12345678
A64 | ldarb w0, [x1] | R1=0x2000 M1@0x2000=0xff | R0=0xff
A64 | ldxp x0, x1, [x2] | R2=0x2000 M8@0x2000=1 M8@0x2008=2 | R0=1 R1=2
A64 | stxp w0, x1, x3, [x2] | R0=5 R1=1 R3=2 R2=0x2000 | R0=0 M8@0x2000=1 M8@0x2008=2
