# addition and subtraction, the record forms set CR0 and the overflow-enabled forms OV
add 3,4,5 | R4 R5 | R3
add. 3,4,5 | R4 R5 SO | R3 CR0LT CR0GT CR0EQ CR0UN
addo 3,4,5 | R4 R5 SO | R3 SO OV OV32
addo. 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32 CR0LT CR0GT CR0EQ CR0UN
addi 3,4,-3 | R4 | R3
addi 3,4,0x7fff | R4 | R3
li 3,-5 | R3 | R3
li 3,0x7fff | R3 | R3
addis 3,4,-1 | R4 | R3
addis 3,4,0x7fff | R4 | R3
lis 3,-32768 | R3 | R3
lis 3,0x1234 | R3 | R3
addic 3,4,-1 | R4 | R3 CA CA32
addic 3,4,1 | R4 | R3 CA CA32
addic. 3,4,1 | R4 SO=1 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
addc 3,4,5 | R4 R5 | R3 CA CA32
addc. 3,4,5 | R4 R5 SO=0 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
addco 3,4,5 | R4 R5 SO=0 | R3 CA CA32 SO OV OV32
adde 3,4,5 | R4 R5 CA | R3 CA CA32
adde. 3,4,5 | R4 R5 CA SO=0 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
addeo 3,4,5 | R4 R5 CA SO=0 | R3 CA CA32 SO OV OV32
addme 3,4 | R4 CA | R3 CA CA32
addmeo 3,4 | R4 CA SO=0 | R3 CA CA32 SO OV OV32
addze 3,4 | R4 CA | R3 CA CA32
addzeo. 3,4 | R4 CA SO=0 | R3 CA CA32 SO OV OV32 CR0LT CR0GT CR0EQ CR0UN
subf 3,4,5 | R4 R5 | R3
subf. 3,4,5 | R4 R5 SO=1 | R3 CR0LT CR0GT CR0EQ CR0UN
subfo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
subfic 3,4,5 | R4 | R3 CA CA32
subfic 3,4,-1 | R4 | R3 CA CA32
subfc 3,4,5 | R4 R5 | R3 CA CA32
subfco. 3,4,5 | R4 R5 SO=0 | R3 CA CA32 SO OV OV32 CR0LT CR0GT CR0EQ CR0UN
subfe 3,4,5 | R4 R5 CA | R3 CA CA32
subfeo 3,4,5 | R4 R5 CA SO=0 | R3 CA CA32 SO OV OV32
subfme 3,4 | R4 CA | R3 CA CA32
subfmeo 3,4 | R4 CA SO=0 | R3 CA CA32 SO OV OV32
subfze 3,4 | R4 CA | R3 CA CA32
subfzeo 3,4 | R4 CA SO=0 | R3 CA CA32 SO OV OV32
neg 3,4 | R4 | R3
neg. 3,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
nego 3,4 | R4 SO=0 | R3 SO OV OV32
# multiplication
mulli 3,4,-7 | R4 | R3
mulli 3,4,0x7fff | R4 | R3
mullw 3,4,5 | R4 R5 | R3
mullw. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
mullwo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
mulhw 3,4,5 | R4 R5 | R3
mulhwu 3,4,5 | R4 R5 | R3
# division, the invalid divisions are tested too
divw 3,4,5 | R4 R5 | R3
divw. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
divwo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
divwu 3,4,5 | R4 R5 | R3
divwuo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
divwe 3,4,5 | R4 R5 | R3
divweo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
divweu 3,4,5 | R4 R5 | R3
divweuo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
modsw 3,4,5 | R4 R5 | R3
moduw 3,4,5 | R4 R5 | R3
# logical operations, the immediates are zero-extended
and 3,4,5 | R4 R5 | R3
and. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
andc 3,4,5 | R4 R5 | R3
andi. 3,4,0x8001 | R4 SO | R3 CR0LT CR0GT CR0EQ CR0UN
andis. 3,4,0x8001 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
or 3,4,5 | R4 R5 | R3
or. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
orc 3,4,5 | R4 R5 | R3
ori 3,4,0xff00 | R4 | R3
oris 3,4,0xff00 | R4 | R3
xor 3,4,5 | R4 R5 | R3
xori 3,4,0xffff | R4 | R3
xoris 3,4,0x8000 | R4 | R3
nand 3,4,5 | R4 R5 | R3
nor 3,4,5 | R4 R5 | R3
nor. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
eqv 3,4,5 | R4 R5 | R3
nop | R3 | R3
mr 3,4 | R4 | R3
extsb 3,4 | R4 | R3
extsb. 3,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
extsh 3,4 | R4 | R3
cntlzw 3,4 | R4 | R3
cntlzw. 3,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
cnttzw 3,4 | R4 | R3
cmpb 3,4,5 | R4 R5 | R3
cmpb 3,4,5 | R4=0x11223344 R5=0x11003344 | R3
popcntb 3,4 | R4 | R3
popcntw 3,4 | R4 | R3
# rotations of words, the masks wrap around if MB > ME
rlwinm 3,4,5,6,7 | R4 | R3
rlwinm 3,4,0,0,31 | R4 | R3
rlwinm 3,4,8,24,7 | R4 | R3
rlwinm. 3,4,31,1,31 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
rlwnm 3,4,5,0,31 | R4 R5@count | R3
rlwnm 3,4,5,16,3 | R4 R5@count | R3
rlwimi 3,4,5,6,7 | R3 R4 | R3
rlwimi 3,4,8,24,7 | R3 R4 | R3
rlwimi. 3,4,0,16,31 | R3 R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
# shifts of words, the amounts have 6 bits
slw 3,4,5 | R4 R5@count | R3
slw. 3,4,5 | R4 R5@count SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
srw 3,4,5 | R4 R5@count | R3
srawi 3,4,5 | R4 | R3 CA CA32
srawi 3,4,0 | R4 | R3 CA CA32
srawi 3,4,31 | R4 | R3 CA CA32
srawi. 3,4,4 | R4 SO=0 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
sraw 3,4,5 | R4 R5@count | R3 CA CA32
sraw. 3,4,5 | R4 R5@count SO=0 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
# comparisons
cmpw 3,4 | R3 R4 SO | CR0LT CR0GT CR0EQ CR0UN
cmpw 2,3,4 | R3 R4 SO=1 CR0LT=1 | CR2LT CR2GT CR2EQ CR2UN CR0LT
cmpwi 3,-5 | R3 SO=0 | CR0LT CR0GT CR0EQ CR0UN
cmpwi 7,3,0x7fff | R3 SO=1 | CR7LT CR7GT CR7EQ CR7UN
cmplw 3,4 | R3 R4 SO=0 | CR0LT CR0GT CR0EQ CR0UN
cmplwi 3,0xffff | R3 SO=0 | CR0LT CR0GT CR0EQ CR0UN
cmplwi 5,3,0x80 | R3 SO=1 | CR5LT CR5GT CR5EQ CR5UN
# the operations on the bits of the condition register
crand 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
crnand 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
cror 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
crxor 31,0,13 | CR7UN=0 CR0LT CR3GT | CR7UN
crnor 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
creqv 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
crandc 1,2,3 | CR0GT=0 CR0EQ CR0UN | CR0GT
crorc 9,2,3 | CR2GT=0 CR0EQ CR0UN | CR2GT
mcrf 1,2 | CR2LT CR2GT CR2EQ CR2UN=1 CR1LT=1 | CR1LT CR1GT CR1EQ CR1UN
mfcr 3 | R3 CR0LT=1 CR1GT=1 CR3EQ=1 CR7UN=1 CR7LT | R3
mtcrf 0xff,3 | R3 | CR0LT CR0GT CR0EQ CR0UN CR1LT CR3EQ CR6GT CR7UN
mtcrf 0x81,3 | R3 CR1LT=1 | CR0LT CR0GT CR0EQ CR0UN CR1LT CR7LT CR7UN
mtocrf 0x08,3 | R3 CR0LT=1 | CR4LT CR4GT CR4EQ CR4UN CR0LT
mfocrf 3,0x08 | R3=0x55 CR4LT CR4UN CR0LT=1 | R3
isel 3,4,5,2 | R4 R5=0x55 CR0EQ | R3
isel 3,0,5,30 | R5 CR7EQ | R3
# special purpose registers
mfxer 3 | SO OV CA | R3
mtxer 3 | R3 | SO OV CA OV32 CA32
mflr 3 | LR | R3
mtlr 3 | R3 | LR
mfctr 3 | CTR | R3
mtctr 3 | R3 | CTR
# loads, the base is R4, or R5 if R4 is 0
lbz 3,1(4) | R4=0x200100 M1@0x200101 | R3
lhz 3,2(4) | R4=0x200100 M2@0x200102 | R3
lha 3,2(4) | R4=0x200100 M2@0x200102 | R3
lwz 3,-4(4) | R4=0x200104 M4@0x200100 | R3
lbzx 3,4,5 | R4=0x200000 R5=0x100 M1@0x200100 | R3
lbzx 3,0,5 | R5=0x200100 M1@0x200100 | R3
lhzx 3,4,5 | R4=0x200000 R5=0x100 M2@0x200100 | R3
lhax 3,4,5 | R4=0x200000 R5=0x100 M2@0x200100 | R3
lwzx 3,4,5 | R4=0x200000 R5=0x100 M4@0x200100 | R3
lbzu 3,1(4) | R4=0x200100 M1@0x200101 | R3 R4
lhzu 3,2(4) | R4=0x200100 M2@0x200102 | R3 R4
lhau 3,-2(4) | R4=0x200102 M2@0x200100 | R3 R4
lwzu 3,4(4) | R4=0x200100 M4@0x200104 | R3 R4
lbzux 3,4,5 | R4=0x200000 R5=0x100 M1@0x200100 | R3 R4
lhzux 3,4,5 | R4=0x200000 R5=0x100 M2@0x200100 | R3 R4
lhaux 3,4,5 | R4=0x200000 R5=0x100 M2@0x200100 | R3 R4
lwzux 3,4,5 | R4=0x200000 R5=0x100 M4@0x200100 | R3 R4
lhbrx 3,4,5 | R4=0x200000 R5=0x100 M2@0x200100 | R3
lwbrx 3,4,5 | R4=0x200000 R5=0x100 M4@0x200100 | R3
lwarx 3,0,4 | R4=0x200100 M4@0x200100 | R3
# stores
stb 3,1(4) | R3 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
sth 3,2(4) | R3 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
stw 3,4(4) | R3 R4=0x200100 | M4@0x200104
stbx 3,4,5 | R3 R4=0x200000 R5=0x100 M4@0x200100=0x11223344 | M4@0x200100
sthx 3,0,5 | R3 R5=0x200100 M4@0x200100=0x11223344 | M4@0x200100
stwx 3,4,5 | R3 R4=0x200000 R5=0x100 | M4@0x200100
stbu 3,1(4) | R3 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100 R4
sthu 3,2(4) | R3 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100 R4
stwu 3,-4(4) | R3 R4=0x200104 | M4@0x200100 R4
stbux 3,4,5 | R3 R4=0x200000 R5=0x100 M4@0x200100=0x11223344 | M4@0x200100 R4
sthux 3,4,5 | R3 R4=0x200000 R5=0x100 M4@0x200100=0x11223344 | M4@0x200100 R4
stwux 3,4,5 | R3 R4=0x200000 R5=0x100 | M4@0x200100 R4
sthbrx 3,4,5 | R3 R4=0x200000 R5=0x100 | M2@0x200100
stwbrx 3,4,5 | R3 R4=0x200000 R5=0x100 | M4@0x200100
# branches, the landings are the offsets of the targets
b .+0x400 | | PC | 0x400
b .-0x400 | | PC | -0x400
ba 0x20400 | | PC | 0x400
bl .+0x400 | | PC LR | 0x400
bla 0x20400 | | PC LR | 0x400
beq .+0x400 | CR0EQ | PC | 0x400
bne 2,.-0x400 | CR2EQ | PC | -0x400
blt .+0x400 | CR0LT | PC | 0x400
bge 7,.+0x400 | CR7LT | PC | 0x400
bso .+0x400 | CR0UN | PC | 0x400
beq+ .+0x400 | CR0EQ | PC | 0x400
beql .+0x400 | CR0EQ | PC LR | 0x400
bdnz .+0x400 | CTR | PC CTR | 0x400
bdz .+0x400 | CTR | PC CTR | 0x400
bdnzt 2,.+0x400 | CTR CR0EQ | PC CTR | 0x400
bdzf 2,.+0x400 | CTR CR0EQ | PC CTR | 0x400
bdnzl .+0x400 | CTR | PC CTR LR | 0x400
bdnz+ .+0x400 | CTR | PC CTR | 0x400
bdz- .+0x400 | CTR | PC CTR | 0x400
blr | LR@lr | PC | 0x400
blrl | LR@lr | PC LR | 0x400
bctr | CTR@lr | PC | 0x400
bctrl | CTR@lr | PC LR | 0x400
beqlr | LR=0x20400 CR0EQ | PC | 0x400
bnelrl | LR=0x20400 CR0EQ | PC LR | 0x400
beqctr | CTR=0x1fc00 CR0EQ | PC | -0x400
bnectrl 1 | CTR=0x1fc00 CR1EQ | PC LR | -0x400
bdnzlr | LR=0x20400 CTR | PC CTR | 0x400
bdzlr | LR=0x20400 CTR | PC CTR | 0x400
bdnzlrl | LR=0x20400 CTR | PC CTR LR | 0x400
# traps, the vectors where they trap are dropped
tw 16,3,4 | R3 R4 | R3
tw 3,3,4 | R3 R4 | R3
twi 4,3,0 | R3 | R3
# no effects on the registers
sync | R3 | R3
lwsync | R3 | R3
isync | R3 | R3
eieio | R3 | R3
dcbt 0,3 | R3=0x200100 | R3
dcbf 0,3 | R3=0x200100 | R3
dcbst 0,3 | R3=0x200100 | R3
icbi 0,3 | R3=0x200100 | R3
