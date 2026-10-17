# multiplication and division of doublewords
mulld 3,4,5 | R4 R5 | R3
mulld. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
mulldo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
mulhd 3,4,5 | R4 R5 | R3
mulhdu 3,4,5 | R4 R5 | R3
divd 3,4,5 | R4 R5 | R3
divd. 3,4,5 | R4 R5 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
divdo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
divdu 3,4,5 | R4 R5 | R3
divduo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
# QEMU misses most overflows of DIVDE, whose results are undefined, so
# the quotients fit a doubleword, but for the division by zero
divde 3,4,5 | R4@dds R5@dd | R3
divdeo 3,4,5 | R4@dds R5@dd SO=0 | R3 SO OV OV32
divdeu 3,4,5 | R4 R5 | R3
divdeuo 3,4,5 | R4 R5 SO=0 | R3 SO OV OV32
modsd 3,4,5 | R4 R5 | R3
modud 3,4,5 | R4 R5 | R3
# operations on doublewords
extsw 3,4 | R4 | R3
extsw. 3,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
extswsli 3,4,5 | R4 | R3
extswsli 3,4,40 | R4 | R3
cntlzd 3,4 | R4 | R3
cntlzd. 3,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
cnttzd 3,4 | R4 | R3
popcntd 3,4 | R4 | R3
bpermd 3,4,5 | R4@sel R5 | R3
# rotations of doublewords, the masks wrap around if MB > ME
rldicl 3,4,5,6 | R4 | R3
rldicl 3,4,0,32 | R4 | R3
rldicl. 3,4,60,4 | R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
rldicr 3,4,5,6 | R4 | R3
rldicr 3,4,8,55 | R4 | R3
rldic 3,4,5,6 | R4 | R3
rldic 3,4,8,60 | R4 | R3
rldcl 3,4,5,6 | R4 R5@count | R3
rldcr 3,4,5,60 | R4 R5@count | R3
rldimi 3,4,5,6 | R3 R4 | R3
rldimi 3,4,40,10 | R3 R4 | R3
rldimi. 3,4,8,60 | R3 R4 SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
# shifts of doublewords, the amounts have 7 bits
sld 3,4,5 | R4 R5@count | R3
sld. 3,4,5 | R4 R5@count SO=0 | R3 CR0LT CR0GT CR0EQ CR0UN
srd 3,4,5 | R4 R5@count | R3
srad 3,4,5 | R4 R5@count | R3 CA CA32
srad. 3,4,5 | R4 R5@count SO=0 | R3 CA CA32 CR0LT CR0GT CR0EQ CR0UN
sradi 3,4,5 | R4 | R3 CA CA32
sradi 3,4,0 | R4 | R3 CA CA32
sradi 3,4,63 | R4 | R3 CA CA32
# comparisons of doublewords
cmpd 3,4 | R3 R4 SO | CR0LT CR0GT CR0EQ CR0UN
cmpdi 3,-5 | R3 SO=0 | CR0LT CR0GT CR0EQ CR0UN
cmpld 6,3,4 | R3 R4 SO=1 | CR6LT CR6GT CR6EQ CR6UN
cmpldi 3,0xffff | R3 SO=0 | CR0LT CR0GT CR0EQ CR0UN
# the other instructions of POWER9
mcrxrx 1 | OV OV32 CA CA32 | CR1LT CR1GT CR1EQ CR1UN
setb 3,1 | CR1LT CR1GT | R3
addpcis 3,1 | | R3
addpcis 3,-1 | | R3
# loads and stores of doublewords
ld 3,8(4) | R4=0x200100 M8@0x200108 | R3
ld 3,-8(4) | R4=0x200108 M8@0x200100 | R3
ldx 3,4,5 | R4=0x200000 R5=0x100 M8@0x200100 | R3
ldu 3,8(4) | R4=0x200100 M8@0x200108 | R3 R4
ldux 3,4,5 | R4=0x200000 R5=0x100 M8@0x200100 | R3 R4
ldbrx 3,4,5 | R4=0x200000 R5=0x100 M8@0x200100 | R3
ldarx 3,0,4 | R4=0x200100 M8@0x200100 | R3
lwa 3,4(4) | R4=0x200100 M4@0x200104 | R3
lwax 3,4,5 | R4=0x200000 R5=0x100 M4@0x200100 | R3
lwaux 3,4,5 | R4=0x200000 R5=0x100 M4@0x200100 | R3 R4
std 3,8(4) | R3 R4=0x200100 | M8@0x200108
stdx 3,4,5 | R3 R4=0x200000 R5=0x100 | M8@0x200100
stdu 3,-8(4) | R3 R4=0x200108 | M8@0x200100 R4
stdux 3,4,5 | R3 R4=0x200000 R5=0x100 | M8@0x200100 R4
stdbrx 3,4,5 | R3 R4=0x200000 R5=0x100 | M8@0x200100
# traps of doublewords, the vectors where they trap are dropped
td 16,3,4 | R3 R4 | R3
tdi 4,3,5 | R3 | R3
