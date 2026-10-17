# 64-bit arithmetic, DADD and DADDI trap on overflow
dadd $2, $4, $5 | R4 R5 | R2
daddi $2, $4, -3 | R4 | R2
daddiu $2, $4, -1 | R4 | R2
daddiu $2, $4, 0x7fff | R4 | R2
daddu $2, $4, $5 | R4 R5 | R2
dsub $2, $4, $5 | R4 R5 | R2
dsubu $2, $4, $5 | R4 R5 | R2
# 64-bit shifts and rotations
dsll $2, $4, 5 | R4 | R2
dsll32 $2, $4, 5 | R4 | R2
dsllv $2, $4, $5 | R4 R5@count | R2
dsra $2, $4, 7 | R4 | R2
dsra32 $2, $4, 3 | R4 | R2
dsrav $2, $4, $5 | R4 R5@count | R2
dsrl $2, $4, 1 | R4 | R2
dsrl32 $2, $4, 0 | R4 | R2
dsrlv $2, $4, $5 | R4 R5@count | R2
drotr $2, $4, 9 | R4 | R2
drotr32 $2, $4, 9 | R4 | R2
drotrv $2, $4, $5 | R4 R5@count | R2
# 64-bit multiplication and division
dmult $4, $5 | R4 R5 | HI LO
dmultu $4, $5 | R4 R5 | HI LO
ddiv $0, $4, $5 | R4 R5@nz | HI LO
ddivu $0, $4, $5 | R4 R5@nz | HI LO
# 64-bit bit operations
dclz $2, $4 | R4 | R2
dclo $2, $4 | R4 | R2
dsbh $2, $4 | R4 | R2
dshd $2, $4 | R4 | R2
dext $2, $4, 3, 5 | R4 | R2
dext $2, $4, 0, 32 | R4 | R2
dextm $2, $4, 3, 40 | R4 | R2
dextu $2, $4, 35, 5 | R4 | R2
dins $2, $4, 3, 5 | R2 R4 | R2
dinsm $2, $4, 3, 40 | R2 R4 | R2
dinsu $2, $4, 35, 5 | R2 R4 | R2
# 64-bit loads and stores
ld $2, 8($4) | R4=0x200100 M8@0x200108 | R2
lwu $2, 4($4) | R4=0x200100 M4@0x200104 | R2
ldl $2, 0($4) | R2 R4=0x200100 M8@0x200100=0x1122334455667788 | R2
ldl $2, 3($4) | R2 R4=0x200100 M8@0x200100=0x1122334455667788 | R2
ldl $2, 7($4) | R2 R4=0x200100 M8@0x200100=0x8122334455667788 | R2
ldr $2, 0($4) | R2 R4=0x200100 M8@0x200100=0x8122334455667788 | R2
ldr $2, 5($4) | R2 R4=0x200100 M8@0x200100=0x1122334455667788 | R2
ldr $2, 7($4) | R2 R4=0x200100 M8@0x200100=0x1122334455667788 | R2
sd $2, 8($4) | R2 R4=0x200100 | M8@0x200108
sdl $2, 0($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
sdl $2, 3($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
sdl $2, 7($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
sdr $2, 0($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
sdr $2, 5($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
sdr $2, 7($4) | R2=0x99aabbccddeeff00 R4=0x200100 M8@0x200100=0x1122334455667788 | M8@0x200100
lld $2, 8($4) | R4=0x200100 M8@0x200108 | R2
