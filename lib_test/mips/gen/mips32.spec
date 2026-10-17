# arithmetic, ADD, ADDI and SUB trap on overflow
add $2, $4, $5 | R4 R5 | R2
addi $2, $4, -3 | R4 | R2
addi $2, $4, 0x7fff | R4 | R2
addiu $2, $4, -1 | R4 | R2
addiu $2, $4, 0x7fff | R4 | R2
addu $2, $4, $5 | R4 R5 | R2
addu $2, $0, $5 | R5 | R2
addu $0, $4, $5 | R2=0x55 R4 R5 | R2
sub $2, $4, $5 | R4 R5 | R2
subu $2, $4, $5 | R4 R5 | R2
slt $2, $4, $5 | R4 R5 | R2
slti $2, $4, -1 | R4 | R2
slti $2, $4, 0x7f | R4 | R2
sltiu $2, $4, -1 | R4 | R2
sltiu $2, $4, 0x80 | R4 | R2
sltu $2, $4, $5 | R4 R5 | R2
lui $2, 0x8001 | R2 | R2
lui $2, 0x1234 | R2 | R2
# logical operations, the immediates are zero-extended
and $2, $4, $5 | R4 R5 | R2
andi $2, $4, 0x8001 | R4 | R2
or $2, $4, $5 | R4 R5 | R2
ori $2, $4, 0xff00 | R4 | R2
xor $2, $4, $5 | R4 R5 | R2
xori $2, $4, 0xffff | R4 | R2
nor $2, $4, $5 | R4 R5 | R2
# shifts and rotations
sll $2, $4, 5 | R4 | R2
sll $2, $4, 31 | R4 | R2
sllv $2, $4, $5 | R4 R5@count | R2
sra $2, $4, 7 | R4 | R2
srav $2, $4, $5 | R4 R5@count | R2
srl $2, $4, 1 | R4 | R2
srlv $2, $4, $5 | R4 R5@count | R2
rotr $2, $4, 9 | R4 | R2
rotrv $2, $4, $5 | R4 R5@count | R2
nop | R2 | R2
# multiplication and division
mult $4, $5 | R4 R5 | HI LO
multu $4, $5 | R4 R5 | HI LO
div $0, $4, $5 | R4 R5@nz | HI LO
divu $0, $4, $5 | R4 R5@nz | HI LO
mfhi $2 | HI | R2
mflo $2 | LO | R2
mthi $4 | R4 | HI
mtlo $4 | R4 | LO
mul $2, $4, $5 | R4 R5 | R2
madd $4, $5 | R4 R5 HI=0x12345678 LO=0xffffffff9abcdef0 | HI LO
maddu $4, $5 | R4 R5 HI=0x12345678 LO=0xffffffff9abcdef0 | HI LO
msub $4, $5 | R4 R5 HI=0x12345678 LO=0xffffffff9abcdef0 | HI LO
msubu $4, $5 | R4 R5 HI=0x12345678 LO=0xffffffff9abcdef0 | HI LO
# bit operations
clz $2, $4 | R4 | R2
clo $2, $4 | R4 | R2
seb $2, $4 | R4 | R2
seh $2, $4 | R4 | R2
wsbh $2, $4 | R4 | R2
ext $2, $4, 3, 5 | R4 | R2
ext $2, $4, 0, 32 | R4 | R2
ext $2, $4, 16, 16 | R4 | R2
ins $2, $4, 3, 5 | R2 R4 | R2
ins $2, $4, 0, 32 | R2 R4 | R2
ins $2, $4, 24, 8 | R2 R4 | R2
movn $2, $4, $5 | R2=0x55 R4 R5 | R2
movz $2, $4, $5 | R2=0x55 R4 R5 | R2
# loads, the base is R4
lb $2, 1($4) | R4=0x200100 M1@0x200101@byte | R2
lbu $2, -1($4) | R4=0x200100 M1@0x2000ff@byte | R2
lh $2, 2($4) | R4=0x200100 M2@0x200102 | R2
lhu $2, 2($4) | R4=0x200100 M2@0x200102 | R2
lw $2, 4($4) | R4=0x200100 M4@0x200104 | R2
lw $2, -4($4) | R4=0x200104 M4@0x200100 | R2
lwl $2, 0($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | R2
lwl $2, 1($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | R2
lwl $2, 2($4) | R2 R4=0x200100 M4@0x200100=0x81223344 | R2
lwl $2, 3($4) | R2 R4=0x200100 M4@0x200100=0x11223384 | R2
lwr $2, 0($4) | R2 R4=0x200100 M4@0x200100=0x81223344 | R2
lwr $2, 1($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | R2
lwr $2, 2($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | R2
lwr $2, 3($4) | R2 R4=0x200100 M4@0x200100=0x81223384 | R2
ll $2, 4($4) | R4=0x200100 M4@0x200104 | R2
# SC and SCD, which fail without a reservation, are not tested, as a
# reservation needs LL in the same test
# stores
sb $2, 1($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
sh $2, 2($4) | R2 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
sw $2, 4($4) | R2 R4=0x200100 | M4@0x200104 M4@0x200100
swl $2, 0($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swl $2, 1($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swl $2, 2($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swl $2, 3($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swr $2, 0($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swr $2, 1($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swr $2, 2($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
swr $2, 3($4) | R2=0x55667788 R4=0x200100 M4@0x200100=0x11223344 | M4@0x200100
# branches, the landings are the offsets of the targets
beq $4, $5, .+0x400 | R4 R5 | PC | 0x400
beq $4, $5, .-0x400 | R4 R5 | PC | -0x400
bne $4, $5, .+0x400 | R4 R5 | PC | 0x400
bgez $4, .+0x400 | R4 | PC | 0x400
bgtz $4, .+0x400 | R4 | PC | 0x400
blez $4, .+0x400 | R4 | PC | 0x400
bltz $4, .+0x400 | R4 | PC | 0x400
bgezal $4, .+0x400 | R4 | PC R31 | 0x400
bltzal $4, .+0x400 | R4 | PC R31 | 0x400
bal .+0x400 | | PC R31 | 0x400
b .-0x800 | | PC | -0x800
beql $4, $5, .+0x400 | R4 R5 | PC | 0x400
bnel $4, $5, .+0x400 | R4 R5 | PC | 0x400
bgezl $4, .+0x400 | R4 | PC | 0x400
bgtzl $4, .+0x400 | R4 | PC | 0x400
blezl $4, .+0x400 | R4 | PC | 0x400
bltzl $4, .+0x400 | R4 | PC | 0x400
j 0x20400 | | PC | 0x400
jal 0x20400 | | PC R31 | 0x400
jr $5 | R5=0x20400 | PC | 0x400
jalr $5 | R5=0x1f000 | PC R31 | -0x1000
jalr $6, $5 | R5=0x20400 R31=0x55 | PC R6 R31 | 0x400
# no effects on the registers
sync | R2 | R2
ehb | R2 | R2
# the traps, the vectors where they trap are dropped
teq $4, $5 | R2=0x55 R4 R5 | R2
tne $4, $5 | R2=0x55 R4 R5 | R2
