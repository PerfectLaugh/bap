# addition and subtraction
add rax, rbx | RAX RBX | RAX CF PF AF ZF SF OF
add eax, ebx | RAX RBX | RAX CF PF AF ZF SF OF
add ax, bx | RAX RBX | RAX CF PF AF ZF SF OF
add al, bl | RAX RBX | RAX CF PF AF ZF SF OF
add ah, bh | RAX RBX | RAX CF PF AF ZF SF OF
add rax, 0x7fffffff | RAX | RAX CF PF AF ZF SF OF
add rax, -1 | RAX | RAX CF PF AF ZF SF OF
add byte ptr [rbx], al | RAX RBX=0x200100 M8@0x200100 | M8@0x200100 CF ZF SF OF
add rax, qword ptr [rbx+rcx*8+8] | RAX RBX=0x200100 RCX=2 M8@0x200118 | RAX CF ZF SF OF
adc rax, rbx | RAX RBX CF | RAX CF PF AF ZF SF OF
adc eax, ebx | RAX RBX CF | RAX CF PF AF ZF SF OF
adc al, bl | RAX RBX CF | RAX CF PF AF ZF SF OF
sub rax, rbx | RAX RBX | RAX CF PF AF ZF SF OF
sub eax, ebx | RAX RBX | RAX CF PF AF ZF SF OF
sub ax, bx | RAX RBX | RAX CF PF AF ZF SF OF
sbb rax, rbx | RAX RBX CF | RAX CF PF AF ZF SF OF
sbb ax, bx | RAX RBX CF | RAX CF PF AF ZF SF OF
cmp rax, rbx | RAX RBX | CF PF AF ZF SF OF
cmp ecx, 0x80 | RCX | CF PF AF ZF SF OF
cmp byte ptr [rbx], 0x7f | RBX=0x200100 M1@0x200100@byte | CF PF AF ZF SF OF
neg rax | RAX | RAX CF PF AF ZF SF OF
neg ecx | RCX | RCX CF PF AF ZF SF OF
inc rax | RAX CF | RAX CF PF AF ZF SF OF
dec ax | RAX CF | RAX CF PF AF ZF SF OF
xadd rax, rbx | RAX RBX | RAX RBX CF PF AF ZF SF OF
# logical operations
and rax, rbx | RAX RBX | RAX CF PF ZF SF OF
or ecx, edx | RCX RDX | RCX CF PF ZF SF OF
xor ax, bx | RAX RBX | RAX CF PF ZF SF OF
xor eax, eax | RAX | RAX CF PF ZF SF OF
test rax, rbx | RAX RBX | CF PF ZF SF OF
test al, 0x80 | RAX | CF PF ZF SF OF
not rax | RAX | RAX
not cl | RCX | RCX
and rax, -0x100 | RAX | RAX CF ZF SF OF
# shifts and rotations
shl rax, cl | RAX RCX@count CF | RAX CF PF ZF SF
shr rax, cl | RAX RCX@count CF | RAX CF PF ZF SF
sar rax, cl | RAX RCX@count CF | RAX CF PF ZF SF
shl eax, cl | RAX RCX@count CF | RAX CF PF ZF SF
shr eax, cl | RAX RCX@count CF | RAX CF PF ZF SF
sar eax, cl | RAX RCX@count CF | RAX CF PF ZF SF
shl ax, cl | RAX RCX@byte CF | RAX PF ZF SF
sar al, cl | RAX RCX@byte CF | RAX PF ZF SF
shl rax, 1 | RAX CF | RAX CF PF ZF SF OF
shr rax, 1 | RAX CF | RAX CF PF ZF SF OF
sar eax, 1 | RAX CF | RAX CF PF ZF SF OF
shl rax, 63 | RAX | RAX CF PF ZF SF
shr eax, 31 | RAX | RAX CF PF ZF SF
sar rdx, 17 | RDX | RDX CF PF ZF SF
rol rax, cl | RAX RCX@count CF | RAX CF
ror rax, cl | RAX RCX@count CF | RAX CF
rol eax, cl | RAX RCX@count CF | RAX CF
ror ax, cl | RAX RCX@count CF | RAX
rol al, cl | RAX RCX@count CF | RAX
rol rax, 1 | RAX CF | RAX CF OF
ror eax, 1 | RAX CF | RAX CF OF
ror rax, 13 | RAX CF | RAX CF
rcl rax, 1 | RAX CF | RAX CF OF
rcr rax, 1 | RAX CF | RAX CF OF
rcl eax, cl | RAX RCX@count CF | RAX CF
rcr rax, cl | RAX RCX@count CF | RAX CF
shld rax, rbx, cl | RAX RBX RCX@count | RAX
shrd rax, rbx, cl | RAX RBX RCX@count | RAX
shld eax, ebx, 7 | RAX RBX | RAX CF PF ZF SF
shrd rax, rbx, 60 | RAX RBX | RAX CF PF ZF SF
# multiplication and division
mul rbx | RAX RBX RDX=5 | RAX RDX CF OF
mul ebx | RAX RBX RDX=5 | RAX RDX CF OF
mul bl | RAX RBX | RAX CF OF
imul rbx | RAX RBX | RAX RDX CF OF
imul ecx | RAX RCX | RAX RDX CF OF
imul rax, rbx | RAX RBX | RAX CF OF
imul eax, ebx, -3 | RAX RBX | RAX CF OF
imul ax, bx | RAX RBX | RAX CF OF
div rbx | RAX RDX=0 RBX@nz | RAX RDX
div rbx | RAX=0 RDX=1 RBX@nz | RAX RDX
div ecx | RAX RDX=0 RCX@nz32 | RAX RDX
div cl | RAX RCX@byte | RAX
idiv rbx | RAX RDX=0 RBX@nz | RAX RDX
idiv rbx | RAX RDX=0xffffffffffffffff RBX@nz | RAX RDX
idiv ecx | RAX RDX=0 RCX@nz32 | RAX RDX
idiv cl | RAX RCX@byte | RAX
# bit operations
bt rax, rbx | RAX RBX | CF
bts rax, rbx | RAX RBX | RAX CF
btr eax, ebx | RAX RBX | RAX CF
btc rax, 63 | RAX | RAX CF
bt dword ptr [rbx], 35 | RBX=0x200100 M8@0x200100 | CF
bsf rax, rbx | RAX=0 RBX@nz | RAX ZF
bsr rax, rbx | RAX=0 RBX@nz | RAX ZF
bsr ecx, edx | RCX=0 RDX@nz | RCX ZF
popcnt rax, rbx | RBX | RAX CF PF AF ZF SF OF
lzcnt rax, rbx | RBX | RAX CF ZF
tzcnt ecx, edx | RDX | RCX CF ZF
bswap rax | RAX | RAX
bswap ecx | RCX | RCX
# BMI
andn rax, rbx, rcx | RBX RCX | RAX ZF SF CF OF
blsi rax, rbx | RBX | RAX ZF SF CF OF
blsr rax, rbx | RBX | RAX ZF SF CF OF
blsmsk eax, ebx | RBX | RAX ZF SF CF OF
bzhi rax, rbx, rcx | RBX RCX@count | RAX ZF SF CF OF
bextr rax, rbx, rcx | RBX RCX=0x1004 | RAX ZF CF OF
pdep rax, rbx, rcx | RBX RCX | RAX
pext rax, rbx, rcx | RBX RCX | RAX
sarx rax, rbx, rcx | RBX RCX@count | RAX
shlx eax, ebx, ecx | RBX RCX@count | RAX
shrx rax, rbx, rcx | RBX RCX@count | RAX
rorx rax, rbx, 13 | RBX | RAX
mulx rax, rcx, rbx | RDX RBX | RAX RCX
adcx rax, rbx | RAX RBX CF OF | RAX CF OF
adox rax, rbx | RAX RBX CF OF | RAX CF OF
blsmsk rax, rbx | RBX | RAX ZF SF CF OF
blsr ecx, edx | RDX | RCX ZF SF CF OF
bzhi eax, ebx, ecx | RBX RCX@count | RAX ZF SF CF OF
bextr eax, ebx, ecx | RBX RCX=0x0c1c | RAX ZF CF OF
pdep eax, ebx, ecx | RBX RCX | RAX
pext eax, ebx, ecx | RBX RCX | RAX
rorx eax, ebx, 37 | RBX | RAX
mulx eax, ecx, ebx | RDX RBX | RAX RCX
mulx rax, rax, rbx | RDX RBX | RAX
adox eax, ebx | RAX RBX CF OF | RAX CF OF
# moves and extensions
movzx eax, bl | RAX RBX | RAX
movzx rax, bx | RAX RBX | RAX
movsx rax, bl | RAX RBX | RAX
movsx eax, bx | RAX RBX | RAX
movsxd rax, ebx | RAX RBX | RAX
mov al, bh | RAX RBX | RAX
mov eax, ebx | RAX RBX | RAX
mov ax, bx | RAX RBX | RAX
cbw | RAX | RAX
cwde | RAX | RAX
cdqe | RAX | RAX
cwd | RAX RDX | RAX RDX
cdq | RAX RDX | RDX
cqo | RAX RDX | RDX
xchg rax, rbx | RAX RBX | RAX RBX
xchg eax, ebx | RAX RBX | RAX RBX
xchg al, bl | RAX RBX | RAX RBX
cmpxchg rcx, rbx | RAX RBX RCX | RAX RCX ZF CF SF OF
cmpxchg rcx, rbx | RAX=5 RCX=5 RBX | RAX RCX ZF CF SF OF
cmpxchg ecx, ebx | RAX=0xffffffff00000005 RCX=5 RBX | RAX RCX ZF
lea rax, [rbx+rcx*4-8] | RBX RCX | RAX
lea eax, [rbx+rcx*2+0x10] | RBX RCX | RAX
mov rax, qword ptr [rbx+8] | RBX=0x200100 M8@0x200108 | RAX
mov dword ptr [rbx-4], eax | RAX RBX=0x200104 | M8@0x200100
movabs rax, 0x123456789abcdef0 | | RAX
# conditional moves and sets
cmovb rax, rbx | RAX=1 RBX=2 CF | RAX
cmovbe rax, rbx | RAX=1 RBX=2 CF ZF | RAX
cmovl eax, ebx | RAX=1 RBX=2 SF OF | RAX
cmovle rax, rbx | RAX=1 RBX=2 SF OF ZF | RAX
cmovg rax, rbx | RAX=1 RBX=2 SF OF ZF | RAX
cmovp rax, rbx | RAX=1 RBX=2 PF | RAX
cmovs eax, ebx | RAX=0xffffffff00000001 RBX=2 SF | RAX
setb al | RAX=0xff CF | RAX
seta cl | RCX CF ZF | RCX
setge al | RAX=0xffff SF OF | RAX
setle bl | RBX SF OF ZF | RBX
setnp al | RAX PF | RAX
# flags
stc | CF | CF
clc | CF | CF
cmc | CF | CF
lahf | RAX CF ZF SF PF | RAX
sahf | RAX@byte | CF PF AF ZF SF
# stack
push rbx | RBX | RSP M8@0x207ff8
pop rbx | M8@0x208000 | RBX RSP
push 0x7f | | RSP M8@0x207ff8
push -1 | | RSP M8@0x207ff8
leave | RBP=0x207000 M8@0x207000 | RSP RBP
# strings
movsb | RSI=0x200100 RDI=0x200200 M1@0x200100@byte | RSI RDI M1@0x200200
movsq | RSI=0x200100 RDI=0x200200 M8@0x200100 DF | RSI RDI M8@0x200200
stosd | RAX RDI=0x200200 DF | RDI M4@0x200200
lodsb | RAX RSI=0x200100 M1@0x200100@byte DF | RAX RSI
lodsw | RAX RSI=0x200100 M2@0x200100 | RAX RSI
lodsd | RAX RSI=0x200100 M4@0x200100=0x89abcdef DF | RAX RSI
lodsq | RAX RSI=0x200100 M8@0x200100 | RAX RSI
rep stosb | RAX@byte RCX@byte RDI=0x200200 | RCX RDI M8@0x200200 M8@0x200208
rep movsb | RCX=5 RSI=0x200100 RDI=0x200200 M8@0x200100 | RCX RSI RDI M8@0x200200
cmpsb | RSI=0x200100 RDI=0x200200 M1@0x200100@byte M1@0x200200@byte | RSI RDI CF ZF SF OF
scasb | RAX@byte RDI=0x200200 M1@0x200200@byte | RDI CF ZF SF OF
# SSE floating point, the default MXCSR rounds to nearest
addsd xmm0, xmm1 | XMM0 XMM1 | XMM0
subsd xmm0, xmm1 | XMM0 XMM1 | XMM0
mulsd xmm0, xmm1 | XMM0 XMM1 | XMM0
divsd xmm0, xmm1 | XMM0 XMM1 | XMM0
sqrtsd xmm0, xmm1 | XMM0 XMM1 | XMM0
minsd xmm0, xmm1 | XMM0 XMM1 | XMM0
maxsd xmm0, xmm1 | XMM0 XMM1 | XMM0
addss xmm0, xmm1 | XMM0 XMM1 | XMM0
subss xmm0, xmm1 | XMM0 XMM1 | XMM0
mulss xmm0, xmm1 | XMM0 XMM1 | XMM0
divss xmm0, xmm1 | XMM0 XMM1 | XMM0
sqrtss xmm0, xmm1 | XMM0 XMM1 | XMM0
minss xmm0, xmm1 | XMM0 XMM1 | XMM0
maxss xmm0, xmm1 | XMM0 XMM1 | XMM0
addpd xmm0, xmm1 | XMM0 XMM1 | XMM0
subpd xmm0, xmm1 | XMM0 XMM1 | XMM0
divps xmm0, xmm1 | XMM0 XMM1 | XMM0
sqrtpd xmm0, xmm1 | XMM0 XMM1 | XMM0
mulps xmm0, xmm1 | XMM0 XMM1 | XMM0
addsd xmm0, qword ptr [rbx] | XMM0 RBX=0x200100 M8@0x200100=0x4000000000000000 | XMM0
ucomisd xmm0, xmm1 | XMM0 XMM1 | ZF PF CF OF SF AF
comiss xmm0, xmm1 | XMM0 XMM1 | ZF PF CF OF SF AF
cvtsi2sd xmm0, rax | XMM0=0x1111111111111111 RAX | XMM0
cvtsi2sd xmm0, eax | XMM0=0 RAX | XMM0
cvtsi2ss xmm0, rax | XMM0=0 RAX | XMM0
cvttsd2si rax, xmm0 | XMM0 | RAX
cvttsd2si eax, xmm0 | XMM0 RAX | RAX
cvtsd2si rax, xmm0 | XMM0 | RAX
cvttss2si eax, xmm0 | XMM0 | RAX
cvtsd2ss xmm0, xmm1 | XMM0 XMM1 | XMM0
cvtss2sd xmm0, xmm1 | XMM0 XMM1 | XMM0
cvtsd2si eax, xmm0 | XMM0 RAX | RAX
cvtss2si rax, xmm0 | XMM0 | RAX
cvtps2pd xmm0, xmm1 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 0 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 2 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 4 | XMM0 XMM1 | XMM0
roundss xmm0, xmm1, 1 | XMM0 XMM1 | XMM0
roundss xmm0, xmm1, 3 | XMM0 XMM1 | XMM0
maxsd xmm0, qword ptr [rbx+rcx*8] | XMM0 RBX=0x200100 RCX=1 M8@0x200108=0xbff8000000000000 | XMM0
ucomisd xmm0, qword ptr [rbx] | XMM0 RBX=0x200100 M8@0x200100=0x3ff8000000000000 | ZF PF CF
andpd xmm0, xmm1 | XMM0 XMM1 | XMM0
xorps xmm0, xmm1 | XMM0 XMM1 | XMM0
andnpd xmm0, xmm1 | XMM0 XMM1 | XMM0
# SSE moves
movsd xmm0, xmm1 | XMM0 XMM1 | XMM0
movss xmm0, xmm1 | XMM0 XMM1 | XMM0
movq rax, xmm0 | XMM0 | RAX
movq xmm0, rax | XMM0 RAX | XMM0
movd eax, xmm0 | XMM0 RAX | RAX
movd xmm0, eax | XMM0 RAX | XMM0
movsd xmm0, qword ptr [rbx] | XMM0 RBX=0x200100 M8@0x200100 | XMM0
movsd qword ptr [rbx], xmm0 | XMM0 RBX=0x200100 | M8@0x200100 M8@0x200108
movups xmm0, xmmword ptr [rbx] | RBX=0x200100 M16@0x200100@vec | XMM0
movaps xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
movhlps xmm0, xmm1 | XMM0 XMM1 | XMM0
movlhps xmm0, xmm1 | XMM0 XMM1 | XMM0
unpcklps xmm0, xmm1 | XMM0 XMM1 | XMM0
unpckhpd xmm0, xmm1 | XMM0 XMM1 | XMM0
unpcklpd xmm0, xmm1 | XMM0 XMM1 | XMM0
unpckhps xmm0, xmm1 | XMM0 XMM1 | XMM0
shufpd xmm0, xmm1, 1 | XMM0 XMM1 | XMM0
shufpd xmm0, xmm1, 2 | XMM0 XMM1 | XMM0
shufps xmm0, xmm1, 0xe4 | XMM0 XMM1 | XMM0
shufps xmm0, xmm1, 0x1b | XMM0 XMM1 | XMM0
movmskpd eax, xmm0 | XMM0 RAX | RAX
movmskps eax, xmm0 | XMM0 RAX | RAX
# SSE integer
paddb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmullw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmuludq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaddwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pand xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pandn xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
por xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pxor xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminub xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psadbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packsswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packuswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packssdw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckldq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhqdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pshufd xmm0, xmm1, 0x1b | XMM1@vec | XMM0
pshuflw xmm0, xmm1, 0xb1 | XMM1@vec | XMM0
pshufhw xmm0, xmm1, 0x4e | XMM1@vec | XMM0
pshufb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psllw xmm0, 3 | XMM0@vec | XMM0
pslld xmm0, 31 | XMM0@vec | XMM0
psllq xmm0, 1 | XMM0@vec | XMM0
psrlw xmm0, 15 | XMM0@vec | XMM0
psrld xmm0, 4 | XMM0@vec | XMM0
psraw xmm0, 3 | XMM0@vec | XMM0
psrad xmm0, 31 | XMM0@vec | XMM0
psraw xmm0, 20 | XMM0@vec | XMM0
psrlw xmm0, 16 | XMM0@vec | XMM0
psllq xmm0, xmm1 | XMM0@vec XMM1=0x21 | XMM0
psrlq xmm0, xmm1 | XMM0@vec XMM1=0x40 | XMM0
pslldq xmm0, 3 | XMM0@vec | XMM0
psrldq xmm0, 9 | XMM0@vec | XMM0
pmovmskb eax, xmm0 | XMM0@vec RAX | RAX
pextrw eax, xmm0, 5 | XMM0@vec RAX | RAX
pinsrw xmm0, eax, 6 | XMM0@vec RAX | XMM0
pminsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulld xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
ptest xmm0, xmm1 | XMM0@vec XMM1@vec | ZF CF
pextrd eax, xmm0, 3 | XMM0@vec RAX | RAX
pinsrq xmm0, rax, 1 | XMM0@vec RAX | XMM0
pextrb eax, xmm0, 17 | XMM0@vec RAX | RAX
pextrq rax, xmm0, 1 | XMM0@vec | RAX
pinsrb xmm0, eax, 9 | XMM0@vec RAX | XMM0
pinsrd xmm0, eax, 2 | XMM0@vec RAX | XMM0
psraw xmm0, xmm1 | XMM0@vec XMM1=0x10 | XMM0
psrld xmm0, xmm1 | XMM0@vec XMM1=0x1f | XMM0
roundsd xmm0, xmm1, 1 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 3 | XMM0 XMM1 | XMM0
pcmpeqq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmovzxbw xmm0, xmm1 | XMM1@vec | XMM0
pmovsxwd xmm0, xmm1 | XMM1@vec | XMM0
palignr xmm0, xmm1, 5 | XMM0@vec XMM1@vec | XMM0
# AVX, the destination is not a source
vpsrlw xmm2, xmm1, 3 | XMM1@vec XMM2@vec | XMM2
vpsllq xmm2, xmm0, xmm1 | XMM0@vec XMM1=0x21 XMM2 | XMM2
vpminub xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | XMM2
vpavgb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | XMM2
vpand xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | XMM2
vpshufb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | XMM2
