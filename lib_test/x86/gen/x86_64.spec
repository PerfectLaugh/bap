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
# the forms of the arithmetic and logical operations, the memory is at 0x200100
add cl, dl | RCX RDX  | RCX CF PF AF ZF SF OF
add cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  | RCX CF PF AF ZF SF OF
add byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
add cl, 0x81 | RCX  | RCX CF PF AF ZF SF OF
add byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
add al, 0x81 | RAX  | RAX CF PF AF ZF SF OF
add cx, dx | RCX RDX  | RCX CF PF AF ZF SF OF
add cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  | RCX CF PF AF ZF SF OF
add word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add cx, 0x8001 | RCX  | RCX CF PF AF ZF SF OF
add cx, -3 | RCX  | RCX CF PF AF ZF SF OF
add word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add ax, 0x8001 | RAX  | RAX CF PF AF ZF SF OF
add ecx, edx | RCX RDX  | RCX CF PF AF ZF SF OF
add ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  | RCX CF PF AF ZF SF OF
add dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add ecx, 0x80000001 | RCX  | RCX CF PF AF ZF SF OF
add ecx, -3 | RCX  | RCX CF PF AF ZF SF OF
add dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add eax, 0x80000001 | RAX  | RAX CF PF AF ZF SF OF
add rcx, rdx | RCX RDX  | RCX CF PF AF ZF SF OF
add rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  | RCX CF PF AF ZF SF OF
add qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
add rcx, -0x7ffffff0 | RCX  | RCX CF PF AF ZF SF OF
add rcx, -3 | RCX  | RCX CF PF AF ZF SF OF
add qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
add qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
add rax, -0x7ffffff0 | RAX  | RAX CF PF AF ZF SF OF
add ah, ch | RAX RCX  | RAX CF PF AF ZF SF OF
adc cl, dl | RCX RDX CF | RCX CF PF AF ZF SF OF
adc cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 CF | RCX CF PF AF ZF SF OF
adc byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
adc cl, 0x81 | RCX CF | RCX CF PF AF ZF SF OF
adc byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
adc al, 0x81 | RAX CF | RAX CF PF AF ZF SF OF
adc cx, dx | RCX RDX CF | RCX CF PF AF ZF SF OF
adc cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 CF | RCX CF PF AF ZF SF OF
adc word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc cx, 0x8001 | RCX CF | RCX CF PF AF ZF SF OF
adc cx, -3 | RCX CF | RCX CF PF AF ZF SF OF
adc word ptr [rbx], -3 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc ax, 0x8001 | RAX CF | RAX CF PF AF ZF SF OF
adc ecx, edx | RCX RDX CF | RCX CF PF AF ZF SF OF
adc ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100 CF | RCX CF PF AF ZF SF OF
adc dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc ecx, 0x80000001 | RCX CF | RCX CF PF AF ZF SF OF
adc ecx, -3 | RCX CF | RCX CF PF AF ZF SF OF
adc dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc eax, 0x80000001 | RAX CF | RAX CF PF AF ZF SF OF
adc rcx, rdx | RCX RDX CF | RCX CF PF AF ZF SF OF
adc rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100 CF | RCX CF PF AF ZF SF OF
adc qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
adc rcx, -0x7ffffff0 | RCX CF | RCX CF PF AF ZF SF OF
adc rcx, -3 | RCX CF | RCX CF PF AF ZF SF OF
adc qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
adc qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
adc rax, -0x7ffffff0 | RAX CF | RAX CF PF AF ZF SF OF
adc ah, ch | RAX RCX CF | RAX CF PF AF ZF SF OF
sub cl, dl | RCX RDX  | RCX CF PF AF ZF SF OF
sub cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  | RCX CF PF AF ZF SF OF
sub byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
sub cl, 0x81 | RCX  | RCX CF PF AF ZF SF OF
sub byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
sub al, 0x81 | RAX  | RAX CF PF AF ZF SF OF
sub cx, dx | RCX RDX  | RCX CF PF AF ZF SF OF
sub cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  | RCX CF PF AF ZF SF OF
sub word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub cx, 0x8001 | RCX  | RCX CF PF AF ZF SF OF
sub cx, -3 | RCX  | RCX CF PF AF ZF SF OF
sub word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub ax, 0x8001 | RAX  | RAX CF PF AF ZF SF OF
sub ecx, edx | RCX RDX  | RCX CF PF AF ZF SF OF
sub ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  | RCX CF PF AF ZF SF OF
sub dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub ecx, 0x80000001 | RCX  | RCX CF PF AF ZF SF OF
sub ecx, -3 | RCX  | RCX CF PF AF ZF SF OF
sub dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub eax, 0x80000001 | RAX  | RAX CF PF AF ZF SF OF
sub rcx, rdx | RCX RDX  | RCX CF PF AF ZF SF OF
sub rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  | RCX CF PF AF ZF SF OF
sub qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
sub rcx, -0x7ffffff0 | RCX  | RCX CF PF AF ZF SF OF
sub rcx, -3 | RCX  | RCX CF PF AF ZF SF OF
sub qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
sub qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF AF ZF SF OF
sub rax, -0x7ffffff0 | RAX  | RAX CF PF AF ZF SF OF
sub ah, ch | RAX RCX  | RAX CF PF AF ZF SF OF
sbb cl, dl | RCX RDX CF | RCX CF PF AF ZF SF OF
sbb cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 CF | RCX CF PF AF ZF SF OF
sbb byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
sbb cl, 0x81 | RCX CF | RCX CF PF AF ZF SF OF
sbb byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
sbb al, 0x81 | RAX CF | RAX CF PF AF ZF SF OF
sbb cx, dx | RCX RDX CF | RCX CF PF AF ZF SF OF
sbb cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 CF | RCX CF PF AF ZF SF OF
sbb word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb cx, 0x8001 | RCX CF | RCX CF PF AF ZF SF OF
sbb cx, -3 | RCX CF | RCX CF PF AF ZF SF OF
sbb word ptr [rbx], -3 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb ax, 0x8001 | RAX CF | RAX CF PF AF ZF SF OF
sbb ecx, edx | RCX RDX CF | RCX CF PF AF ZF SF OF
sbb ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100 CF | RCX CF PF AF ZF SF OF
sbb dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb ecx, 0x80000001 | RCX CF | RCX CF PF AF ZF SF OF
sbb ecx, -3 | RCX CF | RCX CF PF AF ZF SF OF
sbb dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb eax, 0x80000001 | RAX CF | RAX CF PF AF ZF SF OF
sbb rcx, rdx | RCX RDX CF | RCX CF PF AF ZF SF OF
sbb rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100 CF | RCX CF PF AF ZF SF OF
sbb qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
sbb rcx, -0x7ffffff0 | RCX CF | RCX CF PF AF ZF SF OF
sbb rcx, -3 | RCX CF | RCX CF PF AF ZF SF OF
sbb qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
sbb qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
sbb rax, -0x7ffffff0 | RAX CF | RAX CF PF AF ZF SF OF
sbb ah, ch | RAX RCX CF | RAX CF PF AF ZF SF OF
and cl, dl | RCX RDX  | RCX CF PF ZF SF OF
and cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  | RCX CF PF ZF SF OF
and byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
and cl, 0x81 | RCX  | RCX CF PF ZF SF OF
and byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
and al, 0x81 | RAX  | RAX CF PF ZF SF OF
and cx, dx | RCX RDX  | RCX CF PF ZF SF OF
and cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  | RCX CF PF ZF SF OF
and word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and cx, 0x8001 | RCX  | RCX CF PF ZF SF OF
and cx, -3 | RCX  | RCX CF PF ZF SF OF
and word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and ax, 0x8001 | RAX  | RAX CF PF ZF SF OF
and ecx, edx | RCX RDX  | RCX CF PF ZF SF OF
and ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  | RCX CF PF ZF SF OF
and dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and ecx, 0x80000001 | RCX  | RCX CF PF ZF SF OF
and ecx, -3 | RCX  | RCX CF PF ZF SF OF
and dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and eax, 0x80000001 | RAX  | RAX CF PF ZF SF OF
and rcx, rdx | RCX RDX  | RCX CF PF ZF SF OF
and rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  | RCX CF PF ZF SF OF
and qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
and rcx, -0x7ffffff0 | RCX  | RCX CF PF ZF SF OF
and rcx, -3 | RCX  | RCX CF PF ZF SF OF
and qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
and qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
and rax, -0x7ffffff0 | RAX  | RAX CF PF ZF SF OF
and ah, ch | RAX RCX  | RAX CF PF ZF SF OF
or cl, dl | RCX RDX  | RCX CF PF ZF SF OF
or cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  | RCX CF PF ZF SF OF
or byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
or cl, 0x81 | RCX  | RCX CF PF ZF SF OF
or byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
or al, 0x81 | RAX  | RAX CF PF ZF SF OF
or cx, dx | RCX RDX  | RCX CF PF ZF SF OF
or cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  | RCX CF PF ZF SF OF
or word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or cx, 0x8001 | RCX  | RCX CF PF ZF SF OF
or cx, -3 | RCX  | RCX CF PF ZF SF OF
or word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or ax, 0x8001 | RAX  | RAX CF PF ZF SF OF
or ecx, edx | RCX RDX  | RCX CF PF ZF SF OF
or ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  | RCX CF PF ZF SF OF
or dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or ecx, 0x80000001 | RCX  | RCX CF PF ZF SF OF
or ecx, -3 | RCX  | RCX CF PF ZF SF OF
or dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or eax, 0x80000001 | RAX  | RAX CF PF ZF SF OF
or rcx, rdx | RCX RDX  | RCX CF PF ZF SF OF
or rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  | RCX CF PF ZF SF OF
or qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
or rcx, -0x7ffffff0 | RCX  | RCX CF PF ZF SF OF
or rcx, -3 | RCX  | RCX CF PF ZF SF OF
or qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
or qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
or rax, -0x7ffffff0 | RAX  | RAX CF PF ZF SF OF
or ah, ch | RAX RCX  | RAX CF PF ZF SF OF
xor cl, dl | RCX RDX  | RCX CF PF ZF SF OF
xor cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  | RCX CF PF ZF SF OF
xor byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
xor cl, 0x81 | RCX  | RCX CF PF ZF SF OF
xor byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
xor al, 0x81 | RAX  | RAX CF PF ZF SF OF
xor cx, dx | RCX RDX  | RCX CF PF ZF SF OF
xor cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  | RCX CF PF ZF SF OF
xor word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor cx, 0x8001 | RCX  | RCX CF PF ZF SF OF
xor cx, -3 | RCX  | RCX CF PF ZF SF OF
xor word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor ax, 0x8001 | RAX  | RAX CF PF ZF SF OF
xor ecx, edx | RCX RDX  | RCX CF PF ZF SF OF
xor ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  | RCX CF PF ZF SF OF
xor dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor ecx, 0x80000001 | RCX  | RCX CF PF ZF SF OF
xor ecx, -3 | RCX  | RCX CF PF ZF SF OF
xor dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor eax, 0x80000001 | RAX  | RAX CF PF ZF SF OF
xor rcx, rdx | RCX RDX  | RCX CF PF ZF SF OF
xor rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  | RCX CF PF ZF SF OF
xor qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
xor rcx, -0x7ffffff0 | RCX  | RCX CF PF ZF SF OF
xor rcx, -3 | RCX  | RCX CF PF ZF SF OF
xor qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
xor qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  | M8@0x200100 CF PF ZF SF OF
xor rax, -0x7ffffff0 | RAX  | RAX CF PF ZF SF OF
xor ah, ch | RAX RCX  | RAX CF PF ZF SF OF
cmp cl, dl | RCX RDX  |  CF PF AF ZF SF OF
cmp cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp cl, 0x81 | RCX  |  CF PF AF ZF SF OF
cmp byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp al, 0x81 | RAX  |  CF PF AF ZF SF OF
cmp cx, dx | RCX RDX  |  CF PF AF ZF SF OF
cmp cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp cx, 0x8001 | RCX  |  CF PF AF ZF SF OF
cmp cx, -3 | RCX  |  CF PF AF ZF SF OF
cmp word ptr [rbx], -3 | RBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp ax, 0x8001 | RAX  |  CF PF AF ZF SF OF
cmp ecx, edx | RCX RDX  |  CF PF AF ZF SF OF
cmp ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp ecx, 0x80000001 | RCX  |  CF PF AF ZF SF OF
cmp ecx, -3 | RCX  |  CF PF AF ZF SF OF
cmp dword ptr [rbx], -3 | RBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp eax, 0x80000001 | RAX  |  CF PF AF ZF SF OF
cmp rcx, rdx | RCX RDX  |  CF PF AF ZF SF OF
cmp rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100  |  CF PF AF ZF SF OF
cmp qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  |  CF PF AF ZF SF OF
cmp rcx, -0x7ffffff0 | RCX  |  CF PF AF ZF SF OF
cmp rcx, -3 | RCX  |  CF PF AF ZF SF OF
cmp qword ptr [rbx], -3 | RBX=0x200100 M8@0x200100  |  CF PF AF ZF SF OF
cmp qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  |  CF PF AF ZF SF OF
cmp rax, -0x7ffffff0 | RAX  |  CF PF AF ZF SF OF
cmp ah, ch | RAX RCX  |  CF PF AF ZF SF OF
test cl, dl | RCX RDX  |  CF PF ZF SF OF
test byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100  |  CF PF ZF SF OF
test cl, 0x81 | RCX  |  CF PF ZF SF OF
test byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100  |  CF PF ZF SF OF
test al, 0x81 | RAX  |  CF PF ZF SF OF
test cx, dx | RCX RDX  |  CF PF ZF SF OF
test word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100  |  CF PF ZF SF OF
test cx, 0x8001 | RCX  |  CF PF ZF SF OF
test word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100  |  CF PF ZF SF OF
test ax, 0x8001 | RAX  |  CF PF ZF SF OF
test ecx, edx | RCX RDX  |  CF PF ZF SF OF
test dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100  |  CF PF ZF SF OF
test ecx, 0x80000001 | RCX  |  CF PF ZF SF OF
test dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100  |  CF PF ZF SF OF
test eax, 0x80000001 | RAX  |  CF PF ZF SF OF
test rcx, rdx | RCX RDX  |  CF PF ZF SF OF
test qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100  |  CF PF ZF SF OF
test rcx, -0x7ffffff0 | RCX  |  CF PF ZF SF OF
test qword ptr [rbx], -0x7ffffff0 | RBX=0x200100 M8@0x200100  |  CF PF ZF SF OF
test rax, -0x7ffffff0 | RAX  |  CF PF ZF SF OF
test ah, ch | RAX RCX  |  CF PF ZF SF OF
# the unary operations
inc cl | RCX CF | RCX PF AF ZF SF OF CF
inc byte ptr [rbx] | RBX=0x200100 M1@0x200100 CF | M1@0x200100 PF AF ZF SF OF CF
inc cx | RCX CF | RCX PF AF ZF SF OF CF
inc word ptr [rbx] | RBX=0x200100 M2@0x200100 CF | M2@0x200100 PF AF ZF SF OF CF
inc ecx | RCX CF | RCX PF AF ZF SF OF CF
inc dword ptr [rbx] | RBX=0x200100 M4@0x200100 CF | M4@0x200100 PF AF ZF SF OF CF
inc rcx | RCX CF | RCX PF AF ZF SF OF CF
inc qword ptr [rbx] | RBX=0x200100 M8@0x200100 CF | M8@0x200100 PF AF ZF SF OF CF
dec cl | RCX CF | RCX PF AF ZF SF OF CF
dec byte ptr [rbx] | RBX=0x200100 M1@0x200100 CF | M1@0x200100 PF AF ZF SF OF CF
dec cx | RCX CF | RCX PF AF ZF SF OF CF
dec word ptr [rbx] | RBX=0x200100 M2@0x200100 CF | M2@0x200100 PF AF ZF SF OF CF
dec ecx | RCX CF | RCX PF AF ZF SF OF CF
dec dword ptr [rbx] | RBX=0x200100 M4@0x200100 CF | M4@0x200100 PF AF ZF SF OF CF
dec rcx | RCX CF | RCX PF AF ZF SF OF CF
dec qword ptr [rbx] | RBX=0x200100 M8@0x200100 CF | M8@0x200100 PF AF ZF SF OF CF
neg cl | RCX CF | RCX CF PF AF ZF SF OF
neg byte ptr [rbx] | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
neg cx | RCX CF | RCX CF PF AF ZF SF OF
neg word ptr [rbx] | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
neg ecx | RCX CF | RCX CF PF AF ZF SF OF
neg dword ptr [rbx] | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
neg rcx | RCX CF | RCX CF PF AF ZF SF OF
neg qword ptr [rbx] | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF PF AF ZF SF OF
not cl | RCX CF | RCX 
not byte ptr [rbx] | RBX=0x200100 M1@0x200100 CF | M1@0x200100 
not cx | RCX CF | RCX 
not word ptr [rbx] | RBX=0x200100 M2@0x200100 CF | M2@0x200100 
not ecx | RCX CF | RCX 
not dword ptr [rbx] | RBX=0x200100 M4@0x200100 CF | M4@0x200100 
not rcx | RCX CF | RCX 
not qword ptr [rbx] | RBX=0x200100 M8@0x200100 CF | M8@0x200100 
# the multiplications and the divisions, the divisions by zero fault
mul cl | RAX RCX RDX@nzhigh | RAX CF OF
mul byte ptr [rbx] | RAX RBX=0x200100 M1@0x200100 RDX@nzhigh | RAX CF OF
mul cx | RAX RCX RDX@nzhigh | RAX RDX CF OF
mul word ptr [rbx] | RAX RBX=0x200100 M2@0x200100 RDX@nzhigh | RAX RDX CF OF
mul ecx | RAX RCX RDX@nzhigh | RAX RDX CF OF
mul dword ptr [rbx] | RAX RBX=0x200100 M4@0x200100 RDX@nzhigh | RAX RDX CF OF
mul rcx | RAX RCX RDX@nzhigh | RAX RDX CF OF
mul qword ptr [rbx] | RAX RBX=0x200100 M8@0x200100 RDX@nzhigh | RAX RDX CF OF
imul cl | RAX RCX RDX@nzhigh | RAX CF OF
imul byte ptr [rbx] | RAX RBX=0x200100 M1@0x200100 RDX@nzhigh | RAX CF OF
imul cx | RAX RCX RDX@nzhigh | RAX RDX CF OF
imul word ptr [rbx] | RAX RBX=0x200100 M2@0x200100 RDX@nzhigh | RAX RDX CF OF
imul ecx | RAX RCX RDX@nzhigh | RAX RDX CF OF
imul dword ptr [rbx] | RAX RBX=0x200100 M4@0x200100 RDX@nzhigh | RAX RDX CF OF
imul rcx | RAX RCX RDX@nzhigh | RAX RDX CF OF
imul qword ptr [rbx] | RAX RBX=0x200100 M8@0x200100 RDX@nzhigh | RAX RDX CF OF
div cl | RAX RCX RDX@nzhigh | RAX 
div byte ptr [rbx] | RAX RBX=0x200100 M1@0x200100 RDX@nzhigh | RAX 
div cx | RAX RCX RDX@nzhigh | RAX RDX 
div word ptr [rbx] | RAX RBX=0x200100 M2@0x200100 RDX@nzhigh | RAX RDX 
div ecx | RAX RCX RDX@nzhigh | RAX RDX 
div dword ptr [rbx] | RAX RBX=0x200100 M4@0x200100 RDX@nzhigh | RAX RDX 
div rcx | RAX RCX RDX@nzhigh | RAX RDX 
div qword ptr [rbx] | RAX RBX=0x200100 M8@0x200100 RDX@nzhigh | RAX RDX 
idiv cl | RAX RCX RDX@nzhigh | RAX 
idiv byte ptr [rbx] | RAX RBX=0x200100 M1@0x200100 RDX@nzhigh | RAX 
idiv cx | RAX RCX RDX@nzhigh | RAX RDX 
idiv word ptr [rbx] | RAX RBX=0x200100 M2@0x200100 RDX@nzhigh | RAX RDX 
idiv ecx | RAX RCX RDX@nzhigh | RAX RDX 
idiv dword ptr [rbx] | RAX RBX=0x200100 M4@0x200100 RDX@nzhigh | RAX RDX 
idiv rcx | RAX RCX RDX@nzhigh | RAX RDX 
idiv qword ptr [rbx] | RAX RBX=0x200100 M8@0x200100 RDX@nzhigh | RAX RDX 
imul cx, dx | RCX RDX | RCX CF OF
imul cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX CF OF
imul cx, dx, -7 | RDX | RCX CF OF
imul cx, dx, 0x1234 | RDX | RCX CF OF
imul cx, word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 | RCX CF OF
imul cx, word ptr [rbx], 0x1234 | RBX=0x200100 M2@0x200100 | RCX CF OF
imul ecx, edx | RCX RDX | RCX CF OF
imul ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100 | RCX CF OF
imul ecx, edx, -7 | RDX | RCX CF OF
imul ecx, edx, 0x1234 | RDX | RCX CF OF
imul ecx, dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 | RCX CF OF
imul ecx, dword ptr [rbx], 0x1234 | RBX=0x200100 M4@0x200100 | RCX CF OF
imul rcx, rdx | RCX RDX | RCX CF OF
imul rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100 | RCX CF OF
imul rcx, rdx, -7 | RDX | RCX CF OF
imul rcx, rdx, 0x1234 | RDX | RCX CF OF
imul rcx, qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 | RCX CF OF
imul rcx, qword ptr [rbx], 0x1234 | RBX=0x200100 M8@0x200100 | RCX CF OF
cbw | RAX RDX | RAX RDX
cwde | RAX RDX | RAX RDX
cwd | RAX RDX | RAX RDX
cdq | RAX RDX | RAX RDX
cdqe | RAX RDX | RAX RDX
cqo | RAX RDX | RAX RDX
# the shifts and the rotations of each size and form
shl dl, cl | RDX RCX@count CF | RDX CF
shl dl, 1 | RDX CF | RDX CF OF
shl dl, 3 | RDX CF | RDX CF
shl byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
shl byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
shl byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
shl dx, cl | RDX RCX@count CF | RDX CF
shl dx, 1 | RDX CF | RDX CF OF
shl dx, 3 | RDX CF | RDX CF
shl word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
shl word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
shl word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
shl edx, cl | RDX RCX@count CF | RDX CF
shl edx, 1 | RDX CF | RDX CF OF
shl edx, 3 | RDX CF | RDX CF
shl dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
shl dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
shl dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
shl rdx, cl | RDX RCX@count CF | RDX CF
shl rdx, 1 | RDX CF | RDX CF OF
shl rdx, 3 | RDX CF | RDX CF
shl qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
shl qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
shl qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
shr dl, cl | RDX RCX@count CF | RDX CF
shr dl, 1 | RDX CF | RDX CF OF
shr dl, 3 | RDX CF | RDX CF
shr byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
shr byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
shr byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
shr dx, cl | RDX RCX@count CF | RDX CF
shr dx, 1 | RDX CF | RDX CF OF
shr dx, 3 | RDX CF | RDX CF
shr word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
shr word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
shr word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
shr edx, cl | RDX RCX@count CF | RDX CF
shr edx, 1 | RDX CF | RDX CF OF
shr edx, 3 | RDX CF | RDX CF
shr dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
shr dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
shr dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
shr rdx, cl | RDX RCX@count CF | RDX CF
shr rdx, 1 | RDX CF | RDX CF OF
shr rdx, 3 | RDX CF | RDX CF
shr qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
shr qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
shr qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
sar dl, cl | RDX RCX@count CF | RDX CF
sar dl, 1 | RDX CF | RDX CF OF
sar dl, 3 | RDX CF | RDX CF
sar byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
sar byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
sar byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
sar dx, cl | RDX RCX@count CF | RDX CF
sar dx, 1 | RDX CF | RDX CF OF
sar dx, 3 | RDX CF | RDX CF
sar word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
sar word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
sar word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
sar edx, cl | RDX RCX@count CF | RDX CF
sar edx, 1 | RDX CF | RDX CF OF
sar edx, 3 | RDX CF | RDX CF
sar dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
sar dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
sar dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
sar rdx, cl | RDX RCX@count CF | RDX CF
sar rdx, 1 | RDX CF | RDX CF OF
sar rdx, 3 | RDX CF | RDX CF
sar qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
sar qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
sar qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
rol dl, cl | RDX RCX@count CF | RDX CF
rol dl, 1 | RDX CF | RDX CF OF
rol dl, 3 | RDX CF | RDX CF
rol byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
rol byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rol byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rol dx, cl | RDX RCX@count CF | RDX CF
rol dx, 1 | RDX CF | RDX CF OF
rol dx, 3 | RDX CF | RDX CF
rol word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
rol word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rol word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rol edx, cl | RDX RCX@count CF | RDX CF
rol edx, 1 | RDX CF | RDX CF OF
rol edx, 3 | RDX CF | RDX CF
rol dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
rol dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rol dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rol rdx, cl | RDX RCX@count CF | RDX CF
rol rdx, 1 | RDX CF | RDX CF OF
rol rdx, 3 | RDX CF | RDX CF
rol qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
rol qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
rol qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
ror dl, cl | RDX RCX@count CF | RDX CF
ror dl, 1 | RDX CF | RDX CF OF
ror dl, 3 | RDX CF | RDX CF
ror byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
ror byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
ror byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
ror dx, cl | RDX RCX@count CF | RDX CF
ror dx, 1 | RDX CF | RDX CF OF
ror dx, 3 | RDX CF | RDX CF
ror word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
ror word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
ror word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
ror edx, cl | RDX RCX@count CF | RDX CF
ror edx, 1 | RDX CF | RDX CF OF
ror edx, 3 | RDX CF | RDX CF
ror dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
ror dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
ror dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
ror rdx, cl | RDX RCX@count CF | RDX CF
ror rdx, 1 | RDX CF | RDX CF OF
ror rdx, 3 | RDX CF | RDX CF
ror qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
ror qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
ror qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
rcl dl, cl | RDX RCX@count CF | RDX CF
rcl dl, 1 | RDX CF | RDX CF OF
rcl dl, 3 | RDX CF | RDX CF
rcl byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
rcl byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rcl byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rcl dx, cl | RDX RCX@count CF | RDX CF
rcl dx, 1 | RDX CF | RDX CF OF
rcl dx, 3 | RDX CF | RDX CF
rcl word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
rcl word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rcl word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rcl edx, cl | RDX RCX@count CF | RDX CF
rcl edx, 1 | RDX CF | RDX CF OF
rcl edx, 3 | RDX CF | RDX CF
rcl dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
rcl dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rcl dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rcl rdx, cl | RDX RCX@count CF | RDX CF
rcl rdx, 1 | RDX CF | RDX CF OF
rcl rdx, 3 | RDX CF | RDX CF
rcl qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
rcl qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
rcl qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
rcr dl, cl | RDX RCX@count CF | RDX CF
rcr dl, 1 | RDX CF | RDX CF OF
rcr dl, 3 | RDX CF | RDX CF
rcr byte ptr [rbx], cl | RBX=0x200100 M1@0x200100 RCX@count CF | M1@0x200100 CF
rcr byte ptr [rbx], 1 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rcr byte ptr [rbx], 5 | RBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rcr dx, cl | RDX RCX@count CF | RDX CF
rcr dx, 1 | RDX CF | RDX CF OF
rcr dx, 3 | RDX CF | RDX CF
rcr word ptr [rbx], cl | RBX=0x200100 M2@0x200100 RCX@count CF | M2@0x200100 CF
rcr word ptr [rbx], 1 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rcr word ptr [rbx], 5 | RBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rcr edx, cl | RDX RCX@count CF | RDX CF
rcr edx, 1 | RDX CF | RDX CF OF
rcr edx, 3 | RDX CF | RDX CF
rcr dword ptr [rbx], cl | RBX=0x200100 M4@0x200100 RCX@count CF | M4@0x200100 CF
rcr dword ptr [rbx], 1 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rcr dword ptr [rbx], 5 | RBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rcr rdx, cl | RDX RCX@count CF | RDX CF
rcr rdx, 1 | RDX CF | RDX CF OF
rcr rdx, 3 | RDX CF | RDX CF
rcr qword ptr [rbx], cl | RBX=0x200100 M8@0x200100 RCX@count CF | M8@0x200100 CF
rcr qword ptr [rbx], 1 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF OF
rcr qword ptr [rbx], 5 | RBX=0x200100 M8@0x200100 CF | M8@0x200100 CF
shld dx, ax, cl | RDX RAX RCX@count16 | RDX CF ZF SF PF
shld dx, ax, 7 | RDX RAX | RDX CF ZF SF PF
shld dx, ax, 1 | RDX RAX | RDX CF OF ZF SF PF
shld word ptr [rbx], ax, cl | RBX=0x200100 M2@0x200100 RAX RCX@count16 | M2@0x200100 CF ZF
shld word ptr [rbx], ax, 9 | RBX=0x200100 M2@0x200100 RAX | M2@0x200100 CF ZF
shld edx, eax, cl | RDX RAX RCX@count | RDX CF ZF SF PF
shld edx, eax, 7 | RDX RAX | RDX CF ZF SF PF
shld edx, eax, 1 | RDX RAX | RDX CF OF ZF SF PF
shld dword ptr [rbx], eax, cl | RBX=0x200100 M4@0x200100 RAX RCX@count | M4@0x200100 CF ZF
shld dword ptr [rbx], eax, 9 | RBX=0x200100 M4@0x200100 RAX | M4@0x200100 CF ZF
shld rdx, rax, cl | RDX RAX RCX@count | RDX CF ZF SF PF
shld rdx, rax, 7 | RDX RAX | RDX CF ZF SF PF
shld rdx, rax, 1 | RDX RAX | RDX CF OF ZF SF PF
shld qword ptr [rbx], rax, cl | RBX=0x200100 M8@0x200100 RAX RCX@count | M8@0x200100 CF ZF
shld qword ptr [rbx], rax, 9 | RBX=0x200100 M8@0x200100 RAX | M8@0x200100 CF ZF
shrd dx, ax, cl | RDX RAX RCX@count16 | RDX CF ZF SF PF
shrd dx, ax, 7 | RDX RAX | RDX CF ZF SF PF
shrd dx, ax, 1 | RDX RAX | RDX CF OF ZF SF PF
shrd word ptr [rbx], ax, cl | RBX=0x200100 M2@0x200100 RAX RCX@count16 | M2@0x200100 CF ZF
shrd word ptr [rbx], ax, 9 | RBX=0x200100 M2@0x200100 RAX | M2@0x200100 CF ZF
shrd edx, eax, cl | RDX RAX RCX@count | RDX CF ZF SF PF
shrd edx, eax, 7 | RDX RAX | RDX CF ZF SF PF
shrd edx, eax, 1 | RDX RAX | RDX CF OF ZF SF PF
shrd dword ptr [rbx], eax, cl | RBX=0x200100 M4@0x200100 RAX RCX@count | M4@0x200100 CF ZF
shrd dword ptr [rbx], eax, 9 | RBX=0x200100 M4@0x200100 RAX | M4@0x200100 CF ZF
shrd rdx, rax, cl | RDX RAX RCX@count | RDX CF ZF SF PF
shrd rdx, rax, 7 | RDX RAX | RDX CF ZF SF PF
shrd rdx, rax, 1 | RDX RAX | RDX CF OF ZF SF PF
shrd qword ptr [rbx], rax, cl | RBX=0x200100 M8@0x200100 RAX RCX@count | M8@0x200100 CF ZF
shrd qword ptr [rbx], rax, 9 | RBX=0x200100 M8@0x200100 RAX | M8@0x200100 CF ZF
# the bit tests, the register offsets of the memory forms address a bit string
bt dx, cx | RDX RCX@count |  CF
bt dx, 37 | RDX |  CF
bt word ptr [rbx], cx | RBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 RCX@bitoff |  CF
bt word ptr [rbx], 3 | RBX=0x200100 M2@0x200100 |  CF
bt edx, ecx | RDX RCX@count |  CF
bt edx, 37 | RDX |  CF
bt dword ptr [rbx], ecx | RBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 RCX@bitoff |  CF
bt dword ptr [rbx], 3 | RBX=0x200100 M4@0x200100 |  CF
bt rdx, rcx | RDX RCX@count |  CF
bt rdx, 37 | RDX |  CF
bt qword ptr [rbx], rcx | RBX=0x200100 M8@0x2000f0 M8@0x200100 M8@0x200110 RCX@bitoff |  CF
bt qword ptr [rbx], 3 | RBX=0x200100 M8@0x200100 |  CF
bts dx, cx | RDX RCX@count | RDX CF
bts dx, 37 | RDX | RDX CF
bts word ptr [rbx], cx | RBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 RCX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
bts word ptr [rbx], 3 | RBX=0x200100 M2@0x200100 | M2@0x200100 CF
bts edx, ecx | RDX RCX@count | RDX CF
bts edx, 37 | RDX | RDX CF
bts dword ptr [rbx], ecx | RBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 RCX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
bts dword ptr [rbx], 3 | RBX=0x200100 M4@0x200100 | M4@0x200100 CF
bts rdx, rcx | RDX RCX@count | RDX CF
bts rdx, 37 | RDX | RDX CF
bts qword ptr [rbx], rcx | RBX=0x200100 M8@0x2000f0 M8@0x200100 M8@0x200110 RCX@bitoff | M8@0x2000f0 M8@0x200100 M8@0x200110 CF
bts qword ptr [rbx], 3 | RBX=0x200100 M8@0x200100 | M8@0x200100 CF
btr dx, cx | RDX RCX@count | RDX CF
btr dx, 37 | RDX | RDX CF
btr word ptr [rbx], cx | RBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 RCX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
btr word ptr [rbx], 3 | RBX=0x200100 M2@0x200100 | M2@0x200100 CF
btr edx, ecx | RDX RCX@count | RDX CF
btr edx, 37 | RDX | RDX CF
btr dword ptr [rbx], ecx | RBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 RCX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
btr dword ptr [rbx], 3 | RBX=0x200100 M4@0x200100 | M4@0x200100 CF
btr rdx, rcx | RDX RCX@count | RDX CF
btr rdx, 37 | RDX | RDX CF
btr qword ptr [rbx], rcx | RBX=0x200100 M8@0x2000f0 M8@0x200100 M8@0x200110 RCX@bitoff | M8@0x2000f0 M8@0x200100 M8@0x200110 CF
btr qword ptr [rbx], 3 | RBX=0x200100 M8@0x200100 | M8@0x200100 CF
btc dx, cx | RDX RCX@count | RDX CF
btc dx, 37 | RDX | RDX CF
btc word ptr [rbx], cx | RBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 RCX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
btc word ptr [rbx], 3 | RBX=0x200100 M2@0x200100 | M2@0x200100 CF
btc edx, ecx | RDX RCX@count | RDX CF
btc edx, 37 | RDX | RDX CF
btc dword ptr [rbx], ecx | RBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 RCX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
btc dword ptr [rbx], 3 | RBX=0x200100 M4@0x200100 | M4@0x200100 CF
btc rdx, rcx | RDX RCX@count | RDX CF
btc rdx, 37 | RDX | RDX CF
btc qword ptr [rbx], rcx | RBX=0x200100 M8@0x2000f0 M8@0x200100 M8@0x200110 RCX@bitoff | M8@0x2000f0 M8@0x200100 M8@0x200110 CF
btc qword ptr [rbx], 3 | RBX=0x200100 M8@0x200100 | M8@0x200100 CF
# the bit scans and counts, BSF and BSR keep the destination of zero
bsf cx, dx | RCX=0x55 RDX | RCX ZF
bsf cx, word ptr [rbx] | RCX=0x55 RBX=0x200100 M2@0x200100 | RCX ZF
bsf ecx, edx | RCX=0x55 RDX | RCX ZF
bsf ecx, dword ptr [rbx] | RCX=0x55 RBX=0x200100 M4@0x200100 | RCX ZF
bsf rcx, rdx | RCX=0x55 RDX | RCX ZF
bsf rcx, qword ptr [rbx] | RCX=0x55 RBX=0x200100 M8@0x200100 | RCX ZF
bsr cx, dx | RCX=0x55 RDX | RCX ZF
bsr cx, word ptr [rbx] | RCX=0x55 RBX=0x200100 M2@0x200100 | RCX ZF
bsr ecx, edx | RCX=0x55 RDX | RCX ZF
bsr ecx, dword ptr [rbx] | RCX=0x55 RBX=0x200100 M4@0x200100 | RCX ZF
bsr rcx, rdx | RCX=0x55 RDX | RCX ZF
bsr rcx, qword ptr [rbx] | RCX=0x55 RBX=0x200100 M8@0x200100 | RCX ZF
popcnt cx, dx | RCX=0x55 RDX | RCX ZF CF OF SF PF
popcnt cx, word ptr [rbx] | RCX=0x55 RBX=0x200100 M2@0x200100 | RCX ZF CF OF SF PF
popcnt ecx, edx | RCX=0x55 RDX | RCX ZF CF OF SF PF
popcnt ecx, dword ptr [rbx] | RCX=0x55 RBX=0x200100 M4@0x200100 | RCX ZF CF OF SF PF
popcnt rcx, rdx | RCX=0x55 RDX | RCX ZF CF OF SF PF
popcnt rcx, qword ptr [rbx] | RCX=0x55 RBX=0x200100 M8@0x200100 | RCX ZF CF OF SF PF
lzcnt cx, dx | RCX=0x55 RDX | RCX CF ZF
lzcnt cx, word ptr [rbx] | RCX=0x55 RBX=0x200100 M2@0x200100 | RCX CF ZF
lzcnt ecx, edx | RCX=0x55 RDX | RCX CF ZF
lzcnt ecx, dword ptr [rbx] | RCX=0x55 RBX=0x200100 M4@0x200100 | RCX CF ZF
lzcnt rcx, rdx | RCX=0x55 RDX | RCX CF ZF
lzcnt rcx, qword ptr [rbx] | RCX=0x55 RBX=0x200100 M8@0x200100 | RCX CF ZF
tzcnt cx, dx | RCX=0x55 RDX | RCX CF ZF
tzcnt cx, word ptr [rbx] | RCX=0x55 RBX=0x200100 M2@0x200100 | RCX CF ZF
tzcnt ecx, edx | RCX=0x55 RDX | RCX CF ZF
tzcnt ecx, dword ptr [rbx] | RCX=0x55 RBX=0x200100 M4@0x200100 | RCX CF ZF
tzcnt rcx, rdx | RCX=0x55 RDX | RCX CF ZF
tzcnt rcx, qword ptr [rbx] | RCX=0x55 RBX=0x200100 M8@0x200100 | RCX CF ZF
bswap ecx | RCX | RCX
bswap rcx | RCX | RCX
bswap r9 | R9 | R9
# the conditions of SETcc, CMOVcc and Jcc
seto cl | RCX=0x5500 CF ZF SF OF PF | RCX
seto byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setno cl | RCX=0x5500 CF ZF SF OF PF | RCX
setno byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setb cl | RCX=0x5500 CF ZF SF OF PF | RCX
setb byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setae cl | RCX=0x5500 CF ZF SF OF PF | RCX
setae byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
sete cl | RCX=0x5500 CF ZF SF OF PF | RCX
sete byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setne cl | RCX=0x5500 CF ZF SF OF PF | RCX
setne byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setbe cl | RCX=0x5500 CF ZF SF OF PF | RCX
setbe byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
seta cl | RCX=0x5500 CF ZF SF OF PF | RCX
seta byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
sets cl | RCX=0x5500 CF ZF SF OF PF | RCX
sets byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setns cl | RCX=0x5500 CF ZF SF OF PF | RCX
setns byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setp cl | RCX=0x5500 CF ZF SF OF PF | RCX
setp byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setnp cl | RCX=0x5500 CF ZF SF OF PF | RCX
setnp byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setl cl | RCX=0x5500 CF ZF SF OF PF | RCX
setl byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setge cl | RCX=0x5500 CF ZF SF OF PF | RCX
setge byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setle cl | RCX=0x5500 CF ZF SF OF PF | RCX
setle byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
setg cl | RCX=0x5500 CF ZF SF OF PF | RCX
setg byte ptr [rbx] | RBX=0x200100 CF ZF SF OF PF | M1@0x200100
cmove cx, dx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmove cx, word ptr [rbx] | RCX=0x77 RBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | RCX
cmove ecx, edx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmove ecx, dword ptr [rbx] | RCX=0x77 RBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | RCX
cmove rcx, rdx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmove rcx, qword ptr [rbx] | RCX=0x77 RBX=0x200100 M8@0x200100=0x1234 CF ZF SF OF | RCX
cmovl cx, dx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovl cx, word ptr [rbx] | RCX=0x77 RBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | RCX
cmovl ecx, edx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovl ecx, dword ptr [rbx] | RCX=0x77 RBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | RCX
cmovl rcx, rdx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovl rcx, qword ptr [rbx] | RCX=0x77 RBX=0x200100 M8@0x200100=0x1234 CF ZF SF OF | RCX
cmova cx, dx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmova cx, word ptr [rbx] | RCX=0x77 RBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | RCX
cmova ecx, edx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmova ecx, dword ptr [rbx] | RCX=0x77 RBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | RCX
cmova rcx, rdx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmova rcx, qword ptr [rbx] | RCX=0x77 RBX=0x200100 M8@0x200100=0x1234 CF ZF SF OF | RCX
cmovnp cx, dx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovnp cx, word ptr [rbx] | RCX=0x77 RBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | RCX
cmovnp ecx, edx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovnp ecx, dword ptr [rbx] | RCX=0x77 RBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | RCX
cmovnp rcx, rdx | RCX=0x123456789abcdef0 RDX CF ZF SF OF PF | RCX
cmovnp rcx, qword ptr [rbx] | RCX=0x77 RBX=0x200100 M8@0x200100=0x1234 CF ZF SF OF | RCX
jo .+0x400 | CF ZF SF OF PF | PC | 0x400
jno .+0x400 | CF ZF SF OF PF | PC | 0x400
jb .+0x400 | CF ZF SF OF PF | PC | 0x400
jae .+0x400 | CF ZF SF OF PF | PC | 0x400
je .+0x400 | CF ZF SF OF PF | PC | 0x400
jne .+0x400 | CF ZF SF OF PF | PC | 0x400
jbe .+0x400 | CF ZF SF OF PF | PC | 0x400
ja .+0x400 | CF ZF SF OF PF | PC | 0x400
js .+0x400 | CF ZF SF OF PF | PC | 0x400
jns .+0x400 | CF ZF SF OF PF | PC | 0x400
jp .+0x400 | CF ZF SF OF PF | PC | 0x400
jnp .+0x400 | CF ZF SF OF PF | PC | 0x400
jl .+0x400 | CF ZF SF OF PF | PC | 0x400
jge .+0x400 | CF ZF SF OF PF | PC | 0x400
jle .+0x400 | CF ZF SF OF PF | PC | 0x400
jg .+0x400 | CF ZF SF OF PF | PC | 0x400
je .-0x800 | ZF | PC | -0x800
jne .+0x10 | ZF | PC | 0x10
# the jumps, calls and returns, the stack is at 0x208000
jmp .+0x400 | | PC | 0x400
jmp .-0x400 | | PC | -0x400
jmp .+0x10 | | PC | 0x10
jmp rcx | RCX=0x20400 | PC | 0x400
jmp qword ptr [rbx] | RBX=0x200100 M8@0x200100=0x1fc00 | PC | -0x400
call .+0x400 | RSP=0x208000 | PC RSP M8@0x207ff8 | 0x400
call rcx | RSP=0x208000 RCX=0x20400 | PC RSP M8@0x207ff8 | 0x400
call qword ptr [rbx] | RSP=0x208000 RBX=0x200100 M8@0x200100=0x1fc00 | PC RSP M8@0x207ff8 | -0x400
ret | RSP=0x208000 M8@0x208000=0x20400 | PC RSP | 0x400
ret 0x10 | RSP=0x208000 M8@0x208000=0x1fc00 | PC RSP | -0x400
loop .+0x40 | RCX@small | PC RCX | 0x40
loope .+0x40 | RCX@small ZF | PC RCX | 0x40
loopne .+0x40 | RCX@small ZF | PC RCX | 0x40
jrcxz .+0x40 | RCX@small | PC | 0x40
# the moves of each size and form
mov cl, dl | RCX RDX | RCX
mov cl, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
mov byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100=0x55 | M1@0x200100
mov cl, 0x81 | RCX | RCX
mov byte ptr [rbx], 0x81 | RBX=0x200100 M1@0x200100=0x55 | M1@0x200100
mov cx, dx | RCX RDX | RCX
mov cx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX
mov word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100=0x55 | M2@0x200100
mov cx, 0x8001 | RCX | RCX
mov word ptr [rbx], 0x8001 | RBX=0x200100 M2@0x200100=0x55 | M2@0x200100
mov ecx, edx | RCX RDX | RCX
mov ecx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100 | RCX
mov dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100=0x55 | M4@0x200100
mov ecx, 0x80000001 | RCX | RCX
mov dword ptr [rbx], 0x80000001 | RBX=0x200100 M4@0x200100=0x55 | M4@0x200100
mov rcx, rdx | RCX RDX | RCX
mov rcx, qword ptr [rbx] | RCX RBX=0x200100 M8@0x200100 | RCX
mov qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100=0x55 | M8@0x200100
mov rcx, -5 | RCX | RCX
mov qword ptr [rbx], -5 | RBX=0x200100 M8@0x200100=0x55 | M8@0x200100
mov ah, dl | RAX RDX | RAX
movabs rcx, 0x123456789abcdef0 | RCX | RCX
mov r10d, r9d | R10 R9 | R10
mov r10w, r9w | R10 R9 | R10
mov r10b, r9b | R10 R9 | R10
mov sil, dil | RSI RDI | RSI
movabs al, byte ptr [0x200100] | RAX M1@0x200100 | RAX
movabs eax, dword ptr [0x200100] | RAX M4@0x200100 | RAX
movabs rax, qword ptr [0x200100] | RAX M8@0x200100 | RAX
movabs qword ptr [0x200100], rax | RAX | M8@0x200100
movabs word ptr [0x200100], ax | RAX | M2@0x200100
movzx cx, dl | RCX RDX | RCX
movzx cx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movsx cx, dl | RCX RDX | RCX
movsx cx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movzx ecx, dl | RCX RDX | RCX
movzx ecx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movsx ecx, dl | RCX RDX | RCX
movsx ecx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movzx ecx, dx | RCX RDX | RCX
movzx ecx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX
movsx ecx, dx | RCX RDX | RCX
movsx ecx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX
movzx rcx, dl | RCX RDX | RCX
movzx rcx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movsx rcx, dl | RCX RDX | RCX
movsx rcx, byte ptr [rbx] | RCX RBX=0x200100 M1@0x200100 | RCX
movzx rcx, dx | RCX RDX | RCX
movzx rcx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX
movsx rcx, dx | RCX RDX | RCX
movsx rcx, word ptr [rbx] | RCX RBX=0x200100 M2@0x200100 | RCX
movsxd rcx, edx | RCX RDX | RCX
movsxd rcx, dword ptr [rbx] | RCX RBX=0x200100 M4@0x200100 | RCX
lea cx, [rbx+rdx*4+0x10] | RCX RBX RDX | RCX
lea ecx, [rbx+rdx*4+0x10] | RCX RBX RDX | RCX
lea rcx, [rbx+rdx*4+0x10] | RCX RBX RDX | RCX
lea ecx, [rbx+rdx*8-0x10] | RCX RBX RDX | RCX
lea rcx, [rip+0x100] | RCX | RCX
# the exchanges
xchg cl, dl | RCX RDX | RCX RDX
xchg byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100 | RCX M1@0x200100
xadd cl, dl | RCX RDX | RCX RDX CF PF AF ZF SF OF
xadd byte ptr [rbx], cl | RCX RBX=0x200100 M1@0x200100 | RCX M1@0x200100 CF PF AF ZF SF OF
cmpxchg cl, dl | RAX@pair RCX@pair RDX | RAX RCX ZF CF
cmpxchg byte ptr [rbx], dl | RAX@pair RBX=0x200100 M1@0x200100@pair RDX | RAX M1@0x200100 ZF CF
xchg cx, dx | RCX RDX | RCX RDX
xchg word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100 | RCX M2@0x200100
xadd cx, dx | RCX RDX | RCX RDX CF PF AF ZF SF OF
xadd word ptr [rbx], cx | RCX RBX=0x200100 M2@0x200100 | RCX M2@0x200100 CF PF AF ZF SF OF
cmpxchg cx, dx | RAX@pair RCX@pair RDX | RAX RCX ZF CF
cmpxchg word ptr [rbx], dx | RAX@pair RBX=0x200100 M2@0x200100@pair RDX | RAX M2@0x200100 ZF CF
xchg ecx, edx | RCX RDX | RCX RDX
xchg dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100 | RCX M4@0x200100
xadd ecx, edx | RCX RDX | RCX RDX CF PF AF ZF SF OF
xadd dword ptr [rbx], ecx | RCX RBX=0x200100 M4@0x200100 | RCX M4@0x200100 CF PF AF ZF SF OF
cmpxchg ecx, edx | RAX@pair RCX@pair RDX | RAX RCX ZF CF
cmpxchg dword ptr [rbx], edx | RAX@pair RBX=0x200100 M4@0x200100@pair RDX | RAX M4@0x200100 ZF CF
xchg rcx, rdx | RCX RDX | RCX RDX
xchg qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100 | RCX M8@0x200100
xadd rcx, rdx | RCX RDX | RCX RDX CF PF AF ZF SF OF
xadd qword ptr [rbx], rcx | RCX RBX=0x200100 M8@0x200100 | RCX M8@0x200100 CF PF AF ZF SF OF
cmpxchg rcx, rdx | RAX@pair RCX@pair RDX | RAX RCX ZF CF
cmpxchg qword ptr [rbx], rdx | RAX@pair RBX=0x200100 M8@0x200100@pair RDX | RAX M8@0x200100 ZF CF
xchg ax, cx | RAX RCX | RAX RCX
xchg eax, ecx | RAX RCX | RAX RCX
xchg rax, rcx | RAX RCX | RAX RCX
cmpxchg8b qword ptr [rbx] | RAX@pair RDX=0 RBX=0x200100 RCX M8@0x200100@pair | RAX RDX M8@0x200100 ZF
cmpxchg16b xmmword ptr [rbx] | RAX@pair RDX=0 RBX=0x200100 RCX M16@0x200100@pair | RAX RDX M16@0x200100 ZF
# the stack
push cx | RSP=0x208000 RCX | RSP M2@0x207ffe
pop cx | RSP=0x208000 RCX M2@0x208000 | RSP RCX
push word ptr [rbx] | RSP=0x208000 RBX=0x200100 M2@0x200100 | RSP M2@0x207ffe
pop word ptr [rbx] | RSP=0x208000 RBX=0x200100 M2@0x208000 | RSP M2@0x200100
push rcx | RSP=0x208000 RCX | RSP M8@0x207ff8
pop rcx | RSP=0x208000 RCX M8@0x208000 | RSP RCX
push qword ptr [rbx] | RSP=0x208000 RBX=0x200100 M8@0x200100 | RSP M8@0x207ff8
pop qword ptr [rbx] | RSP=0x208000 RBX=0x200100 M8@0x208000 | RSP M8@0x200100
push -5 | RSP=0x208000 | RSP M8@0x207ff8
push 0x12345678 | RSP=0x208000 | RSP M8@0x207ff8
pushfq | RSP=0x208000 IF=1 CF ZF SF OF | RSP M8@0x207ff8
popfq | RSP=0x208000 M8@0x208000@flagword | RSP CF PF AF ZF SF OF
leave | RSP=0x208000 RBP=0x207f00 M8@0x207f00 | RSP RBP
enter 0x20, 0 | RSP=0x208000 RBP | RSP RBP M8@0x207ff8
# the flags
lahf | RAX CF PF AF ZF SF | RAX
sahf | RAX@ah | CF PF AF ZF SF
clc | CF | CF
stc | CF | CF
cmc | CF | CF
std | | DF
cld | DF=1 | DF
# the string instructions, with REP the count is RCX, DF is the direction
movsb | RSI=0x200100 RDI=0x200200 M1@0x200100 DF=0 | RSI RDI M1@0x200200
movsb | RSI=0x200100 RDI=0x200200 M1@0x200100 DF=1 | RSI RDI M1@0x200200
rep movsb | RSI=0x200100 RDI=0x200200 RCX@small M16@0x200100 | RSI RDI RCX M16@0x200200
stosb | RAX RDI=0x200200 DF | RDI M1@0x200200
rep stosb | RAX RDI=0x200200 RCX@small | RDI RCX M16@0x200200
lodsb | RAX RSI=0x200100 M1@0x200100 DF | RAX RSI
scasb | RAX@pair RDI=0x200100 M1@0x200100@pair | RDI CF PF AF ZF SF OF
repne scasb | RAX=0x41 RDI=0x200100 RCX@small M8@0x200100=0x4142434445464748 | RDI RCX ZF
repe scasb | RAX=0 RDI=0x200100 RCX@small M8@0x200104=0x41 | RDI RCX ZF
cmpsb | RSI=0x200100 RDI=0x200200 M1@0x200100@pair M1@0x200200@pair | RSI RDI CF PF AF ZF SF OF
repe cmpsb | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | RSI RDI RCX ZF
repne cmpsb | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | RSI RDI RCX ZF
movsw | RSI=0x200100 RDI=0x200200 M2@0x200100 DF=0 | RSI RDI M2@0x200200
movsw | RSI=0x200100 RDI=0x200200 M2@0x200100 DF=1 | RSI RDI M2@0x200200
rep movsw | RSI=0x200100 RDI=0x200200 RCX@small M16@0x200100 | RSI RDI RCX M16@0x200200
stosw | RAX RDI=0x200200 DF | RDI M2@0x200200
rep stosw | RAX RDI=0x200200 RCX@small | RDI RCX M16@0x200200
lodsw | RAX RSI=0x200100 M2@0x200100 DF | RAX RSI
scasw | RAX@pair RDI=0x200100 M2@0x200100@pair | RDI CF PF AF ZF SF OF
repne scasw | RAX=0x41 RDI=0x200100 RCX@small M8@0x200100=0x4142434445464748 | RDI RCX ZF
repe scasw | RAX=0 RDI=0x200100 RCX@small M8@0x200104=0x41 | RDI RCX ZF
cmpsw | RSI=0x200100 RDI=0x200200 M2@0x200100@pair M2@0x200200@pair | RSI RDI CF PF AF ZF SF OF
repe cmpsw | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | RSI RDI RCX ZF
repne cmpsw | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | RSI RDI RCX ZF
movsd | RSI=0x200100 RDI=0x200200 M4@0x200100 DF=0 | RSI RDI M4@0x200200
movsd | RSI=0x200100 RDI=0x200200 M4@0x200100 DF=1 | RSI RDI M4@0x200200
rep movsd | RSI=0x200100 RDI=0x200200 RCX@small M16@0x200100 | RSI RDI RCX M16@0x200200
stosd | RAX RDI=0x200200 DF | RDI M4@0x200200
rep stosd | RAX RDI=0x200200 RCX@small | RDI RCX M16@0x200200
lodsd | RAX RSI=0x200100 M4@0x200100 DF | RAX RSI
scasd | RAX@pair RDI=0x200100 M4@0x200100@pair | RDI CF PF AF ZF SF OF
repne scasd | RAX=0x41 RDI=0x200100 RCX@small M8@0x200100=0x4142434445464748 | RDI RCX ZF
repe scasd | RAX=0 RDI=0x200100 RCX@small M8@0x200104=0x41 | RDI RCX ZF
cmpsd | RSI=0x200100 RDI=0x200200 M4@0x200100@pair M4@0x200200@pair | RSI RDI CF PF AF ZF SF OF
repe cmpsd | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | RSI RDI RCX ZF
repne cmpsd | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | RSI RDI RCX ZF
movsq | RSI=0x200100 RDI=0x200200 M8@0x200100 DF=0 | RSI RDI M8@0x200200
movsq | RSI=0x200100 RDI=0x200200 M8@0x200100 DF=1 | RSI RDI M8@0x200200
rep movsq | RSI=0x200100 RDI=0x200200 RCX@small M16@0x200100 | RSI RDI RCX M16@0x200200
stosq | RAX RDI=0x200200 DF | RDI M8@0x200200
rep stosq | RAX RDI=0x200200 RCX@small | RDI RCX M16@0x200200
lodsq | RAX RSI=0x200100 M8@0x200100 DF | RAX RSI
scasq | RAX@pair RDI=0x200100 M8@0x200100@pair | RDI CF PF AF ZF SF OF
repne scasq | RAX=0x41 RDI=0x200100 RCX@small M8@0x200100=0x4142434445464748 | RDI RCX ZF
repe scasq | RAX=0 RDI=0x200100 RCX@small M8@0x200104=0x41 | RDI RCX ZF
cmpsq | RSI=0x200100 RDI=0x200200 M8@0x200100@pair M8@0x200200@pair | RSI RDI CF PF AF ZF SF OF
repe cmpsq | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | RSI RDI RCX ZF
repne cmpsq | RSI=0x200100 RDI=0x200200 RCX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | RSI RDI RCX ZF
# no effects on the registers
nop | RAX | RAX
pause | RAX | RAX
lfence | RAX | RAX
sfence | RAX | RAX
mfence | RAX | RAX
endbr64 | RAX | RAX
prefetcht0 byte ptr [rbx] | RBX=0x200100 | RBX
prefetcht1 byte ptr [rbx] | RBX=0x200100 | RBX
prefetcht2 byte ptr [rbx] | RBX=0x200100 | RBX
prefetchnta byte ptr [rbx] | RBX=0x200100 | RBX
prefetchw byte ptr [rbx] | RBX=0x200100 | RBX
clflush byte ptr [rbx] | RBX=0x200100 | RBX
nop dword ptr [rbx+rax*2+0x10] | RAX | RAX
nop word ptr [rbx] | RAX | RAX
# the packed integer operations, in the SSE, VEX.128, VEX.256 and MMX forms
paddb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddb mm0, mm1 | MM0 MM1 | MM0
paddb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddw mm0, mm1 | MM0 MM1 | MM0
paddw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddd mm0, mm1 | MM0 MM1 | MM0
paddd mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddq mm0, mm1 | MM0 MM1 | MM0
paddq mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubb mm0, mm1 | MM0 MM1 | MM0
psubb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubw mm0, mm1 | MM0 MM1 | MM0
psubw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubd mm0, mm1 | MM0 MM1 | MM0
psubd mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubq mm0, mm1 | MM0 MM1 | MM0
psubq mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddsb mm0, mm1 | MM0 MM1 | MM0
paddsb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddsw mm0, mm1 | MM0 MM1 | MM0
paddsw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubsb mm0, mm1 | MM0 MM1 | MM0
psubsb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubsw mm0, mm1 | MM0 MM1 | MM0
psubsw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddusb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddusb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddusb mm0, mm1 | MM0 MM1 | MM0
paddusb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
paddusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpaddusw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddusw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddusw mm0, mm1 | MM0 MM1 | MM0
paddusw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubusb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubusb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubusb mm0, mm1 | MM0 MM1 | MM0
psubusb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
psubusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsubusw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubusw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubusw mm0, mm1 | MM0 MM1 | MM0
psubusw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pmullw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmullw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmullw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmullw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmullw mm0, mm1 | MM0 MM1 | MM0
pmullw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pmulld xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulld xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmulld xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulld ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmulhw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmulhw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulhw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmulhw mm0, mm1 | MM0 MM1 | MM0
pmulhw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pmulhuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhuw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmulhuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulhuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmuludq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmuludq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmuludq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmuludq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmuldq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmuldq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmuldq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmuldq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaddwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaddwd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaddwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaddwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psadbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psadbw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpsadbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsadbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpavgb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpavgb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgb mm0, mm1 | MM0 MM1 | MM0
pavgb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pavgw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpavgw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpavgw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgw mm0, mm1 | MM0 MM1 | MM0
pavgw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pminub xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminub xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminub xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminub ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminub mm0, mm1 | MM0 MM1 | MM0
pminub mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pminuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminuw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminud xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminud xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminud xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminud ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxub xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxub xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxub xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxub ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxub mm0, mm1 | MM0 MM1 | MM0
pmaxub mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pmaxuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxuw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxud xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxud xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxud xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxud ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsw mm0, mm1 | MM0 MM1 | MM0
pminsw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pminsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpminsd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsw mm0, mm1 | MM0 MM1 | MM0
pmaxsw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pmaxsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqb mm0, mm1 | MM0 MM1 | MM0
pcmpeqb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpeqw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqw mm0, mm1 | MM0 MM1 | MM0
pcmpeqw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpeqd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqd mm0, mm1 | MM0 MM1 | MM0
pcmpeqd mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpeqq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtb mm0, mm1 | MM0 MM1 | MM0
pcmpgtb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpgtw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtw mm0, mm1 | MM0 MM1 | MM0
pcmpgtw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpgtd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtd mm0, mm1 | MM0 MM1 | MM0
pcmpgtd mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pcmpgtq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pand xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pand xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpand xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpand ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pand mm0, mm1 | MM0 MM1 | MM0
pand mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pandn xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pandn xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpandn xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpandn ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pandn mm0, mm1 | MM0 MM1 | MM0
pandn mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
por xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
por xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpor xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpor ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
por mm0, mm1 | MM0 MM1 | MM0
por mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
pxor xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pxor xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpxor xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpxor ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pxor mm0, mm1 | MM0 MM1 | MM0
pxor mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpcklbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklbw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpcklbw mm0, mm1 | MM0 MM1 | MM0
punpcklbw mm0, dword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpcklwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklwd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpcklwd mm0, mm1 | MM0 MM1 | MM0
punpcklwd mm0, dword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpckldq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckldq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpckldq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckldq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckldq mm0, mm1 | MM0 MM1 | MM0
punpckldq mm0, dword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpcklqdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklqdq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklqdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklqdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhbw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhbw mm0, mm1 | MM0 MM1 | MM0
punpckhbw mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpckhwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhwd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhwd mm0, mm1 | MM0 MM1 | MM0
punpckhwd mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpckhdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhdq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhdq mm0, mm1 | MM0 MM1 | MM0
punpckhdq mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
punpckhqdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhqdq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhqdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhqdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packsswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packsswb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpacksswb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpacksswb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packssdw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packssdw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpackssdw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackssdw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packuswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packuswb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpackuswb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackuswb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packusdw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packusdw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpackusdw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackusdw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pshufb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pshufb xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vpshufb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpshufb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pshufb mm0, mm1 | MM0 MM1 | MM0
pshufb mm0, qword ptr [rbx] | MM0 RBX=0x200100 M8@0x200100 | MM0
unpcklps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpcklps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vunpcklps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpcklps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpckhps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpckhps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vunpckhps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpckhps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpcklpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpcklpd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vunpcklpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpcklpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpckhpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpckhpd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vunpckhpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpckhpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vandps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vandps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andpd xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vandpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vandpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
orps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
orps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vorps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vorps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
xorps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
xorps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vxorps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vxorps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andnps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andnps xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
vandnps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vandnps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
# the absolute values
pabsb xmm0, xmm1 | XMM1@vec | XMM0
vpabsb ymm0, ymm1 | YMM1 | YMM0
pabsb mm0, mm1 | MM1 | MM0
pabsw xmm0, xmm1 | XMM1@vec | XMM0
vpabsw ymm0, ymm1 | YMM1 | YMM0
pabsw mm0, mm1 | MM1 | MM0
pabsd xmm0, xmm1 | XMM1@vec | XMM0
vpabsd ymm0, ymm1 | YMM1 | YMM0
pabsd mm0, mm1 | MM1 | MM0
# the shifts of the lanes
psllw xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psllw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psllw xmm0, 5 | XMM0@vec | XMM0
psllw xmm0, 40 | XMM0@vec | XMM0
vpsllw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsllw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsllw ymm2, ymm0, 3 | YMM0 | YMM2
psllw mm0, mm1 | MM0 MM1@count | MM0
psllw mm0, 7 | MM0 | MM0
pslld xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
pslld xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
pslld xmm0, 5 | XMM0@vec | XMM0
pslld xmm0, 40 | XMM0@vec | XMM0
vpslld xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpslld ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpslld ymm2, ymm0, 3 | YMM0 | YMM2
pslld mm0, mm1 | MM0 MM1@count | MM0
pslld mm0, 7 | MM0 | MM0
psllq xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psllq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psllq xmm0, 5 | XMM0@vec | XMM0
psllq xmm0, 40 | XMM0@vec | XMM0
vpsllq xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsllq ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsllq ymm2, ymm0, 3 | YMM0 | YMM2
psllq mm0, mm1 | MM0 MM1@count | MM0
psllq mm0, 7 | MM0 | MM0
psrlw xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrlw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psrlw xmm0, 5 | XMM0@vec | XMM0
psrlw xmm0, 40 | XMM0@vec | XMM0
vpsrlw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrlw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrlw ymm2, ymm0, 3 | YMM0 | YMM2
psrlw mm0, mm1 | MM0 MM1@count | MM0
psrlw mm0, 7 | MM0 | MM0
psrld xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrld xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psrld xmm0, 5 | XMM0@vec | XMM0
psrld xmm0, 40 | XMM0@vec | XMM0
vpsrld xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrld ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrld ymm2, ymm0, 3 | YMM0 | YMM2
psrld mm0, mm1 | MM0 MM1@count | MM0
psrld mm0, 7 | MM0 | MM0
psrlq xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrlq xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psrlq xmm0, 5 | XMM0@vec | XMM0
psrlq xmm0, 40 | XMM0@vec | XMM0
vpsrlq xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrlq ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrlq ymm2, ymm0, 3 | YMM0 | YMM2
psrlq mm0, mm1 | MM0 MM1@count | MM0
psrlq mm0, 7 | MM0 | MM0
psraw xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psraw xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psraw xmm0, 5 | XMM0@vec | XMM0
psraw xmm0, 40 | XMM0@vec | XMM0
vpsraw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsraw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsraw ymm2, ymm0, 3 | YMM0 | YMM2
psraw mm0, mm1 | MM0 MM1@count | MM0
psraw mm0, 7 | MM0 | MM0
psrad xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrad xmm0, xmmword ptr [rbx] | XMM0@vec RBX=0x200100 M16@0x200100@count | XMM0
psrad xmm0, 5 | XMM0@vec | XMM0
psrad xmm0, 40 | XMM0@vec | XMM0
vpsrad xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrad ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrad ymm2, ymm0, 3 | YMM0 | YMM2
psrad mm0, mm1 | MM0 MM1@count | MM0
psrad mm0, 7 | MM0 | MM0
pslldq xmm0, 0 | XMM0@vec | XMM0
pslldq xmm0, 3 | XMM0@vec | XMM0
pslldq xmm0, 9 | XMM0@vec | XMM0
pslldq xmm0, 16 | XMM0@vec | XMM0
vpslldq ymm0, ymm1, 5 | YMM1 | YMM0
psrldq xmm0, 0 | XMM0@vec | XMM0
psrldq xmm0, 3 | XMM0@vec | XMM0
psrldq xmm0, 9 | XMM0@vec | XMM0
psrldq xmm0, 16 | XMM0@vec | XMM0
vpsrldq ymm0, ymm1, 5 | YMM1 | YMM0
# the shuffles and the alignments
pshufd xmm0, xmm1, 0x1b | XMM1@vec | XMM0
pshuflw xmm0, xmm1, 0x1b | XMM1@vec | XMM0
pshufhw xmm0, xmm1, 0x1b | XMM1@vec | XMM0
pshufd xmm0, xmm1, 0x0 | XMM1@vec | XMM0
pshuflw xmm0, xmm1, 0x0 | XMM1@vec | XMM0
pshufhw xmm0, xmm1, 0x0 | XMM1@vec | XMM0
pshufd xmm0, xmm1, 0xe4 | XMM1@vec | XMM0
pshuflw xmm0, xmm1, 0xe4 | XMM1@vec | XMM0
pshufhw xmm0, xmm1, 0xe4 | XMM1@vec | XMM0
pshufd xmm0, xmmword ptr [rbx], 0x1b | RBX=0x200100 M16@0x200100@vec | XMM0
vpshufd ymm0, ymm1, 0x4e | YMM1 | YMM0
vpshuflw xmm0, xmm1, 0x1b | XMM1@vec | YMM0
vpshufhw xmm0, xmm1, 0x1b | XMM1@vec | YMM0
palignr xmm0, xmm1, 0 | XMM0@vec XMM1@vec | XMM0
palignr xmm0, xmm1, 5 | XMM0@vec XMM1@vec | XMM0
palignr xmm0, xmm1, 16 | XMM0@vec XMM1@vec | XMM0
palignr xmm0, xmm1, 31 | XMM0@vec XMM1@vec | XMM0
vpalignr ymm0, ymm1, ymm2, 3 | YMM1 YMM2 | YMM0
palignr mm0, mm1, 3 | MM0 MM1 | MM0
shufps xmm0, xmm1, 0x1b | XMM0@vec XMM1@vec | XMM0
shufpd xmm0, xmmword ptr [rbx], 1 | XMM0@vec RBX=0x200100 M16@0x200100@vec | XMM0
insertps xmm0, xmm1, 0x5c | XMM0@vec XMM1@vec | XMM0
insertps xmm0, dword ptr [rbx], 0x20 | XMM0@vec RBX=0x200100 M4@0x200100 | XMM0
vinsertps xmm0, xmm1, xmm2, 0x91 | XMM1@vec XMM2@vec | YMM0
# the masks, the tests and the extensions
pmovmskb ecx, xmm0 | XMM0@vec | RCX
vpmovmskb ecx, ymm0 | YMM0 | RCX
pmovmskb ecx, mm0 | MM0 | RCX
ptest xmm0, xmm1 | XMM0@vec XMM1@vec | ZF CF
vptest ymm0, ymm1 | YMM0 YMM1 | ZF CF
pmovzxbw xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbw ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbw xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbw ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbw xmm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | XMM0
pmovzxbd xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbd ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbd xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbd ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbd xmm0, dword ptr [rbx] | RBX=0x200100 M4@0x200100 | XMM0
pmovzxbq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbq xmm0, word ptr [rbx] | RBX=0x200100 M2@0x200100 | XMM0
pmovzxwd xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxwd ymm0, xmm1 | XMM1@vec | YMM0
pmovsxwd xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxwd ymm0, xmm1 | XMM1@vec | YMM0
pmovzxwd xmm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | XMM0
pmovzxwq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxwq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxwq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxwq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxwq xmm0, dword ptr [rbx] | RBX=0x200100 M4@0x200100 | XMM0
pmovzxdq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxdq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxdq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxdq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxdq xmm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | XMM0
# the moves of the vector registers
movaps xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movaps xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movaps xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovaps xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovaps ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovaps ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
movups xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movups xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movups xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovups xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovups ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovups ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
movapd xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movapd xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movapd xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovapd xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovapd ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovapd ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
movupd xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movupd xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movupd xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovupd xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovupd ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovupd ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
movdqa xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movdqa xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movdqa xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovdqa xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovdqa ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovdqa ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
movdqu xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movdqu xmm0, xmmword ptr [rbx] | XMM0 RBX=0x200100 M16@0x200100@vec | XMM0
movdqu xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
vmovdqu xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovdqu ymm0, ymmword ptr [rbx] | RBX=0x200100 M32@0x200100@ymm | YMM0
vmovdqu ymmword ptr [rbx], ymm1 | YMM1 RBX=0x200100 | M32@0x200100
lddqu xmm0, xmmword ptr [rbx] | RBX=0x200100 M16@0x200100@vec | XMM0
movntdq xmmword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 | M16@0x200100
movss xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movss xmm0, dword ptr [rbx] | XMM0@vec RBX=0x200100 M4@0x200100 | XMM0
movss dword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 M16@0x200100=0xffffffffffffffffffffffffffffffff | M16@0x200100
vmovss xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
vmovss xmm0, dword ptr [rbx] | RBX=0x200100 M4@0x200100 | YMM0
movsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movsd xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movsd qword ptr [rbx], xmm1 | XMM1@vec RBX=0x200100 M16@0x200100=0xffffffffffffffffffffffffffffffff | M16@0x200100
vmovsd xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
vmovsd xmm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | YMM0
movd xmm0, ecx | XMM0@vec RCX | XMM0
movd ecx, xmm0 | XMM0@vec RCX | RCX
movd xmm0, dword ptr [rbx] | XMM0@vec RBX=0x200100 M4@0x200100 | XMM0
movd dword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M4@0x200100
movq xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movq qword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M8@0x200100
movq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
vmovd xmm0, ecx | RCX | YMM0
vmovq xmm0, xmm1 | XMM1@vec | YMM0
movq xmm0, rcx | XMM0@vec RCX | XMM0
movq rcx, xmm0 | XMM0@vec | RCX
vmovq rcx, xmm0 | XMM0@vec | RCX
movd mm0, ecx | RCX | MM0
movd ecx, mm0 | MM0 | RCX
movq mm0, mm1 | MM1 | MM0
movq mm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | MM0
movq qword ptr [rbx], mm0 | MM0 RBX=0x200100 | M8@0x200100
movdq2q mm0, xmm1 | XMM1@vec | MM0
movq2dq xmm0, mm1 | XMM0@vec MM1 | XMM0
movhps xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movhps qword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M8@0x200100
vmovhps xmm0, xmm1, qword ptr [rbx] | XMM1@vec RBX=0x200100 M8@0x200100 | YMM0
movlps xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movlps qword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M8@0x200100
vmovlps xmm0, xmm1, qword ptr [rbx] | XMM1@vec RBX=0x200100 M8@0x200100 | YMM0
movhpd xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movhpd qword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M8@0x200100
vmovhpd xmm0, xmm1, qword ptr [rbx] | XMM1@vec RBX=0x200100 M8@0x200100 | YMM0
movlpd xmm0, qword ptr [rbx] | XMM0@vec RBX=0x200100 M8@0x200100 | XMM0
movlpd qword ptr [rbx], xmm0 | XMM0@vec RBX=0x200100 | M8@0x200100
vmovlpd xmm0, xmm1, qword ptr [rbx] | XMM1@vec RBX=0x200100 M8@0x200100 | YMM0
movhlps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movlhps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
vmovhlps xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
movddup xmm0, xmm1 | XMM1@vec | XMM0
vmovddup ymm0, ymm1 | YMM1 | YMM0
movshdup xmm0, xmm1 | XMM1@vec | XMM0
vmovshdup ymm0, ymm1 | YMM1 | YMM0
movsldup xmm0, xmm1 | XMM1@vec | XMM0
vmovsldup ymm0, ymm1 | YMM1 | YMM0
movddup xmm0, qword ptr [rbx] | RBX=0x200100 M8@0x200100 | XMM0
pextrw ecx, xmm0, 5 | XMM0@vec | RCX
pinsrw xmm0, ecx, 3 | XMM0@vec RCX | XMM0
pextrb ecx, xmm0, 9 | XMM0@vec | RCX
pinsrd xmm0, ecx, 2 | XMM0@vec RCX | XMM0
# the packed string comparisons, the strings end with a zero element
pcmpistri xmm0, xmm1, 0x0 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x4 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x8 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0xc | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x1 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x10 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x30 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x40 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x12 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0xd | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x48 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x14 | XMM0@str XMM1@str | RCX CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x0 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x40 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x8 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x44 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpestri xmm0, xmm1, 0x0 | XMM0@str XMM1@str RAX@len RDX@len | RCX CF ZF SF OF
pcmpestri xmm0, xmm1, 0xc | XMM0@str XMM1@str RAX@len RDX@len | RCX CF ZF SF OF
pcmpestri xmm0, xmm1, 0x1 | XMM0@str XMM1@str RAX@len RDX@len | RCX CF ZF SF OF
pcmpestrm xmm1, xmm2, 0x08 | XMM1@str XMM2@str RAX@len RDX@len | XMM0 CF ZF SF OF
pcmpistri xmm0, xmmword ptr [rbx], 0x0c | XMM0@str RBX=0x200100 M16@0x200100@str | RCX CF ZF
