# addition and subtraction
add eax, ebx | EAX EBX | EAX CF PF AF ZF SF OF
add ax, bx | EAX EBX | EAX CF PF AF ZF SF OF
add al, bl | EAX EBX | EAX CF PF AF ZF SF OF
add ah, bh | EAX EBX | EAX CF PF AF ZF SF OF
add byte ptr [ebx], al | EAX EBX=0x200100 M8@0x200100 | M8@0x200100 CF ZF SF OF
adc eax, ebx | EAX EBX CF | EAX CF PF AF ZF SF OF
adc al, bl | EAX EBX CF | EAX CF PF AF ZF SF OF
sub eax, ebx | EAX EBX | EAX CF PF AF ZF SF OF
sub ax, bx | EAX EBX | EAX CF PF AF ZF SF OF
sbb ax, bx | EAX EBX CF | EAX CF PF AF ZF SF OF
cmp ecx, 0x80 | ECX | CF PF AF ZF SF OF
cmp byte ptr [ebx], 0x7f | EBX=0x200100 M1@0x200100@byte | CF PF AF ZF SF OF
neg ecx | ECX | ECX CF PF AF ZF SF OF
inc eax | EAX CF | EAX CF PF AF ZF SF OF
dec ax | EAX CF | EAX CF PF AF ZF SF OF
dec ecx | ECX CF | ECX CF PF AF ZF SF OF
add eax, 0x7fffffff | EAX | EAX CF PF AF ZF SF OF
add eax, dword ptr [ebx+ecx*8+8] | EAX EBX=0x200100 ECX=2 M4@0x200118 | EAX CF ZF SF OF
xadd eax, ebx | EAX EBX | EAX EBX CF PF AF ZF SF OF
# logical operations
or ecx, edx | ECX EDX | ECX CF PF ZF SF OF
xor ax, bx | EAX EBX | EAX CF PF ZF SF OF
xor eax, eax | EAX | EAX CF PF ZF SF OF
test al, 0x80 | EAX | CF PF ZF SF OF
and eax, ebx | EAX EBX | EAX CF PF ZF SF OF
test eax, ebx | EAX EBX | CF PF ZF SF OF
not eax | EAX | EAX
and eax, -0x100 | EAX | EAX CF ZF SF OF
not cl | ECX | ECX
# shifts and rotations
shl eax, cl | EAX ECX@count CF | EAX CF PF ZF SF
shr eax, cl | EAX ECX@count CF | EAX CF PF ZF SF
sar eax, cl | EAX ECX@count CF | EAX CF PF ZF SF
shl ax, cl | EAX ECX@byte CF | EAX PF ZF SF
sar al, cl | EAX ECX@byte CF | EAX PF ZF SF
sar eax, 1 | EAX CF | EAX CF PF ZF SF OF
shl eax, 1 | EAX CF | EAX CF PF ZF SF OF
shr eax, 1 | EAX CF | EAX CF PF ZF SF OF
shr eax, 31 | EAX | EAX CF PF ZF SF
sar edx, 17 | EDX | EDX CF PF ZF SF
rol eax, cl | EAX ECX@count CF | EAX CF
ror ax, cl | EAX ECX@count CF | EAX
rol al, cl | EAX ECX@count CF | EAX
ror eax, 1 | EAX CF | EAX CF OF
rol eax, 1 | EAX CF | EAX CF OF
rcl eax, 1 | EAX CF | EAX CF OF
rcr eax, 1 | EAX CF | EAX CF OF
rcl eax, cl | EAX ECX@count CF | EAX CF
rcr eax, cl | EAX ECX@count CF | EAX CF
shld eax, ebx, cl | EAX EBX ECX@count | EAX
shrd eax, ebx, cl | EAX EBX ECX@count | EAX
shld eax, ebx, 7 | EAX EBX | EAX CF PF ZF SF
# multiplication and division
mul ebx | EAX EBX EDX=5 | EAX EDX CF OF
mul bl | EAX EBX | EAX CF OF
imul ecx | EAX ECX | EAX EDX CF OF
imul eax, ebx | EAX EBX | EAX CF OF
imul eax, ebx, -3 | EAX EBX | EAX CF OF
imul ax, bx | EAX EBX | EAX CF OF
div ecx | EAX EDX=0 ECX@nz32 | EAX EDX
div ecx | EAX=0 EDX=1 ECX@nz32 | EAX EDX
div cl | EAX ECX@byte | EAX
idiv ecx | EAX EDX=0 ECX@nz32 | EAX EDX
idiv ecx | EAX EDX=0xffffffff ECX@nz32 | EAX EDX
idiv cl | EAX ECX@byte | EAX
# bit operations
bt eax, ebx | EAX EBX | CF
bts eax, ebx | EAX EBX | EAX CF
btr eax, ebx | EAX EBX | EAX CF
btc eax, 31 | EAX | EAX CF
bt dword ptr [ebx], 35 | EBX=0x200100 M8@0x200100 | CF
bsf eax, ebx | EAX=0 EBX@nz | EAX ZF
popcnt eax, ebx | EBX | EAX CF PF AF ZF SF OF
lzcnt eax, ebx | EBX | EAX CF ZF
bsr ecx, edx | ECX=0 EDX@nz | ECX ZF
tzcnt ecx, edx | EDX | ECX CF ZF
bswap ecx | ECX | ECX
# BMI
andn eax, ebx, ecx | EBX ECX | EAX ZF SF CF OF
blsi eax, ebx | EBX | EAX ZF SF CF OF
blsmsk eax, ebx | EBX | EAX ZF SF CF OF
sarx eax, ebx, ecx | EBX ECX@count | EAX
shrx eax, ebx, ecx | EBX ECX@count | EAX
adcx eax, ebx | EAX EBX CF OF | EAX CF OF
shlx eax, ebx, ecx | EBX ECX@count | EAX
blsr ecx, edx | EDX | ECX ZF SF CF OF
bzhi eax, ebx, ecx | EBX ECX@count | EAX ZF SF CF OF
bextr eax, ebx, ecx | EBX ECX=0x0c1c | EAX ZF CF OF
pdep eax, ebx, ecx | EBX ECX | EAX
pext eax, ebx, ecx | EBX ECX | EAX
rorx eax, ebx, 37 | EBX | EAX
mulx eax, ecx, ebx | EDX EBX | EAX ECX
adox eax, ebx | EAX EBX CF OF | EAX CF OF
# moves and extensions
movzx eax, bl | EAX EBX | EAX
movzx eax, bx | EAX EBX | EAX
movsx eax, bl | EAX EBX | EAX
movsx eax, bx | EAX EBX | EAX
mov al, bh | EAX EBX | EAX
mov eax, ebx | EAX EBX | EAX
mov ax, bx | EAX EBX | EAX
cbw | EAX | EAX
cwde | EAX | EAX
cwd | EAX EDX | EAX EDX
cdq | EAX EDX | EDX
xchg eax, ebx | EAX EBX | EAX EBX
xchg al, bl | EAX EBX | EAX EBX
cmpxchg ecx, ebx | EAX=0xffffffff00000005 ECX=5 EBX | EAX ECX ZF
lea eax, [ebx+ecx*4-8] | EBX ECX | EAX
lea eax, [ebx+ecx*2+0x10] | EBX ECX | EAX
mov eax, dword ptr [ebx+8] | EBX=0x200100 M8@0x200108 | EAX
mov dword ptr [ebx-4], eax | EAX EBX=0x200104 | M8@0x200100
# conditional moves and sets
cmovb eax, ebx | EAX=1 EBX=2 CF | EAX
cmovbe eax, ebx | EAX=1 EBX=2 CF ZF | EAX
cmovl eax, ebx | EAX=1 EBX=2 SF OF | EAX
cmovle eax, ebx | EAX=1 EBX=2 SF OF ZF | EAX
cmovg eax, ebx | EAX=1 EBX=2 SF OF ZF | EAX
cmovp eax, ebx | EAX=1 EBX=2 PF | EAX
cmovs eax, ebx | EAX=0xffffffff00000001 EBX=2 SF | EAX
setb al | EAX=0xff CF | EAX
seta cl | ECX CF ZF | ECX
setge al | EAX=0xffff SF OF | EAX
setle bl | EBX SF OF ZF | EBX
setnp al | EAX PF | EAX
# flags
stc | CF | CF
clc | CF | CF
cmc | CF | CF
lahf | EAX CF ZF SF PF | EAX
sahf | EAX@byte | CF PF AF ZF SF
# stack
push ebx | EBX | ESP M4@0x207ffc
pop ebx | M4@0x208000 | EBX ESP
push 0x7f | | ESP M4@0x207ffc
push -1 | | ESP M4@0x207ffc
leave | EBP=0x207000 M8@0x207000 | ESP EBP
# strings
movsb | ESI=0x200100 EDI=0x200200 M1@0x200100@byte | ESI EDI M1@0x200200
stosd | EAX EDI=0x200200 DF | EDI M4@0x200200
lodsb | EAX ESI=0x200100 M1@0x200100@byte DF | EAX ESI
lodsw | EAX ESI=0x200100 M2@0x200100 | EAX ESI
lodsd | EAX ESI=0x200100 M4@0x200100=0x89abcdef DF | EAX ESI
rep stosb | EAX@byte ECX@byte EDI=0x200200 | ECX EDI M8@0x200200 M8@0x200208
rep movsb | ECX=5 ESI=0x200100 EDI=0x200200 M8@0x200100 | ECX ESI EDI M8@0x200200
cmpsb | ESI=0x200100 EDI=0x200200 M1@0x200100@byte M1@0x200200@byte | ESI EDI CF ZF SF OF
scasb | EAX@byte EDI=0x200200 M1@0x200200@byte | EDI CF ZF SF OF
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
addsd xmm0, qword ptr [ebx] | XMM0 EBX=0x200100 M8@0x200100=0x4000000000000000 | XMM0
ucomisd xmm0, xmm1 | XMM0 XMM1 | ZF PF CF OF SF AF
comiss xmm0, xmm1 | XMM0 XMM1 | ZF PF CF OF SF AF
cvtsi2sd xmm0, eax | XMM0=0 EAX | XMM0
cvtsi2ss xmm0, eax | XMM0=0 EAX | XMM0
cvttsd2si eax, xmm0 | XMM0 EAX | EAX
cvttss2si eax, xmm0 | XMM0 | EAX
cvtsd2ss xmm0, xmm1 | XMM0 XMM1 | XMM0
cvtss2sd xmm0, xmm1 | XMM0 XMM1 | XMM0
cvtsd2si eax, xmm0 | XMM0 EAX | EAX
cvtps2pd xmm0, xmm1 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 0 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 2 | XMM0 XMM1 | XMM0
roundsd xmm0, xmm1, 4 | XMM0 XMM1 | XMM0
roundss xmm0, xmm1, 1 | XMM0 XMM1 | XMM0
roundss xmm0, xmm1, 3 | XMM0 XMM1 | XMM0
maxsd xmm0, qword ptr [ebx+ecx*8] | XMM0 EBX=0x200100 ECX=1 M8@0x200108=0xbff8000000000000 | XMM0
ucomisd xmm0, qword ptr [ebx] | XMM0 EBX=0x200100 M8@0x200100=0x3ff8000000000000 | ZF PF CF
andpd xmm0, xmm1 | XMM0 XMM1 | XMM0
xorps xmm0, xmm1 | XMM0 XMM1 | XMM0
andnpd xmm0, xmm1 | XMM0 XMM1 | XMM0
# SSE moves
movsd xmm0, xmm1 | XMM0 XMM1 | XMM0
movss xmm0, xmm1 | XMM0 XMM1 | XMM0
movd eax, xmm0 | XMM0 EAX | EAX
movd xmm0, eax | XMM0 EAX | XMM0
movsd xmm0, qword ptr [ebx] | XMM0 EBX=0x200100 M8@0x200100 | XMM0
movsd qword ptr [ebx], xmm0 | XMM0 EBX=0x200100 | M8@0x200100 M8@0x200108
movups xmm0, xmmword ptr [ebx] | EBX=0x200100 M16@0x200100@vec | XMM0
movaps xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
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
movmskpd eax, xmm0 | XMM0 EAX | EAX
movmskps eax, xmm0 | XMM0 EAX | EAX
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
pmovmskb eax, xmm0 | XMM0@vec EAX | EAX
pextrw eax, xmm0, 5 | XMM0@vec EAX | EAX
pinsrw xmm0, eax, 6 | XMM0@vec EAX | XMM0
pminsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulld xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
ptest xmm0, xmm1 | XMM0@vec XMM1@vec | ZF CF
pextrd eax, xmm0, 3 | XMM0@vec EAX | EAX
pextrb eax, xmm0, 17 | XMM0@vec EAX | EAX
pinsrb xmm0, eax, 9 | XMM0@vec EAX | XMM0
pinsrd xmm0, eax, 2 | XMM0@vec EAX | XMM0
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
add cl, dl | ECX EDX  | ECX CF PF AF ZF SF OF
add cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  | ECX CF PF AF ZF SF OF
add byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
add cl, 0x81 | ECX  | ECX CF PF AF ZF SF OF
add byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
add al, 0x81 | EAX  | EAX CF PF AF ZF SF OF
add cx, dx | ECX EDX  | ECX CF PF AF ZF SF OF
add cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  | ECX CF PF AF ZF SF OF
add word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add cx, 0x8001 | ECX  | ECX CF PF AF ZF SF OF
add cx, -3 | ECX  | ECX CF PF AF ZF SF OF
add word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
add ax, 0x8001 | EAX  | EAX CF PF AF ZF SF OF
add ecx, edx | ECX EDX  | ECX CF PF AF ZF SF OF
add ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  | ECX CF PF AF ZF SF OF
add dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add ecx, 0x80000001 | ECX  | ECX CF PF AF ZF SF OF
add ecx, -3 | ECX  | ECX CF PF AF ZF SF OF
add dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
add eax, 0x80000001 | EAX  | EAX CF PF AF ZF SF OF
add ah, ch | EAX ECX  | EAX CF PF AF ZF SF OF
adc cl, dl | ECX EDX CF | ECX CF PF AF ZF SF OF
adc cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 CF | ECX CF PF AF ZF SF OF
adc byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
adc cl, 0x81 | ECX CF | ECX CF PF AF ZF SF OF
adc byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
adc al, 0x81 | EAX CF | EAX CF PF AF ZF SF OF
adc cx, dx | ECX EDX CF | ECX CF PF AF ZF SF OF
adc cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 CF | ECX CF PF AF ZF SF OF
adc word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc cx, 0x8001 | ECX CF | ECX CF PF AF ZF SF OF
adc cx, -3 | ECX CF | ECX CF PF AF ZF SF OF
adc word ptr [ebx], -3 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
adc ax, 0x8001 | EAX CF | EAX CF PF AF ZF SF OF
adc ecx, edx | ECX EDX CF | ECX CF PF AF ZF SF OF
adc ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100 CF | ECX CF PF AF ZF SF OF
adc dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc ecx, 0x80000001 | ECX CF | ECX CF PF AF ZF SF OF
adc ecx, -3 | ECX CF | ECX CF PF AF ZF SF OF
adc dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
adc eax, 0x80000001 | EAX CF | EAX CF PF AF ZF SF OF
adc ah, ch | EAX ECX CF | EAX CF PF AF ZF SF OF
sub cl, dl | ECX EDX  | ECX CF PF AF ZF SF OF
sub cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  | ECX CF PF AF ZF SF OF
sub byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
sub cl, 0x81 | ECX  | ECX CF PF AF ZF SF OF
sub byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF AF ZF SF OF
sub al, 0x81 | EAX  | EAX CF PF AF ZF SF OF
sub cx, dx | ECX EDX  | ECX CF PF AF ZF SF OF
sub cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  | ECX CF PF AF ZF SF OF
sub word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub cx, 0x8001 | ECX  | ECX CF PF AF ZF SF OF
sub cx, -3 | ECX  | ECX CF PF AF ZF SF OF
sub word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF AF ZF SF OF
sub ax, 0x8001 | EAX  | EAX CF PF AF ZF SF OF
sub ecx, edx | ECX EDX  | ECX CF PF AF ZF SF OF
sub ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  | ECX CF PF AF ZF SF OF
sub dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub ecx, 0x80000001 | ECX  | ECX CF PF AF ZF SF OF
sub ecx, -3 | ECX  | ECX CF PF AF ZF SF OF
sub dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF AF ZF SF OF
sub eax, 0x80000001 | EAX  | EAX CF PF AF ZF SF OF
sub ah, ch | EAX ECX  | EAX CF PF AF ZF SF OF
sbb cl, dl | ECX EDX CF | ECX CF PF AF ZF SF OF
sbb cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 CF | ECX CF PF AF ZF SF OF
sbb byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
sbb cl, 0x81 | ECX CF | ECX CF PF AF ZF SF OF
sbb byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
sbb al, 0x81 | EAX CF | EAX CF PF AF ZF SF OF
sbb cx, dx | ECX EDX CF | ECX CF PF AF ZF SF OF
sbb cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 CF | ECX CF PF AF ZF SF OF
sbb word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb cx, 0x8001 | ECX CF | ECX CF PF AF ZF SF OF
sbb cx, -3 | ECX CF | ECX CF PF AF ZF SF OF
sbb word ptr [ebx], -3 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
sbb ax, 0x8001 | EAX CF | EAX CF PF AF ZF SF OF
sbb ecx, edx | ECX EDX CF | ECX CF PF AF ZF SF OF
sbb ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100 CF | ECX CF PF AF ZF SF OF
sbb dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb ecx, 0x80000001 | ECX CF | ECX CF PF AF ZF SF OF
sbb ecx, -3 | ECX CF | ECX CF PF AF ZF SF OF
sbb dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
sbb eax, 0x80000001 | EAX CF | EAX CF PF AF ZF SF OF
sbb ah, ch | EAX ECX CF | EAX CF PF AF ZF SF OF
and cl, dl | ECX EDX  | ECX CF PF ZF SF OF
and cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  | ECX CF PF ZF SF OF
and byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
and cl, 0x81 | ECX  | ECX CF PF ZF SF OF
and byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
and al, 0x81 | EAX  | EAX CF PF ZF SF OF
and cx, dx | ECX EDX  | ECX CF PF ZF SF OF
and cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  | ECX CF PF ZF SF OF
and word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and cx, 0x8001 | ECX  | ECX CF PF ZF SF OF
and cx, -3 | ECX  | ECX CF PF ZF SF OF
and word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
and ax, 0x8001 | EAX  | EAX CF PF ZF SF OF
and ecx, edx | ECX EDX  | ECX CF PF ZF SF OF
and ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  | ECX CF PF ZF SF OF
and dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and ecx, 0x80000001 | ECX  | ECX CF PF ZF SF OF
and ecx, -3 | ECX  | ECX CF PF ZF SF OF
and dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
and eax, 0x80000001 | EAX  | EAX CF PF ZF SF OF
and ah, ch | EAX ECX  | EAX CF PF ZF SF OF
or cl, dl | ECX EDX  | ECX CF PF ZF SF OF
or cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  | ECX CF PF ZF SF OF
or byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
or cl, 0x81 | ECX  | ECX CF PF ZF SF OF
or byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
or al, 0x81 | EAX  | EAX CF PF ZF SF OF
or cx, dx | ECX EDX  | ECX CF PF ZF SF OF
or cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  | ECX CF PF ZF SF OF
or word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or cx, 0x8001 | ECX  | ECX CF PF ZF SF OF
or cx, -3 | ECX  | ECX CF PF ZF SF OF
or word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
or ax, 0x8001 | EAX  | EAX CF PF ZF SF OF
or ecx, edx | ECX EDX  | ECX CF PF ZF SF OF
or ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  | ECX CF PF ZF SF OF
or dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or ecx, 0x80000001 | ECX  | ECX CF PF ZF SF OF
or ecx, -3 | ECX  | ECX CF PF ZF SF OF
or dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
or eax, 0x80000001 | EAX  | EAX CF PF ZF SF OF
or ah, ch | EAX ECX  | EAX CF PF ZF SF OF
xor cl, dl | ECX EDX  | ECX CF PF ZF SF OF
xor cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  | ECX CF PF ZF SF OF
xor byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
xor cl, 0x81 | ECX  | ECX CF PF ZF SF OF
xor byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  | M1@0x200100 CF PF ZF SF OF
xor al, 0x81 | EAX  | EAX CF PF ZF SF OF
xor cx, dx | ECX EDX  | ECX CF PF ZF SF OF
xor cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  | ECX CF PF ZF SF OF
xor word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor cx, 0x8001 | ECX  | ECX CF PF ZF SF OF
xor cx, -3 | ECX  | ECX CF PF ZF SF OF
xor word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  | M2@0x200100 CF PF ZF SF OF
xor ax, 0x8001 | EAX  | EAX CF PF ZF SF OF
xor ecx, edx | ECX EDX  | ECX CF PF ZF SF OF
xor ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  | ECX CF PF ZF SF OF
xor dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor ecx, 0x80000001 | ECX  | ECX CF PF ZF SF OF
xor ecx, -3 | ECX  | ECX CF PF ZF SF OF
xor dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  | M4@0x200100 CF PF ZF SF OF
xor eax, 0x80000001 | EAX  | EAX CF PF ZF SF OF
xor ah, ch | EAX ECX  | EAX CF PF ZF SF OF
cmp cl, dl | ECX EDX  |  CF PF AF ZF SF OF
cmp cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp cl, 0x81 | ECX  |  CF PF AF ZF SF OF
cmp byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  |  CF PF AF ZF SF OF
cmp al, 0x81 | EAX  |  CF PF AF ZF SF OF
cmp cx, dx | ECX EDX  |  CF PF AF ZF SF OF
cmp cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp cx, 0x8001 | ECX  |  CF PF AF ZF SF OF
cmp cx, -3 | ECX  |  CF PF AF ZF SF OF
cmp word ptr [ebx], -3 | EBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  |  CF PF AF ZF SF OF
cmp ax, 0x8001 | EAX  |  CF PF AF ZF SF OF
cmp ecx, edx | ECX EDX  |  CF PF AF ZF SF OF
cmp ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp ecx, 0x80000001 | ECX  |  CF PF AF ZF SF OF
cmp ecx, -3 | ECX  |  CF PF AF ZF SF OF
cmp dword ptr [ebx], -3 | EBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  |  CF PF AF ZF SF OF
cmp eax, 0x80000001 | EAX  |  CF PF AF ZF SF OF
cmp ah, ch | EAX ECX  |  CF PF AF ZF SF OF
test cl, dl | ECX EDX  |  CF PF ZF SF OF
test byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100  |  CF PF ZF SF OF
test cl, 0x81 | ECX  |  CF PF ZF SF OF
test byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100  |  CF PF ZF SF OF
test al, 0x81 | EAX  |  CF PF ZF SF OF
test cx, dx | ECX EDX  |  CF PF ZF SF OF
test word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100  |  CF PF ZF SF OF
test cx, 0x8001 | ECX  |  CF PF ZF SF OF
test word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100  |  CF PF ZF SF OF
test ax, 0x8001 | EAX  |  CF PF ZF SF OF
test ecx, edx | ECX EDX  |  CF PF ZF SF OF
test dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100  |  CF PF ZF SF OF
test ecx, 0x80000001 | ECX  |  CF PF ZF SF OF
test dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100  |  CF PF ZF SF OF
test eax, 0x80000001 | EAX  |  CF PF ZF SF OF
test ah, ch | EAX ECX  |  CF PF ZF SF OF
# the unary operations
inc cl | ECX CF | ECX PF AF ZF SF OF CF
inc byte ptr [ebx] | EBX=0x200100 M1@0x200100 CF | M1@0x200100 PF AF ZF SF OF CF
inc cx | ECX CF | ECX PF AF ZF SF OF CF
inc word ptr [ebx] | EBX=0x200100 M2@0x200100 CF | M2@0x200100 PF AF ZF SF OF CF
inc ecx | ECX CF | ECX PF AF ZF SF OF CF
inc dword ptr [ebx] | EBX=0x200100 M4@0x200100 CF | M4@0x200100 PF AF ZF SF OF CF
dec cl | ECX CF | ECX PF AF ZF SF OF CF
dec byte ptr [ebx] | EBX=0x200100 M1@0x200100 CF | M1@0x200100 PF AF ZF SF OF CF
dec cx | ECX CF | ECX PF AF ZF SF OF CF
dec word ptr [ebx] | EBX=0x200100 M2@0x200100 CF | M2@0x200100 PF AF ZF SF OF CF
dec ecx | ECX CF | ECX PF AF ZF SF OF CF
dec dword ptr [ebx] | EBX=0x200100 M4@0x200100 CF | M4@0x200100 PF AF ZF SF OF CF
neg cl | ECX CF | ECX CF PF AF ZF SF OF
neg byte ptr [ebx] | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF PF AF ZF SF OF
neg cx | ECX CF | ECX CF PF AF ZF SF OF
neg word ptr [ebx] | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF PF AF ZF SF OF
neg ecx | ECX CF | ECX CF PF AF ZF SF OF
neg dword ptr [ebx] | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF PF AF ZF SF OF
not cl | ECX CF | ECX 
not byte ptr [ebx] | EBX=0x200100 M1@0x200100 CF | M1@0x200100 
not cx | ECX CF | ECX 
not word ptr [ebx] | EBX=0x200100 M2@0x200100 CF | M2@0x200100 
not ecx | ECX CF | ECX 
not dword ptr [ebx] | EBX=0x200100 M4@0x200100 CF | M4@0x200100 
# the multiplications and the divisions, the divisions by zero fault
mul cl | EAX ECX EDX@nzhigh | EAX CF OF
mul byte ptr [ebx] | EAX EBX=0x200100 M1@0x200100 EDX@nzhigh | EAX CF OF
mul cx | EAX ECX EDX@nzhigh | EAX EDX CF OF
mul word ptr [ebx] | EAX EBX=0x200100 M2@0x200100 EDX@nzhigh | EAX EDX CF OF
mul ecx | EAX ECX EDX@nzhigh | EAX EDX CF OF
mul dword ptr [ebx] | EAX EBX=0x200100 M4@0x200100 EDX@nzhigh | EAX EDX CF OF
imul cl | EAX ECX EDX@nzhigh | EAX CF OF
imul byte ptr [ebx] | EAX EBX=0x200100 M1@0x200100 EDX@nzhigh | EAX CF OF
imul cx | EAX ECX EDX@nzhigh | EAX EDX CF OF
imul word ptr [ebx] | EAX EBX=0x200100 M2@0x200100 EDX@nzhigh | EAX EDX CF OF
imul ecx | EAX ECX EDX@nzhigh | EAX EDX CF OF
imul dword ptr [ebx] | EAX EBX=0x200100 M4@0x200100 EDX@nzhigh | EAX EDX CF OF
div cl | EAX ECX EDX@nzhigh | EAX 
div byte ptr [ebx] | EAX EBX=0x200100 M1@0x200100 EDX@nzhigh | EAX 
div cx | EAX ECX EDX@nzhigh | EAX EDX 
div word ptr [ebx] | EAX EBX=0x200100 M2@0x200100 EDX@nzhigh | EAX EDX 
div ecx | EAX ECX EDX@nzhigh | EAX EDX 
div dword ptr [ebx] | EAX EBX=0x200100 M4@0x200100 EDX@nzhigh | EAX EDX 
idiv cl | EAX ECX EDX@nzhigh | EAX 
idiv byte ptr [ebx] | EAX EBX=0x200100 M1@0x200100 EDX@nzhigh | EAX 
idiv cx | EAX ECX EDX@nzhigh | EAX EDX 
idiv word ptr [ebx] | EAX EBX=0x200100 M2@0x200100 EDX@nzhigh | EAX EDX 
idiv ecx | EAX ECX EDX@nzhigh | EAX EDX 
idiv dword ptr [ebx] | EAX EBX=0x200100 M4@0x200100 EDX@nzhigh | EAX EDX 
imul cx, dx | ECX EDX | ECX CF OF
imul cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 | ECX CF OF
imul cx, dx, -7 | EDX | ECX CF OF
imul cx, dx, 0x1234 | EDX | ECX CF OF
imul cx, word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 | ECX CF OF
imul cx, word ptr [ebx], 0x1234 | EBX=0x200100 M2@0x200100 | ECX CF OF
imul ecx, edx | ECX EDX | ECX CF OF
imul ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100 | ECX CF OF
imul ecx, edx, -7 | EDX | ECX CF OF
imul ecx, edx, 0x1234 | EDX | ECX CF OF
imul ecx, dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 | ECX CF OF
imul ecx, dword ptr [ebx], 0x1234 | EBX=0x200100 M4@0x200100 | ECX CF OF
cbw | EAX EDX | EAX EDX
cwde | EAX EDX | EAX EDX
cwd | EAX EDX | EAX EDX
cdq | EAX EDX | EAX EDX
# the shifts and the rotations of each size and form
shl dl, cl | EDX ECX@count CF | EDX CF
shl dl, 1 | EDX CF | EDX CF OF
shl dl, 3 | EDX CF | EDX CF
shl byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
shl byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
shl byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
shl dx, cl | EDX ECX@count CF | EDX CF
shl dx, 1 | EDX CF | EDX CF OF
shl dx, 3 | EDX CF | EDX CF
shl word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
shl word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
shl word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
shl edx, cl | EDX ECX@count CF | EDX CF
shl edx, 1 | EDX CF | EDX CF OF
shl edx, 3 | EDX CF | EDX CF
shl dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
shl dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
shl dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
shr dl, cl | EDX ECX@count CF | EDX CF
shr dl, 1 | EDX CF | EDX CF OF
shr dl, 3 | EDX CF | EDX CF
shr byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
shr byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
shr byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
shr dx, cl | EDX ECX@count CF | EDX CF
shr dx, 1 | EDX CF | EDX CF OF
shr dx, 3 | EDX CF | EDX CF
shr word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
shr word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
shr word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
shr edx, cl | EDX ECX@count CF | EDX CF
shr edx, 1 | EDX CF | EDX CF OF
shr edx, 3 | EDX CF | EDX CF
shr dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
shr dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
shr dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
sar dl, cl | EDX ECX@count CF | EDX CF
sar dl, 1 | EDX CF | EDX CF OF
sar dl, 3 | EDX CF | EDX CF
sar byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
sar byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
sar byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
sar dx, cl | EDX ECX@count CF | EDX CF
sar dx, 1 | EDX CF | EDX CF OF
sar dx, 3 | EDX CF | EDX CF
sar word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
sar word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
sar word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
sar edx, cl | EDX ECX@count CF | EDX CF
sar edx, 1 | EDX CF | EDX CF OF
sar edx, 3 | EDX CF | EDX CF
sar dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
sar dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
sar dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rol dl, cl | EDX ECX@count CF | EDX CF
rol dl, 1 | EDX CF | EDX CF OF
rol dl, 3 | EDX CF | EDX CF
rol byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
rol byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rol byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rol dx, cl | EDX ECX@count CF | EDX CF
rol dx, 1 | EDX CF | EDX CF OF
rol dx, 3 | EDX CF | EDX CF
rol word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
rol word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rol word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rol edx, cl | EDX ECX@count CF | EDX CF
rol edx, 1 | EDX CF | EDX CF OF
rol edx, 3 | EDX CF | EDX CF
rol dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
rol dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rol dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
ror dl, cl | EDX ECX@count CF | EDX CF
ror dl, 1 | EDX CF | EDX CF OF
ror dl, 3 | EDX CF | EDX CF
ror byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
ror byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
ror byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
ror dx, cl | EDX ECX@count CF | EDX CF
ror dx, 1 | EDX CF | EDX CF OF
ror dx, 3 | EDX CF | EDX CF
ror word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
ror word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
ror word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
ror edx, cl | EDX ECX@count CF | EDX CF
ror edx, 1 | EDX CF | EDX CF OF
ror edx, 3 | EDX CF | EDX CF
ror dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
ror dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
ror dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rcl dl, cl | EDX ECX@count CF | EDX CF
rcl dl, 1 | EDX CF | EDX CF OF
rcl dl, 3 | EDX CF | EDX CF
rcl byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
rcl byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rcl byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rcl dx, cl | EDX ECX@count CF | EDX CF
rcl dx, 1 | EDX CF | EDX CF OF
rcl dx, 3 | EDX CF | EDX CF
rcl word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
rcl word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rcl word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rcl edx, cl | EDX ECX@count CF | EDX CF
rcl edx, 1 | EDX CF | EDX CF OF
rcl edx, 3 | EDX CF | EDX CF
rcl dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
rcl dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rcl dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
rcr dl, cl | EDX ECX@count CF | EDX CF
rcr dl, 1 | EDX CF | EDX CF OF
rcr dl, 3 | EDX CF | EDX CF
rcr byte ptr [ebx], cl | EBX=0x200100 M1@0x200100 ECX@count CF | M1@0x200100 CF
rcr byte ptr [ebx], 1 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF OF
rcr byte ptr [ebx], 5 | EBX=0x200100 M1@0x200100 CF | M1@0x200100 CF
rcr dx, cl | EDX ECX@count CF | EDX CF
rcr dx, 1 | EDX CF | EDX CF OF
rcr dx, 3 | EDX CF | EDX CF
rcr word ptr [ebx], cl | EBX=0x200100 M2@0x200100 ECX@count CF | M2@0x200100 CF
rcr word ptr [ebx], 1 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF OF
rcr word ptr [ebx], 5 | EBX=0x200100 M2@0x200100 CF | M2@0x200100 CF
rcr edx, cl | EDX ECX@count CF | EDX CF
rcr edx, 1 | EDX CF | EDX CF OF
rcr edx, 3 | EDX CF | EDX CF
rcr dword ptr [ebx], cl | EBX=0x200100 M4@0x200100 ECX@count CF | M4@0x200100 CF
rcr dword ptr [ebx], 1 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF OF
rcr dword ptr [ebx], 5 | EBX=0x200100 M4@0x200100 CF | M4@0x200100 CF
shld dx, ax, cl | EDX EAX ECX@count16 | EDX CF ZF SF PF
shld dx, ax, 7 | EDX EAX | EDX CF ZF SF PF
shld dx, ax, 1 | EDX EAX | EDX CF OF ZF SF PF
shld word ptr [ebx], ax, cl | EBX=0x200100 M2@0x200100 EAX ECX@count16 | M2@0x200100 CF ZF
shld word ptr [ebx], ax, 9 | EBX=0x200100 M2@0x200100 EAX | M2@0x200100 CF ZF
shld edx, eax, cl | EDX EAX ECX@count | EDX CF ZF SF PF
shld edx, eax, 7 | EDX EAX | EDX CF ZF SF PF
shld edx, eax, 1 | EDX EAX | EDX CF OF ZF SF PF
shld dword ptr [ebx], eax, cl | EBX=0x200100 M4@0x200100 EAX ECX@count | M4@0x200100 CF ZF
shld dword ptr [ebx], eax, 9 | EBX=0x200100 M4@0x200100 EAX | M4@0x200100 CF ZF
shrd dx, ax, cl | EDX EAX ECX@count16 | EDX CF ZF SF PF
shrd dx, ax, 7 | EDX EAX | EDX CF ZF SF PF
shrd dx, ax, 1 | EDX EAX | EDX CF OF ZF SF PF
shrd word ptr [ebx], ax, cl | EBX=0x200100 M2@0x200100 EAX ECX@count16 | M2@0x200100 CF ZF
shrd word ptr [ebx], ax, 9 | EBX=0x200100 M2@0x200100 EAX | M2@0x200100 CF ZF
shrd edx, eax, cl | EDX EAX ECX@count | EDX CF ZF SF PF
shrd edx, eax, 7 | EDX EAX | EDX CF ZF SF PF
shrd edx, eax, 1 | EDX EAX | EDX CF OF ZF SF PF
shrd dword ptr [ebx], eax, cl | EBX=0x200100 M4@0x200100 EAX ECX@count | M4@0x200100 CF ZF
shrd dword ptr [ebx], eax, 9 | EBX=0x200100 M4@0x200100 EAX | M4@0x200100 CF ZF
# the bit tests, the register offsets of the memory forms address a bit string
bt dx, cx | EDX ECX@count |  CF
bt dx, 37 | EDX |  CF
bt word ptr [ebx], cx | EBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 ECX@bitoff |  CF
bt word ptr [ebx], 3 | EBX=0x200100 M2@0x200100 |  CF
bt edx, ecx | EDX ECX@count |  CF
bt edx, 37 | EDX |  CF
bt dword ptr [ebx], ecx | EBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 ECX@bitoff |  CF
bt dword ptr [ebx], 3 | EBX=0x200100 M4@0x200100 |  CF
bts dx, cx | EDX ECX@count | EDX CF
bts dx, 37 | EDX | EDX CF
bts word ptr [ebx], cx | EBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 ECX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
bts word ptr [ebx], 3 | EBX=0x200100 M2@0x200100 | M2@0x200100 CF
bts edx, ecx | EDX ECX@count | EDX CF
bts edx, 37 | EDX | EDX CF
bts dword ptr [ebx], ecx | EBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 ECX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
bts dword ptr [ebx], 3 | EBX=0x200100 M4@0x200100 | M4@0x200100 CF
btr dx, cx | EDX ECX@count | EDX CF
btr dx, 37 | EDX | EDX CF
btr word ptr [ebx], cx | EBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 ECX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
btr word ptr [ebx], 3 | EBX=0x200100 M2@0x200100 | M2@0x200100 CF
btr edx, ecx | EDX ECX@count | EDX CF
btr edx, 37 | EDX | EDX CF
btr dword ptr [ebx], ecx | EBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 ECX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
btr dword ptr [ebx], 3 | EBX=0x200100 M4@0x200100 | M4@0x200100 CF
btc dx, cx | EDX ECX@count | EDX CF
btc dx, 37 | EDX | EDX CF
btc word ptr [ebx], cx | EBX=0x200100 M2@0x2000f0 M2@0x200100 M2@0x200110 ECX@bitoff | M2@0x2000f0 M2@0x200100 M2@0x200110 CF
btc word ptr [ebx], 3 | EBX=0x200100 M2@0x200100 | M2@0x200100 CF
btc edx, ecx | EDX ECX@count | EDX CF
btc edx, 37 | EDX | EDX CF
btc dword ptr [ebx], ecx | EBX=0x200100 M4@0x2000f0 M4@0x200100 M4@0x200110 ECX@bitoff | M4@0x2000f0 M4@0x200100 M4@0x200110 CF
btc dword ptr [ebx], 3 | EBX=0x200100 M4@0x200100 | M4@0x200100 CF
# the bit scans and counts, BSF and BSR keep the destination of zero
bsf cx, dx | ECX=0x55 EDX | ECX ZF
bsf cx, word ptr [ebx] | ECX=0x55 EBX=0x200100 M2@0x200100 | ECX ZF
bsf ecx, edx | ECX=0x55 EDX | ECX ZF
bsf ecx, dword ptr [ebx] | ECX=0x55 EBX=0x200100 M4@0x200100 | ECX ZF
bsr cx, dx | ECX=0x55 EDX | ECX ZF
bsr cx, word ptr [ebx] | ECX=0x55 EBX=0x200100 M2@0x200100 | ECX ZF
bsr ecx, edx | ECX=0x55 EDX | ECX ZF
bsr ecx, dword ptr [ebx] | ECX=0x55 EBX=0x200100 M4@0x200100 | ECX ZF
popcnt cx, dx | ECX=0x55 EDX | ECX ZF CF OF SF PF
popcnt cx, word ptr [ebx] | ECX=0x55 EBX=0x200100 M2@0x200100 | ECX ZF CF OF SF PF
popcnt ecx, edx | ECX=0x55 EDX | ECX ZF CF OF SF PF
popcnt ecx, dword ptr [ebx] | ECX=0x55 EBX=0x200100 M4@0x200100 | ECX ZF CF OF SF PF
lzcnt cx, dx | ECX=0x55 EDX | ECX CF ZF
lzcnt cx, word ptr [ebx] | ECX=0x55 EBX=0x200100 M2@0x200100 | ECX CF ZF
lzcnt ecx, edx | ECX=0x55 EDX | ECX CF ZF
lzcnt ecx, dword ptr [ebx] | ECX=0x55 EBX=0x200100 M4@0x200100 | ECX CF ZF
tzcnt cx, dx | ECX=0x55 EDX | ECX CF ZF
tzcnt cx, word ptr [ebx] | ECX=0x55 EBX=0x200100 M2@0x200100 | ECX CF ZF
tzcnt ecx, edx | ECX=0x55 EDX | ECX CF ZF
tzcnt ecx, dword ptr [ebx] | ECX=0x55 EBX=0x200100 M4@0x200100 | ECX CF ZF
bswap ecx | ECX | ECX
# the conditions of SETcc, CMOVcc and Jcc
seto cl | ECX=0x5500 CF ZF SF OF PF | ECX
seto byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setno cl | ECX=0x5500 CF ZF SF OF PF | ECX
setno byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setb cl | ECX=0x5500 CF ZF SF OF PF | ECX
setb byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setae cl | ECX=0x5500 CF ZF SF OF PF | ECX
setae byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
sete cl | ECX=0x5500 CF ZF SF OF PF | ECX
sete byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setne cl | ECX=0x5500 CF ZF SF OF PF | ECX
setne byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setbe cl | ECX=0x5500 CF ZF SF OF PF | ECX
setbe byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
seta cl | ECX=0x5500 CF ZF SF OF PF | ECX
seta byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
sets cl | ECX=0x5500 CF ZF SF OF PF | ECX
sets byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setns cl | ECX=0x5500 CF ZF SF OF PF | ECX
setns byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setp cl | ECX=0x5500 CF ZF SF OF PF | ECX
setp byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setnp cl | ECX=0x5500 CF ZF SF OF PF | ECX
setnp byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setl cl | ECX=0x5500 CF ZF SF OF PF | ECX
setl byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setge cl | ECX=0x5500 CF ZF SF OF PF | ECX
setge byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setle cl | ECX=0x5500 CF ZF SF OF PF | ECX
setle byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
setg cl | ECX=0x5500 CF ZF SF OF PF | ECX
setg byte ptr [ebx] | EBX=0x200100 CF ZF SF OF PF | M1@0x200100
cmove cx, dx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmove cx, word ptr [ebx] | ECX=0x77 EBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | ECX
cmove ecx, edx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmove ecx, dword ptr [ebx] | ECX=0x77 EBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | ECX
cmovl cx, dx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmovl cx, word ptr [ebx] | ECX=0x77 EBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | ECX
cmovl ecx, edx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmovl ecx, dword ptr [ebx] | ECX=0x77 EBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | ECX
cmova cx, dx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmova cx, word ptr [ebx] | ECX=0x77 EBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | ECX
cmova ecx, edx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmova ecx, dword ptr [ebx] | ECX=0x77 EBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | ECX
cmovnp cx, dx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmovnp cx, word ptr [ebx] | ECX=0x77 EBX=0x200100 M2@0x200100=0x1234 CF ZF SF OF | ECX
cmovnp ecx, edx | ECX=0x12345678 EDX=0x55 CF ZF SF OF PF | ECX
cmovnp ecx, dword ptr [ebx] | ECX=0x77 EBX=0x200100 M4@0x200100=0x1234 CF ZF SF OF | ECX
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
jmp ecx | ECX=0x20400 | PC | 0x400
jmp dword ptr [ebx] | EBX=0x200100 M4@0x200100=0x1fc00 | PC | -0x400
call .+0x400 | ESP=0x208000 | PC ESP M4@0x207ffc | 0x400
call ecx | ESP=0x208000 ECX=0x20400 | PC ESP M4@0x207ffc | 0x400
call dword ptr [ebx] | ESP=0x208000 EBX=0x200100 M4@0x200100=0x1fc00 | PC ESP M4@0x207ffc | -0x400
ret | ESP=0x208000 M4@0x208000=0x20400 | PC ESP | 0x400
ret 0x10 | ESP=0x208000 M4@0x208000=0x1fc00 | PC ESP | -0x400
loop .+0x40 | ECX@small | PC ECX | 0x40
loope .+0x40 | ECX@small ZF | PC ECX | 0x40
loopne .+0x40 | ECX@small ZF | PC ECX | 0x40
jecxz .+0x40 | ECX@small | PC | 0x40
# the moves of each size and form
mov cl, dl | ECX EDX | ECX
mov cl, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 | ECX
mov byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100=0x55 | M1@0x200100
mov cl, 0x81 | ECX | ECX
mov byte ptr [ebx], 0x81 | EBX=0x200100 M1@0x200100=0x55 | M1@0x200100
mov cx, dx | ECX EDX | ECX
mov cx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 | ECX
mov word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100=0x55 | M2@0x200100
mov cx, 0x8001 | ECX | ECX
mov word ptr [ebx], 0x8001 | EBX=0x200100 M2@0x200100=0x55 | M2@0x200100
mov ecx, edx | ECX EDX | ECX
mov ecx, dword ptr [ebx] | ECX EBX=0x200100 M4@0x200100 | ECX
mov dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100=0x55 | M4@0x200100
mov ecx, 0x80000001 | ECX | ECX
mov dword ptr [ebx], 0x80000001 | EBX=0x200100 M4@0x200100=0x55 | M4@0x200100
mov ah, dl | EAX EDX | EAX
mov al, byte ptr ds:[0x200100] | EAX M1@0x200100 | EAX
mov eax, dword ptr ds:[0x200100] | EAX M4@0x200100 | EAX
mov dword ptr ds:[0x200100], eax | EAX | M4@0x200100
mov word ptr ds:[0x200100], ax | EAX | M2@0x200100
movzx cx, dl | ECX EDX | ECX
movzx cx, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 | ECX
movsx cx, dl | ECX EDX | ECX
movsx cx, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 | ECX
movzx ecx, dl | ECX EDX | ECX
movzx ecx, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 | ECX
movsx ecx, dl | ECX EDX | ECX
movsx ecx, byte ptr [ebx] | ECX EBX=0x200100 M1@0x200100 | ECX
movzx ecx, dx | ECX EDX | ECX
movzx ecx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 | ECX
movsx ecx, dx | ECX EDX | ECX
movsx ecx, word ptr [ebx] | ECX EBX=0x200100 M2@0x200100 | ECX
lea cx, [ebx+edx*4+0x10] | ECX EBX EDX | ECX
lea ecx, [ebx+edx*4+0x10] | ECX EBX EDX | ECX
# the exchanges
xchg cl, dl | ECX EDX | ECX EDX
xchg byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100 | ECX M1@0x200100
xadd cl, dl | ECX EDX | ECX EDX CF PF AF ZF SF OF
xadd byte ptr [ebx], cl | ECX EBX=0x200100 M1@0x200100 | ECX M1@0x200100 CF PF AF ZF SF OF
cmpxchg cl, dl | EAX@pair ECX@pair EDX | EAX ECX ZF CF
cmpxchg byte ptr [ebx], dl | EAX@pair EBX=0x200100 M1@0x200100@pair EDX | EAX M1@0x200100 ZF CF
xchg cx, dx | ECX EDX | ECX EDX
xchg word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100 | ECX M2@0x200100
xadd cx, dx | ECX EDX | ECX EDX CF PF AF ZF SF OF
xadd word ptr [ebx], cx | ECX EBX=0x200100 M2@0x200100 | ECX M2@0x200100 CF PF AF ZF SF OF
cmpxchg cx, dx | EAX@pair ECX@pair EDX | EAX ECX ZF CF
cmpxchg word ptr [ebx], dx | EAX@pair EBX=0x200100 M2@0x200100@pair EDX | EAX M2@0x200100 ZF CF
xchg ecx, edx | ECX EDX | ECX EDX
xchg dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100 | ECX M4@0x200100
xadd ecx, edx | ECX EDX | ECX EDX CF PF AF ZF SF OF
xadd dword ptr [ebx], ecx | ECX EBX=0x200100 M4@0x200100 | ECX M4@0x200100 CF PF AF ZF SF OF
cmpxchg ecx, edx | EAX@pair ECX@pair EDX | EAX ECX ZF CF
cmpxchg dword ptr [ebx], edx | EAX@pair EBX=0x200100 M4@0x200100@pair EDX | EAX M4@0x200100 ZF CF
xchg ax, cx | EAX ECX | EAX ECX
xchg eax, ecx | EAX ECX | EAX ECX
cmpxchg8b qword ptr [ebx] | EAX@pair EDX=0 EBX=0x200100 ECX M8@0x200100@pair | EAX EDX M8@0x200100 ZF
# the stack
push cx | ESP=0x208000 ECX | ESP M2@0x207ffe
pop cx | ESP=0x208000 ECX M2@0x208000 | ESP ECX
push word ptr [ebx] | ESP=0x208000 EBX=0x200100 M2@0x200100 | ESP M2@0x207ffe
pop word ptr [ebx] | ESP=0x208000 EBX=0x200100 M2@0x208000 | ESP M2@0x200100
push ecx | ESP=0x208000 ECX | ESP M4@0x207ffc
pop ecx | ESP=0x208000 ECX M4@0x208000 | ESP ECX
push dword ptr [ebx] | ESP=0x208000 EBX=0x200100 M4@0x200100 | ESP M4@0x207ffc
pop dword ptr [ebx] | ESP=0x208000 EBX=0x200100 M4@0x208000 | ESP M4@0x200100
push -5 | ESP=0x208000 | ESP M4@0x207ffc
push 0x12345678 | ESP=0x208000 | ESP M4@0x207ffc
pushfd | ESP=0x208000 IF=1 CF ZF SF OF | ESP M4@0x207ffc
popfd | ESP=0x208000 M4@0x208000@flagword | ESP CF PF AF ZF SF OF
leave | ESP=0x208000 EBP=0x207f00 M4@0x207f00 | ESP EBP
enter 0x20, 0 | ESP=0x208000 EBP | ESP EBP M4@0x207ffc
pushad | ESP=0x208000 EAX ECX=7 EDX=0x55 EBX=3 EBP=4 ESI=5 EDI=6 | ESP M4@0x207ffc M4@0x207ff0 M4@0x207fe0
popad | ESP=0x207fe0 M4@0x207fe0 M4@0x207fe4 M4@0x207ffc | ESP EDI ESI EAX
# the flags
lahf | EAX CF PF AF ZF SF | EAX
sahf | EAX@ah | CF PF AF ZF SF
clc | CF | CF
stc | CF | CF
cmc | CF | CF
std | | DF
cld | DF=1 | DF
# the string instructions, with REP the count is RCX, DF is the direction
movsb | ESI=0x200100 EDI=0x200200 M1@0x200100 DF=0 | ESI EDI M1@0x200200
movsb | ESI=0x200100 EDI=0x200200 M1@0x200100 DF=1 | ESI EDI M1@0x200200
rep movsb | ESI=0x200100 EDI=0x200200 ECX@small M16@0x200100 | ESI EDI ECX M16@0x200200
stosb | EAX EDI=0x200200 DF | EDI M1@0x200200
rep stosb | EAX EDI=0x200200 ECX@small | EDI ECX M16@0x200200
lodsb | EAX ESI=0x200100 M1@0x200100 DF | EAX ESI
scasb | EAX@pair EDI=0x200100 M1@0x200100@pair | EDI CF PF AF ZF SF OF
repne scasb | EAX=0x41 EDI=0x200100 ECX@small M8@0x200100=0x4142434445464748 | EDI ECX ZF
repe scasb | EAX=0 EDI=0x200100 ECX@small M8@0x200104=0x41 | EDI ECX ZF
cmpsb | ESI=0x200100 EDI=0x200200 M1@0x200100@pair M1@0x200200@pair | ESI EDI CF PF AF ZF SF OF
repe cmpsb | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | ESI EDI ECX ZF
repne cmpsb | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | ESI EDI ECX ZF
movsw | ESI=0x200100 EDI=0x200200 M2@0x200100 DF=0 | ESI EDI M2@0x200200
movsw | ESI=0x200100 EDI=0x200200 M2@0x200100 DF=1 | ESI EDI M2@0x200200
rep movsw | ESI=0x200100 EDI=0x200200 ECX@small M16@0x200100 | ESI EDI ECX M16@0x200200
stosw | EAX EDI=0x200200 DF | EDI M2@0x200200
rep stosw | EAX EDI=0x200200 ECX@small | EDI ECX M16@0x200200
lodsw | EAX ESI=0x200100 M2@0x200100 DF | EAX ESI
scasw | EAX@pair EDI=0x200100 M2@0x200100@pair | EDI CF PF AF ZF SF OF
repne scasw | EAX=0x41 EDI=0x200100 ECX@small M8@0x200100=0x4142434445464748 | EDI ECX ZF
repe scasw | EAX=0 EDI=0x200100 ECX@small M8@0x200104=0x41 | EDI ECX ZF
cmpsw | ESI=0x200100 EDI=0x200200 M2@0x200100@pair M2@0x200200@pair | ESI EDI CF PF AF ZF SF OF
repe cmpsw | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | ESI EDI ECX ZF
repne cmpsw | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | ESI EDI ECX ZF
movsd | ESI=0x200100 EDI=0x200200 M4@0x200100 DF=0 | ESI EDI M4@0x200200
movsd | ESI=0x200100 EDI=0x200200 M4@0x200100 DF=1 | ESI EDI M4@0x200200
rep movsd | ESI=0x200100 EDI=0x200200 ECX@small M16@0x200100 | ESI EDI ECX M16@0x200200
stosd | EAX EDI=0x200200 DF | EDI M4@0x200200
rep stosd | EAX EDI=0x200200 ECX@small | EDI ECX M16@0x200200
lodsd | EAX ESI=0x200100 M4@0x200100 DF | EAX ESI
scasd | EAX@pair EDI=0x200100 M4@0x200100@pair | EDI CF PF AF ZF SF OF
repne scasd | EAX=0x41 EDI=0x200100 ECX@small M8@0x200100=0x4142434445464748 | EDI ECX ZF
repe scasd | EAX=0 EDI=0x200100 ECX@small M8@0x200104=0x41 | EDI ECX ZF
cmpsd | ESI=0x200100 EDI=0x200200 M4@0x200100@pair M4@0x200200@pair | ESI EDI CF PF AF ZF SF OF
repe cmpsd | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M8@0x200200=0x4142434445464748 M1@0x200203@byte | ESI EDI ECX ZF
repne cmpsd | ESI=0x200100 EDI=0x200200 ECX@small M8@0x200100=0x4142434445464748 M1@0x200202@byte | ESI EDI ECX ZF
# no effects on the registers
nop | EAX | EAX
pause | EAX | EAX
lfence | EAX | EAX
sfence | EAX | EAX
mfence | EAX | EAX
endbr32 | EAX | EAX
prefetcht0 byte ptr [ebx] | EBX=0x200100 | EBX
prefetcht1 byte ptr [ebx] | EBX=0x200100 | EBX
prefetcht2 byte ptr [ebx] | EBX=0x200100 | EBX
prefetchnta byte ptr [ebx] | EBX=0x200100 | EBX
prefetchw byte ptr [ebx] | EBX=0x200100 | EBX
clflush byte ptr [ebx] | EBX=0x200100 | EBX
nop dword ptr [ebx+eax*2+0x10] | EAX | EAX
nop word ptr [ebx] | EAX | EAX
# the packed integer operations, in the SSE, VEX.128, VEX.256 and MMX forms
paddb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddb mm0, mm1 | MM0 MM1 | MM0
paddb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddw mm0, mm1 | MM0 MM1 | MM0
paddw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddd mm0, mm1 | MM0 MM1 | MM0
paddd mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddq mm0, mm1 | MM0 MM1 | MM0
paddq mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubb mm0, mm1 | MM0 MM1 | MM0
psubb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubw mm0, mm1 | MM0 MM1 | MM0
psubw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubd mm0, mm1 | MM0 MM1 | MM0
psubd mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubq mm0, mm1 | MM0 MM1 | MM0
psubq mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddsb mm0, mm1 | MM0 MM1 | MM0
paddsb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddsw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddsw mm0, mm1 | MM0 MM1 | MM0
paddsw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubsb mm0, mm1 | MM0 MM1 | MM0
psubsb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubsw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubsw mm0, mm1 | MM0 MM1 | MM0
psubsw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddusb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddusb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddusb mm0, mm1 | MM0 MM1 | MM0
paddusb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
paddusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
paddusw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpaddusw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpaddusw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
paddusw mm0, mm1 | MM0 MM1 | MM0
paddusw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubusb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubusb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubusb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubusb mm0, mm1 | MM0 MM1 | MM0
psubusb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
psubusw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psubusw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsubusw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsubusw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psubusw mm0, mm1 | MM0 MM1 | MM0
psubusw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pmullw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmullw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmullw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmullw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmullw mm0, mm1 | MM0 MM1 | MM0
pmullw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pmulld xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulld xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmulld xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulld ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmulhw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmulhw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulhw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmulhw mm0, mm1 | MM0 MM1 | MM0
pmulhw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pmulhuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmulhuw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmulhuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmulhuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmuludq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmuludq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmuludq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmuludq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmuldq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmuldq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmuldq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmuldq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaddwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaddwd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaddwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaddwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
psadbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
psadbw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpsadbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpsadbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpavgb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpavgb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgb mm0, mm1 | MM0 MM1 | MM0
pavgb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pavgw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pavgw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpavgw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpavgw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pavgw mm0, mm1 | MM0 MM1 | MM0
pavgw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pminub xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminub xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminub xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminub ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminub mm0, mm1 | MM0 MM1 | MM0
pminub mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pminuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminuw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminud xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminud xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminud xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminud ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxub xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxub xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxub xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxub ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxub mm0, mm1 | MM0 MM1 | MM0
pmaxub mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pmaxuw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxuw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxuw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxuw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxud xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxud xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxud xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxud ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pminsw mm0, mm1 | MM0 MM1 | MM0
pminsw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pminsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pminsd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpminsd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpminsd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pmaxsw mm0, mm1 | MM0 MM1 | MM0
pmaxsw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pmaxsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pmaxsd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpmaxsd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpmaxsd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqb mm0, mm1 | MM0 MM1 | MM0
pcmpeqb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpeqw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqw mm0, mm1 | MM0 MM1 | MM0
pcmpeqw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpeqd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpeqd mm0, mm1 | MM0 MM1 | MM0
pcmpeqd mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpeqq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpeqq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpeqq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpeqq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtb mm0, mm1 | MM0 MM1 | MM0
pcmpgtb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpgtw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtw mm0, mm1 | MM0 MM1 | MM0
pcmpgtw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpgtd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pcmpgtd mm0, mm1 | MM0 MM1 | MM0
pcmpgtd mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pcmpgtq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pcmpgtq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpcmpgtq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpcmpgtq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pand xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pand xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpand xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpand ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pand mm0, mm1 | MM0 MM1 | MM0
pand mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pandn xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pandn xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpandn xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpandn ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pandn mm0, mm1 | MM0 MM1 | MM0
pandn mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
por xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
por xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpor xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpor ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
por mm0, mm1 | MM0 MM1 | MM0
por mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
pxor xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pxor xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpxor xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpxor ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pxor mm0, mm1 | MM0 MM1 | MM0
pxor mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpcklbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklbw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpcklbw mm0, mm1 | MM0 MM1 | MM0
punpcklbw mm0, dword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpcklwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklwd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpcklwd mm0, mm1 | MM0 MM1 | MM0
punpcklwd mm0, dword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpckldq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckldq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpckldq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckldq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckldq mm0, mm1 | MM0 MM1 | MM0
punpckldq mm0, dword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpcklqdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpcklqdq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpcklqdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpcklqdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhbw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhbw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhbw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhbw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhbw mm0, mm1 | MM0 MM1 | MM0
punpckhbw mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpckhwd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhwd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhwd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhwd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhwd mm0, mm1 | MM0 MM1 | MM0
punpckhwd mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpckhdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhdq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
punpckhdq mm0, mm1 | MM0 MM1 | MM0
punpckhdq mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
punpckhqdq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
punpckhqdq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpunpckhqdq xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpunpckhqdq ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packsswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packsswb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpacksswb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpacksswb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packssdw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packssdw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpackssdw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackssdw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packuswb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packuswb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpackuswb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackuswb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
packusdw xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
packusdw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpackusdw xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpackusdw ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pshufb xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
pshufb xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vpshufb xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vpshufb ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
pshufb mm0, mm1 | MM0 MM1 | MM0
pshufb mm0, qword ptr [ebx] | MM0 EBX=0x200100 M8@0x200100 | MM0
unpcklps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpcklps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vunpcklps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpcklps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpckhps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpckhps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vunpckhps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpckhps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpcklpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpcklpd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vunpcklpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpcklpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
unpckhpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
unpckhpd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vunpckhpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vunpckhpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vandps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vandps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andpd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andpd xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vandpd xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vandpd ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
orps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
orps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vorps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vorps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
xorps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
xorps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
vxorps xmm2, xmm0, xmm1 | XMM0@vec XMM1@vec XMM2 | YMM2
vxorps ymm2, ymm0, ymm1 | YMM0 YMM1 | YMM2
andnps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
andnps xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
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
psllw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psllw xmm0, 5 | XMM0@vec | XMM0
psllw xmm0, 40 | XMM0@vec | XMM0
vpsllw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsllw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsllw ymm2, ymm0, 3 | YMM0 | YMM2
psllw mm0, mm1 | MM0 MM1@count | MM0
psllw mm0, 7 | MM0 | MM0
pslld xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
pslld xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
pslld xmm0, 5 | XMM0@vec | XMM0
pslld xmm0, 40 | XMM0@vec | XMM0
vpslld xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpslld ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpslld ymm2, ymm0, 3 | YMM0 | YMM2
pslld mm0, mm1 | MM0 MM1@count | MM0
pslld mm0, 7 | MM0 | MM0
psllq xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psllq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psllq xmm0, 5 | XMM0@vec | XMM0
psllq xmm0, 40 | XMM0@vec | XMM0
vpsllq xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsllq ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsllq ymm2, ymm0, 3 | YMM0 | YMM2
psllq mm0, mm1 | MM0 MM1@count | MM0
psllq mm0, 7 | MM0 | MM0
psrlw xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrlw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psrlw xmm0, 5 | XMM0@vec | XMM0
psrlw xmm0, 40 | XMM0@vec | XMM0
vpsrlw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrlw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrlw ymm2, ymm0, 3 | YMM0 | YMM2
psrlw mm0, mm1 | MM0 MM1@count | MM0
psrlw mm0, 7 | MM0 | MM0
psrld xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrld xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psrld xmm0, 5 | XMM0@vec | XMM0
psrld xmm0, 40 | XMM0@vec | XMM0
vpsrld xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrld ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrld ymm2, ymm0, 3 | YMM0 | YMM2
psrld mm0, mm1 | MM0 MM1@count | MM0
psrld mm0, 7 | MM0 | MM0
psrlq xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrlq xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psrlq xmm0, 5 | XMM0@vec | XMM0
psrlq xmm0, 40 | XMM0@vec | XMM0
vpsrlq xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsrlq ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsrlq ymm2, ymm0, 3 | YMM0 | YMM2
psrlq mm0, mm1 | MM0 MM1@count | MM0
psrlq mm0, 7 | MM0 | MM0
psraw xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psraw xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
psraw xmm0, 5 | XMM0@vec | XMM0
psraw xmm0, 40 | XMM0@vec | XMM0
vpsraw xmm2, xmm0, xmm1 | XMM0@vec XMM1@count XMM2 | YMM2
vpsraw ymm2, ymm0, xmm1 | YMM0 XMM1@count | YMM2
vpsraw ymm2, ymm0, 3 | YMM0 | YMM2
psraw mm0, mm1 | MM0 MM1@count | MM0
psraw mm0, 7 | MM0 | MM0
psrad xmm0, xmm1 | XMM0@vec XMM1@count | XMM0
psrad xmm0, xmmword ptr [ebx] | XMM0@vec EBX=0x200100 M16@0x200100@count | XMM0
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
pshufd xmm0, xmmword ptr [ebx], 0x1b | EBX=0x200100 M16@0x200100@vec | XMM0
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
shufpd xmm0, xmmword ptr [ebx], 1 | XMM0@vec EBX=0x200100 M16@0x200100@vec | XMM0
insertps xmm0, xmm1, 0x5c | XMM0@vec XMM1@vec | XMM0
insertps xmm0, dword ptr [ebx], 0x20 | XMM0@vec EBX=0x200100 M4@0x200100 | XMM0
vinsertps xmm0, xmm1, xmm2, 0x91 | XMM1@vec XMM2@vec | YMM0
# the masks, the tests and the extensions
pmovmskb ecx, xmm0 | XMM0@vec | ECX
vpmovmskb ecx, ymm0 | YMM0 | ECX
pmovmskb ecx, mm0 | MM0 | ECX
ptest xmm0, xmm1 | XMM0@vec XMM1@vec | ZF CF
vptest ymm0, ymm1 | YMM0 YMM1 | ZF CF
pmovzxbw xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbw ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbw xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbw ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbw xmm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | XMM0
pmovzxbd xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbd ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbd xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbd ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbd xmm0, dword ptr [ebx] | EBX=0x200100 M4@0x200100 | XMM0
pmovzxbq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxbq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxbq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxbq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxbq xmm0, word ptr [ebx] | EBX=0x200100 M2@0x200100 | XMM0
pmovzxwd xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxwd ymm0, xmm1 | XMM1@vec | YMM0
pmovsxwd xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxwd ymm0, xmm1 | XMM1@vec | YMM0
pmovzxwd xmm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | XMM0
pmovzxwq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxwq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxwq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxwq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxwq xmm0, dword ptr [ebx] | EBX=0x200100 M4@0x200100 | XMM0
pmovzxdq xmm0, xmm1 | XMM1@vec | XMM0
vpmovzxdq ymm0, xmm1 | XMM1@vec | YMM0
pmovsxdq xmm0, xmm1 | XMM1@vec | XMM0
vpmovsxdq ymm0, xmm1 | XMM1@vec | YMM0
pmovzxdq xmm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | XMM0
# the moves of the vector registers
movaps xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movaps xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movaps xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovaps xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovaps ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovaps ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
movups xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movups xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movups xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovups xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovups ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovups ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
movapd xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movapd xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movapd xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovapd xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovapd ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovapd ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
movupd xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movupd xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movupd xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovupd xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovupd ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovupd ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
movdqa xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movdqa xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movdqa xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovdqa xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovdqa ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovdqa ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
movdqu xmm0, xmm1 | XMM0 XMM1@vec | XMM0
movdqu xmm0, xmmword ptr [ebx] | XMM0 EBX=0x200100 M16@0x200100@vec | XMM0
movdqu xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
vmovdqu xmm0, xmm1 | XMM0 XMM1@vec | YMM0
vmovdqu ymm0, ymmword ptr [ebx] | EBX=0x200100 M32@0x200100@ymm | YMM0
vmovdqu ymmword ptr [ebx], ymm1 | YMM1 EBX=0x200100 | M32@0x200100
lddqu xmm0, xmmword ptr [ebx] | EBX=0x200100 M16@0x200100@vec | XMM0
movntdq xmmword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 | M16@0x200100
movss xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movss xmm0, dword ptr [ebx] | XMM0@vec EBX=0x200100 M4@0x200100 | XMM0
movss dword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 M16@0x200100=0xffffffffffffffffffffffffffffffff | M16@0x200100
vmovss xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
vmovss xmm0, dword ptr [ebx] | EBX=0x200100 M4@0x200100 | YMM0
movsd xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movsd xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movsd qword ptr [ebx], xmm1 | XMM1@vec EBX=0x200100 M16@0x200100=0xffffffffffffffffffffffffffffffff | M16@0x200100
vmovsd xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
vmovsd xmm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | YMM0
movd xmm0, ecx | XMM0@vec ECX | XMM0
movd ecx, xmm0 | XMM0@vec ECX | ECX
movd xmm0, dword ptr [ebx] | XMM0@vec EBX=0x200100 M4@0x200100 | XMM0
movd dword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M4@0x200100
movq xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movq qword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M8@0x200100
movq xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
vmovd xmm0, ecx | ECX | YMM0
vmovq xmm0, xmm1 | XMM1@vec | YMM0
movd mm0, ecx | ECX | MM0
movd ecx, mm0 | MM0 | ECX
movq mm0, mm1 | MM1 | MM0
movq mm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | MM0
movq qword ptr [ebx], mm0 | MM0 EBX=0x200100 | M8@0x200100
movdq2q mm0, xmm1 | XMM1@vec | MM0
movq2dq xmm0, mm1 | XMM0@vec MM1 | XMM0
movhps xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movhps qword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M8@0x200100
vmovhps xmm0, xmm1, qword ptr [ebx] | XMM1@vec EBX=0x200100 M8@0x200100 | YMM0
movlps xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movlps qword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M8@0x200100
vmovlps xmm0, xmm1, qword ptr [ebx] | XMM1@vec EBX=0x200100 M8@0x200100 | YMM0
movhpd xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movhpd qword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M8@0x200100
vmovhpd xmm0, xmm1, qword ptr [ebx] | XMM1@vec EBX=0x200100 M8@0x200100 | YMM0
movlpd xmm0, qword ptr [ebx] | XMM0@vec EBX=0x200100 M8@0x200100 | XMM0
movlpd qword ptr [ebx], xmm0 | XMM0@vec EBX=0x200100 | M8@0x200100
vmovlpd xmm0, xmm1, qword ptr [ebx] | XMM1@vec EBX=0x200100 M8@0x200100 | YMM0
movhlps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
movlhps xmm0, xmm1 | XMM0@vec XMM1@vec | XMM0
vmovhlps xmm0, xmm1, xmm2 | XMM1@vec XMM2@vec | YMM0
movddup xmm0, xmm1 | XMM1@vec | XMM0
vmovddup ymm0, ymm1 | YMM1 | YMM0
movshdup xmm0, xmm1 | XMM1@vec | XMM0
vmovshdup ymm0, ymm1 | YMM1 | YMM0
movsldup xmm0, xmm1 | XMM1@vec | XMM0
vmovsldup ymm0, ymm1 | YMM1 | YMM0
movddup xmm0, qword ptr [ebx] | EBX=0x200100 M8@0x200100 | XMM0
pextrw ecx, xmm0, 5 | XMM0@vec | ECX
pinsrw xmm0, ecx, 3 | XMM0@vec ECX | XMM0
pextrb ecx, xmm0, 9 | XMM0@vec | ECX
pinsrd xmm0, ecx, 2 | XMM0@vec ECX | XMM0
# the packed string comparisons, the strings end with a zero element
pcmpistri xmm0, xmm1, 0x0 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x4 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x8 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0xc | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x1 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x10 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x30 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x40 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x12 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0xd | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x48 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistri xmm0, xmm1, 0x14 | XMM0@str XMM1@str | ECX CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x0 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x40 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x8 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpistrm xmm1, xmm2, 0x44 | XMM1@str XMM2@str | XMM0 CF ZF SF OF
pcmpestri xmm0, xmm1, 0x0 | XMM0@str XMM1@str EAX@len EDX@len | ECX CF ZF SF OF
pcmpestri xmm0, xmm1, 0xc | XMM0@str XMM1@str EAX@len EDX@len | ECX CF ZF SF OF
pcmpestri xmm0, xmm1, 0x1 | XMM0@str XMM1@str EAX@len EDX@len | ECX CF ZF SF OF
pcmpestrm xmm1, xmm2, 0x08 | XMM1@str XMM2@str EAX@len EDX@len | XMM0 CF ZF SF OF
pcmpistri xmm0, xmmword ptr [ebx], 0x0c | XMM0@str EBX=0x200100 M16@0x200100@str | ECX CF ZF
