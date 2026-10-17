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
