// What a review of the semantics of x86 and of the floating point found that the machine didn't do as a processor and Linux do, of a
// program of 64 bits. What each line says is what an AMD of AVX2 under Linux says of it (testsuite/data), but for what this says
// otherwise of.
//   state: a program starts with the selectors of Linux, and with the registers of MMX and of the masks.
//   x87: FSCALE of what is past any exponent, an infinity or a NaN; of a quiet and a signaling NaN, the quiet one; FSIN, FCOS, FSINCOS
//     and FPTAN of 2^63 or more set C2 and do nothing, and reduce by the π of 66 bits; the constants are rounded by the control word;
//     a precision control of 53 or 24 bits raises what its rounding does, and rounds what is below the normal numbers; C1 says that
//     what was stored was rounded up; and a stack that overflows or underflows is invalid, with the indefinite.
//   MXCSR: FTZ makes a zero of what is tiny before it is rounded up to the smallest normal number; VCVTPH2PS takes a denormal half
//     whatever DAZ says and doesn't say so, and VCVTPS2PH gives one whatever FTZ says.
//   prefixes: EIP as a base, with the address-size prefix; LOOP of ECX with it; XLAT in a segment and of 32 bits; and a null prefix
//     of a segment after that of FS doesn't take FS away. arch_prctl sets and gets the base of GS.
//   flags and frames: POPF changes what a program may; LEAVE and ENTER of 16 bits; BSF and BSR of zero leave all of the register.
//   MMX is in the state of x87: the top is 0, every tag valid, and a register that is written has an exponent of ones. FNSTENV has
//     ones in what is reserved, and FXSAVE doesn't write past the registers. AES-NI is what FIPS 197 says.
//   moves that are aligned fault of an address that isn't: SIGSEGV of the kernel.
//   traps: what is privileged, and INT to a gate that isn't the program's, is SIGSEGV of the kernel; INT 3 and INT1 are SIGTRAP, INT 4
//     SIGSEGV after it; SYSENTER, SYSEXIT and the instructions of a monitor SIGILL; INT 0x80 is the call of i386; SYSCALL leaves the
//     return address in RCX and the flags in R11; XGETBV says the states of x87 and SSE; a selector that isn't the program's
//     faults; SMSW, LSL, LAR, VERR, VERW, SLDT and STR say what Linux has; and the encodings d1 /6, f6 /1, f7 /1 and the hint NOPs
//     0f 19 to 0f 1e run.
//     (The host emulates SMSW of 32 bits, as it has UMIP, and leaves the upper half of the register: here it starts as zero.)
//   fetch: an instruction that goes on into a page that can't be executed faults at that page's first byte.
// Built with -mavx -maes -mf16c.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <ucontext.h>
#include <unistd.h>

typedef unsigned long long u64; typedef unsigned int u32; typedef unsigned short u16; typedef unsigned char u8;
static long sys3(long n,long a,long b,long c){long r;__asm__ volatile("syscall":"=a"(r):"a"(n),"D"(a),"S"(b),"d"(c):"rcx","r11","memory");return r;}
// What is said is kept and written by the call itself, so that nothing of libc runs between the instructions that are looked at.
static char obuf[1<<16]; static int opos;
static void flush(void){if(opos)sys3(1,1,(long)obuf,opos);opos=0;}
static void pc(char c){obuf[opos++]=c;if(opos>=(1<<16)-256)flush();}
static void ps(const char*s){while(*s)pc(*s++);}
static void px(u64 v,int n){for(int i=n-1;i>=0;i--)pc("0123456789abcdef"[(v>>(4*i))&15]);}
static void pb(const void*p,int n){const u8*b=p;for(int i=n-1;i>=0;i--)px(b[i],2);}
static void nl(void){pc('\n');}
#define P(...) do { opos += snprintf(obuf + opos, sizeof obuf - opos, __VA_ARGS__); } while (0)

static void state(void){ u64 a,b,c,d;
  __asm__ volatile("mov %%ds,%%eax; mov %%cs,%%ebx; mov %%ss,%%ecx; push %%fs; pop %%rdx":"=a"(a),"=b"(b),"=c"(c),"=d"(d)); ps("seg ");px(a,4);px(b,4);px(c,4);px(d,4);nl();
  __asm__ volatile("mov %%es,%%eax; mov %%gs,%%ebx":"=a"(a),"=b"(b)); ps("seg ");px(a,4);px(b,4);nl();
  __asm__ volatile("movq %%mm3,%%rax; emms":"=a"(a)); ps("mm ");px(a,16);nl(); }

typedef struct{u64 m;u16 e;} __attribute__((packed)) ld;
static void pl(const char*s,ld v,u16 sw){ps(s);pc(' ');px(v.e,4);pc(':');px(v.m,16);ps(" sw=");px(sw&0x47ff,4);nl();}
#define LD(e,m) ((ld){m,e})
static void bin(const char*n,int op,ld a,ld b,u16 cw){ld r;u16 sw;u16 d=0x37f;
  switch(op){
  case 0: __asm__ volatile("fninit; fldcw %[cw]; fldt %[b]; fldt %[a]; fscale; fnstsw %[sw]; fstpt %[r]; fstp %%st(0); fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[b]"m"(b),[cw]"m"(cw),[d]"m"(d));break;
  case 1: __asm__ volatile("fninit; fldcw %[cw]; fldt %[b]; fldt %[a]; faddp; fnstsw %[sw]; fstpt %[r]; fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[b]"m"(b),[cw]"m"(cw),[d]"m"(d));break;
  case 2: __asm__ volatile("fninit; fldcw %[cw]; fldt %[b]; fldt %[a]; fmulp; fnstsw %[sw]; fstpt %[r]; fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[b]"m"(b),[cw]"m"(cw),[d]"m"(d));break;
  case 3: __asm__ volatile("fninit; fldcw %[cw]; fldt %[b]; fldt %[a]; fdivp; fnstsw %[sw]; fstpt %[r]; fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[b]"m"(b),[cw]"m"(cw),[d]"m"(d));break;
  }
  pl(n,r,sw);}
static void un(const char*n,int op,ld a,u16 cw){ld r,r2={0,0};u16 sw;u16 d=0x37f;
  switch(op){
  case 0: __asm__ volatile("fninit; fldcw %[cw]; fldt %[a]; fsin; fnstsw %[sw]; fstpt %[r]; fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[cw]"m"(cw),[d]"m"(d));break;
  case 1: __asm__ volatile("fninit; fldcw %[cw]; fldt %[a]; fcos; fnstsw %[sw]; fstpt %[r]; fldcw %[d]":[r]"=m"(r),[sw]"=m"(sw):[a]"m"(a),[cw]"m"(cw),[d]"m"(d));break;
  case 2: __asm__ volatile("fninit; fldcw %[cw]; fldt %[a]; fptan; fnstsw %[sw]; fstpt %[r]; fstpt %[r2]; fldcw %[d]":[r]"=m"(r),[r2]"=m"(r2),[sw]"=m"(sw):[a]"m"(a),[cw]"m"(cw),[d]"m"(d));break;
  case 3: __asm__ volatile("fninit; fldcw %[cw]; fldt %[a]; fsincos; fnstsw %[sw]; fstpt %[r]; fstpt %[r2]; fldcw %[d]":[r]"=m"(r),[r2]"=m"(r2),[sw]"=m"(sw):[a]"m"(a),[cw]"m"(cw),[d]"m"(d));break;
  }
  pl(n,r,sw); if(op>=2) pl(" second",r2,0);}
static void cst(u16 cw){ld r[5];u16 d=0x37f;
  __asm__ volatile("fninit; fldcw %[cw]; fldpi; fstpt %[a]; fldl2t; fstpt %[b]; fldl2e; fstpt %[c]; fldlg2; fstpt %[e]; fldln2; fstpt %[f]; fldcw %[d]":[a]"=m"(r[0]),[b]"=m"(r[1]),[c]"=m"(r[2]),[e]"=m"(r[3]),[f]"=m"(r[4]):[cw]"m"(cw),[d]"m"(d));
  ps("consts cw=");px(cw,4);nl(); for(int i=0;i<5;i++)pl(" c",r[i],0);}

static void x87(void){
  ld one=LD(0x3fff,0x8000000000000000ull), inf=LD(0x7fff,0x8000000000000000ull), ninf=LD(0xffff,0x8000000000000000ull), zero=LD(0,0);
  ld qnan=LD(0x7fff,0xc000000000000000ull), snan=LD(0x7fff,0x8000000000000001ull), tiny=LD(0,1), nz=LD(0x8000,0);
  bin("fscale 1 2^31",0,one,LD(0x401e,0x8000000000000000ull),0x37f);
  bin("fscale 1 1e10",0,one,LD(0x4020,0x9502f90000000000ull),0x37f);
  bin("fscale 1 -1e10",0,one,LD(0xc020,0x9502f90000000000ull),0x37f);
  bin("fscale 1 inf",0,one,inf,0x37f);
  bin("fscale 1 -inf",0,one,ninf,0x37f);
  bin("fscale 0 inf",0,zero,inf,0x37f);
  bin("fscale inf -inf",0,inf,ninf,0x37f);
  bin("fscale inf inf",0,ninf,inf,0x37f);
  bin("fscale 1 nan",0,one,qnan,0x37f);
  bin("fscale snan 1",0,snan,one,0x37f);
  bin("fscale tiny 32500",0,tiny,LD(0x400d,0xfde8000000000000ull),0x37f);
  bin("fscale 1 3.7",0,one,LD(0x4000,0xeccccccccccccccdull),0x37f);
  bin("fscale 1 -3.7",0,one,LD(0xc000,0xeccccccccccccccdull),0x37f);
  bin("fscale 1.5 -16390",0,LD(0x3fff,0xc000000000000001ull),LD(0xc00d,0x800c000000000000ull),0x37f);
  bin("fscale 1.5 -16390 up",0,LD(0x3fff,0xc000000000000001ull),LD(0xc00d,0x800c000000000000ull),0xb7f);
  bin("fscale -0 5",0,nz,LD(0x4001,0xa000000000000000ull),0x37f);
  bin("fscale tiny tiny",0,tiny,tiny,0x37f);
  bin("fscale 1 tiny",0,one,tiny,0x37f);
  bin("fscale 3 20000",0,LD(0x4000,0xc000000000000000ull),LD(0x400d,0x9c40000000000000ull),0x37f);
  bin("fscale 3 20000 rtz",0,LD(0x4000,0xc000000000000000ull),LD(0x400d,0x9c40000000000000ull),0xf7f);
  bin("fadd qnan snan",1,qnan,snan,0x37f);
  bin("fadd snan qnan",1,snan,qnan,0x37f);
  bin("fmul snan2 qnan",2,LD(0xffff,0xbfffffffffffffffull),qnan,0x37f);
  bin("fdiv snan snan2",3,snan,LD(0x7fff,0x8000000000000002ull),0x37f);
  bin("fadd qnan qnan2",1,qnan,LD(0xffff,0xc000000000000005ull),0x37f);
  ld pi=LD(0x4000,0xc90fdaa22168c235ull);
  un("fsin pi",0,pi,0x37f); un("fcos pi",1,pi,0x37f);
  un("fsin 2^31",0,LD(0x401e,0x8000000000000000ull),0x37f);
  un("fsin 2^63-",0,LD(0x403d,0xffffffffffffffffull),0x37f);
  un("fcos 2^63",1,LD(0x403e,0x8000000000000000ull),0x37f);
  un("fsin 2^63",0,LD(0x403e,0x8000000000000000ull),0x37f);
  un("fptan 2^70",2,LD(0x4045,0x8000000000000000ull),0x37f);
  un("fsincos -2^64",3,LD(0xc03f,0x8000000000000000ull),0x37f);
  un("fsin inf",0,inf,0x37f);
  cst(0x37f);cst(0x77f);cst(0xb7f);cst(0xf7f);
  // precision control
  bin("pc53 1*(2-2^-63)",2,one,LD(0x3fff,0xffffffffffffffffull),0x27f);
  bin("pc53 0+tiny",1,zero,tiny,0x27f);
  bin("pc24 1+2^-30",1,one,LD(0x3fe1,0x8000000000000000ull),0x07f);
  bin("pc53 1/3",3,LD(0x4000,0xc000000000000000ull),one,0x27f);
  bin("1/3",3,LD(0x4000,0xc000000000000000ull),one,0x37f);
  bin("2/3",3,LD(0x4000,0xc000000000000000ull),LD(0x4000,0x8000000000000000ull),0x37f);
  { int v; u16 sw; ld a=LD(0x3fff,0xc000000000000000ull); long long q; float f; double dd; ld t; u8 bcd[10];
    __asm__ volatile("fninit; fldt %[a]; fistpl %[v]; fnstsw %[sw]":[v]"=m"(v),[sw]"=m"(sw):[a]"m"(a)); ps("fistpl 1.5 ");px(v,8);ps(" sw=");px(sw,4);nl();
    a=LD(0xbfff,0xc000000000000000ull);
    __asm__ volatile("fninit; fldt %[a]; fistpl %[v]; fnstsw %[sw]":[v]"=m"(v),[sw]"=m"(sw):[a]"m"(a)); ps("fistpl -1.5 ");px(v,8);ps(" sw=");px(sw,4);nl();
    a=LD(0x4000,0xa000000000000000ull);
    __asm__ volatile("fninit; fldt %[a]; fistpl %[v]; fnstsw %[sw]":[v]"=m"(v),[sw]"=m"(sw):[a]"m"(a)); ps("fistpl 2.5 ");px(v,8);ps(" sw=");px(sw,4);nl();
    a=LD(0x3fff,0xffffffffffffffffull);
    __asm__ volatile("fninit; fldt %[a]; fistpq %[v]; fnstsw %[sw]":[v]"=m"(q),[sw]"=m"(sw):[a]"m"(a)); ps("fistpq ");px(q,16);ps(" sw=");px(sw,4);nl();
    __asm__ volatile("fninit; fldt %[a]; fstps %[v]; fnstsw %[sw]":[v]"=m"(f),[sw]"=m"(sw):[a]"m"(a)); ps("fstps ");px(*(u32*)&f,8);ps(" sw=");px(sw,4);nl();
    __asm__ volatile("fninit; fldt %[a]; fstpl %[v]; fnstsw %[sw]":[v]"=m"(dd),[sw]"=m"(sw):[a]"m"(a)); ps("fstpl ");px(*(u64*)&dd,16);ps(" sw=");px(sw,4);nl();
    a=LD(0x3fff,0x8000000000000001ull);
    __asm__ volatile("fninit; fldt %[a]; fstpl %[v]; fnstsw %[sw]":[v]"=m"(dd),[sw]"=m"(sw):[a]"m"(a)); ps("fstpl dn ");px(*(u64*)&dd,16);ps(" sw=");px(sw,4);nl();
    a=LD(0x4002,0xa666666666666666ull);
    __asm__ volatile("fninit; fldt %[a]; fbstp %[v]; fnstsw %[sw]":[v]"=m"(bcd),[sw]"=m"(sw):[a]"m"(a)); ps("fbstp ");pb(bcd,10);ps(" sw=");px(sw,4);nl();
    a=LD(0x4002,0xa000000000000000ull); ld b=LD(0x4000,0xc000000000000000ull);
    __asm__ volatile("fninit; fldt %[b]; fldt %[a]; fprem; fstpt %[t]; fnstsw %[sw]; fstp %%st(0)":[t]"=m"(t),[sw]"=m"(sw):[a]"m"(a),[b]"m"(b)); ps("fprem fstpt sw=");px(sw,4);nl();
    __asm__ volatile("fninit; fld1;fld1;fld1;fld1;fld1;fld1;fld1;fld1;fld1; fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("overflow",t,sw);
    __asm__ volatile("fninit; fstpt %[t]; fnstsw %[sw]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fstp",t,sw);
    __asm__ volatile("fninit; fld1; faddp; fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow faddp",t,sw);
    __asm__ volatile("fninit; fld1; fadd %%st(3),%%st; fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fadd st3",t,sw);
    __asm__ volatile("fninit; fsqrt; fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fsqrt",t,sw);
    __asm__ volatile("fninit; fld1; fxch %%st(1); fnstsw %[sw]; fstpt %[t]; fstp %%st(0)":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fxch",t,sw);
    __asm__ volatile("fninit; fld1; fcomi %%st(2),%%st; fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fcomi",t,sw);
    __asm__ volatile("fninit; fistpl %[v]; fnstsw %[sw]":[v]"=m"(v),[sw]"=m"(sw)); ps("underflow fistpl ");px(v,8);ps(" sw=");px(sw,4);nl();
    __asm__ volatile("fninit; fld %%st(0); fnstsw %[sw]; fstpt %[t]":[t]"=m"(t),[sw]"=m"(sw)); pl("underflow fld st0",t,sw);
  }
  }

static u64 mul(u64 a,u64 b,u32 csr,u32*out){u32 c=csr;double x,y;*(u64*)&x=a;*(u64*)&y=b;
 __asm__ volatile("ldmxcsr %[c]; mulsd %[y],%[x]; stmxcsr %[c]":[x]"+x"(x),[c]"+m"(c):[y]"x"(y)); *out=c; c=0x1f80; __asm__ volatile("ldmxcsr %0"::"m"(c)); return *(u64*)&x;}
static void ftz(void){u32 o;u64 r;
 r=mul(0x0010000000000000ull,0x3fe0000000000000ull,0x9f80,&o);ps("ftz exact tiny ");px(r,16);pc(' ');px(o,4);nl();
 r=mul(0x0010000000000000ull,0x3fefffffffffffffull,0x9f80,&o);ps("ftz roundup ");px(r,16);pc(' ');px(o,4);nl();
 r=mul(0x0010000000000000ull,0x3fe8000000000001ull,0x9f80,&o);ps("ftz inexact ");px(r,16);pc(' ');px(o,4);nl();
 r=mul(0x0010000000000000ull,0x3fefffffffffffffull,0x1f80,&o);ps("roundup ");px(r,16);pc(' ');px(o,4);nl();
 }

static u64 tls[4]={0x1111,0x2222,0x3333,0x4444}; static u8 tab[300];
static void prefixes(void){ u64 a,b,c; for(int i=0;i<300;i++)tab[i]=i*7;
  // EIP-relative with address-size prefix
  static u32 v=0xabcdef01;
  __asm__ volatile("addr32 mov %c[v](%%rip),%%eax":"=a"(a):[v]"i"(&v)); ps("eip mov ");px(a,16);nl();
  __asm__ volatile("addr32 lea %c[v](%%rip),%%rcx":"=c"(c):[v]"i"(&v)); ps("eip lea ");px(c==(u64)&v,1);nl();
  // loop with addr32
  c=0xffffffff00000003ull; a=0; __asm__ volatile("1: inc %%rax; addr32 loop 1b":"+a"(a),"+c"(c)); ps("loopl ");px(a,4);pc(' ');px(c,16);nl();
  c=0xffffffff00000003ull; a=0; __asm__ volatile("xor %%edx,%%edx; 1: inc %%rax; cmp $2,%%rax; addr32 loopne 1b":"+a"(a),"+c"(c)::"rdx"); ps("loopnel ");px(a,4);pc(' ');px(c,16);nl();
  // fs base
  u64 libc_fs; sys3(158,0x1003,(long)&libc_fs,0); sys3(158,0x1002,(long)tls,0);
  __asm__ volatile("mov %%fs:8,%%rax":"=a"(a)); ps("fs:8 ");px(a,8);nl();
  __asm__ volatile(".byte 0x64,0x3e,0x48,0x8b,0x0c,0x25,0x08,0x00,0x00,0x00":"=c"(c)); ps("fs ds ");px(c,8);nl();
  __asm__ volatile(".byte 0x64,0x26,0x48,0x8b,0x0c,0x25,0x10,0x00,0x00,0x00":"=c"(c)); ps("fs es ");px(c,8);nl();
  __asm__ volatile(".byte 0x2e,0x64,0x48,0x8b,0x0c,0x25,0x18,0x00,0x00,0x00":"=c"(c)); ps("cs fs ");px(c,8);nl();
  // xlat
  a=0x1105; __asm__ volatile("xlat":"+a"(a):"b"(tab)); ps("xlat ");px(a,8);nl();
  sys3(158,0x1002,(long)tab,0);
  a=0x1107; __asm__ volatile(".byte 0x64; xlat":"+a"(a):"b"(16L)); ps("fs xlat ");px(a,8);nl();
  a=0x1109; __asm__ volatile(".byte 0x67; xlat":"+a"(a):"b"(0xffffffff00000000ull+(u64)tab)); ps("addr32 xlat ");px(a,8);nl();
  // gs base by arch_prctl
  a=sys3(158,0x1001,(long)tls,0); ps("set gs ");px(a,16);nl();
  a=sys3(158,0x1004,(long)&b,0); ps("get gs ");px(a,16);pc(' ');px(b==(u64)tls,1);nl();
  __asm__ volatile("mov %%gs:16,%%rax":"=a"(a)); ps("gs:16 ");px(a,8);nl();
  a=sys3(158,0x1003,(long)&b,0); sys3(158,0x1002,libc_fs,0); ps("get fs ");px(a,16);pc(' ');px(b==(u64)tab,1);nl();
  a=sys3(158,0x1001,0x800000000000ull,0); ps("set gs bad ");px(a,16);nl();
  a=sys3(158,0x1004,1,0); ps("get gs fault ");px(a,16);nl();
  }

static void frames(void){ u64 a,b,c,d;
  __asm__ volatile("pushfq; pop %%rbx; push $-257; popfq; pushfq; pop %%rax; push %%rbx; popfq":"=a"(a),"=b"(b)); ps("popf -257 ");px(a,16);nl();
  __asm__ volatile("pushfq; pop %%rbx; push $0; popfq; pushfq; pop %%rax; push %%rbx; popfq":"=a"(a),"=b"(b)); ps("popf 0 ");px(a,16);nl();
  __asm__ volatile("pushfq; pop %%rbx; pushw $0x0cd5; popfw; pushfq; pop %%rax; push %%rbx; popfq":"=a"(a),"=b"(b)); ps("popfw ");px(a,16);nl();
  // 66 leave / enter
  { u64 st[16]; for(int i=0;i<16;i++)st[i]=0x1111111111110000ull+i; u64 rbp,rsp;
    __asm__ volatile("mov %%rsp,%%r8; mov %%rbp,%%r9; lea 64(%[st]),%%rbp; mov $0x7777777777777777,%%rax; mov %%rax,%%rsp; .byte 0x66,0xc9; mov %%rsp,%%rcx; mov %%rbp,%%rdx; mov %%r8,%%rsp; mov %%r9,%%rbp":"=c"(rsp),"=d"(rbp):[st]"b"(st):"rax","r8","r9","memory");
    ps("leavew rsp+");px(rsp-(u64)st,4);ps(" rbp ");px(rbp==(((u64)st+64)&~0xffffull)+8,1);nl();
    __asm__ volatile("mov %%rsp,%%r8; mov %%rbp,%%r9; lea 64(%[st]),%%rsp; mov $0x7777777777771234,%%rbp; .byte 0x66,0xc8,0x10,0x00,0x00; mov %%rsp,%%rcx; mov %%rbp,%%rdx; mov %%r8,%%rsp; mov %%r9,%%rbp":"=c"(rsp),"=d"(rbp):[st]"b"(st):"rax","r8","r9","memory");
    ps("enterw rsp+");px(rsp-(u64)st,4);ps(" rbp ");px(rbp>>16,12);pc(' ');px((rbp&0xffff)==(((u64)st+62)&0xffff),1);ps(" pushed ");px(st[7],16);nl();
    for(int i=0;i<16;i++)st[i]=0x1111111111110000ull+i;
    __asm__ volatile("mov %%rsp,%%r8; mov %%rbp,%%r9; lea 64(%[st]),%%rsp; lea 120(%[st]),%%rbp; .byte 0x66,0xc8,0x08,0x00,0x03; mov %%rsp,%%rcx; mov %%rbp,%%rdx; mov %%r8,%%rsp; mov %%r9,%%rbp":"=c"(rsp),"=d"(rbp):[st]"b"(st):"rax","r8","r9","memory");
    ps("enterw 3 rsp+");px(rsp-(u64)st,4);ps(" rbp+");px(rbp-(u64)st,4);ps(" frame ");px((st[7]&0xffff)==(((u64)st+62)&0xffff),1);px((st[7]>>48)==(((u64)st+120)&0xffff),1);
    ps(" levels ");px((st[7]>>16)&0xffffffff,8);ps(" st6 ");px(st[6]>>32,8);nl(); }
  // bsr / bsf with a zero source
  d=0x1234567890abcdefull; a=0; __asm__ volatile("bsr %%eax,%%edx":"+d"(d):"a"(a)); ps("bsr32 0 ");px(d,16);nl();
  d=0x1234567890abcdefull; a=0; __asm__ volatile("bsf %%eax,%%edx":"+d"(d):"a"(a)); ps("bsf32 0 ");px(d,16);nl();
  d=0x1234567890abcdefull; a=0x10; __asm__ volatile("bsr %%eax,%%edx":"+d"(d):"a"(a)); ps("bsr32 16 ");px(d,16);nl();
  d=0x1234567890abcdefull; static u32 z=0; __asm__ volatile("bsr %1,%%edx":"+d"(d):"m"(z)); ps("bsr32 m0 ");px(d,16);nl();
  // MMX and the x87 state
  { struct{u64 m;u16 e;}__attribute__((packed)) t; u16 sw; u8 env[28]; u8 fx[512] __attribute__((aligned(16)));
    // The registers hold what the last instructions left, whatever the tags say: zeros, from here.
    __asm__ volatile("fninit; fldz; fldz; fldz; fldz; fldz; fldz; fldz; fldz; fstp %st(0); fstp %st(0); fstp %st(0); fstp %st(0); fstp %st(0); fstp %st(0); fstp %st(0); fstp %st(0)");
    a=0x1122334455667788ull;
    __asm__ volatile("fninit; fld1; movq %%rax,%%mm0; fnstsw %[sw]; fnstenv %[env]; fxsave %[fx]; emms":[sw]"=m"(sw),[env]"=m"(env),[fx]"=m"(fx):"a"(a));
    ps("mmx sw ");px(sw,4);ps(" tags ");px(*(u16*)(env+8),4);ps(" st0 ");pb(fx+32,10);ps(" st1 ");pb(fx+48,10);ps(" ftw ");px(fx[4],2);nl();
    __asm__ volatile("fninit; fld1; fldpi; movq %%mm0,%%rax; movq %%mm7,%%rcx; fnstsw %[sw]; emms":[sw]"=m"(sw),"=a"(a),"=c"(c)); ps("mmx reads ");px(a,16);pc(' ');px(c,16);ps(" sw ");px(sw,4);nl();
    a=5; __asm__ volatile("fninit; fld1; movq %%rax,%%mm3; paddq %%mm3,%%mm3; fxsave %[fx]; emms; fnstenv %[env]; fninit":[env]"=m"(env),[fx]"=m"(fx):"a"(a));
    ps("mmx paddq st3 ");pb(fx+32+48,10);ps(" st7 ");pb(fx+32+112,10);ps(" emms tags ");px(*(u16*)(env+8),4);nl();
    __asm__ volatile("fninit; fnstenv %[env]; fninit":[env]"=m"(env)); ps("fnstenv ");pb(env,28);nl();
    for(int i=0;i<512;i++)fx[i]=0xa5; __asm__ volatile("fninit; fxsave %[fx]":[fx]"=m"(fx)); ps("fxsave tail ");px(fx[415],2);px(fx[416],2);px(fx[463],2);px(fx[464],2);px(fx[511],2);ps(" head ");pb(fx,8);ps(" mxcsr ");pb(fx+24,4);nl(); }
  // AES-NI
  { u8 st[16],k[16],o[16]; for(int i=0;i<16;i++){st[i]=i*17;k[i]=0xa0+i;}
#define AES(name,insn) __asm__ volatile("movdqu %1,%%xmm0; movdqu %2,%%xmm1; " insn "; movdqu %%xmm0,%0":"=m"(o):"m"(st),"m"(k):"xmm0","xmm1"); ps(name " ");pb(o,16);nl();
    AES("aesenc","aesenc %%xmm1,%%xmm0") AES("aesenclast","aesenclast %%xmm1,%%xmm0") AES("aesdec","aesdec %%xmm1,%%xmm0") AES("aesdeclast","aesdeclast %%xmm1,%%xmm0")
    AES("aesimc","aesimc %%xmm1,%%xmm0") AES("aeskeygenassist","aeskeygenassist $0x1b,%%xmm1,%%xmm0") AES("vaesenc","vaesenc %%xmm1,%%xmm0,%%xmm0") }
  // F16C and MXCSR
  { u32 csr; float f[4]={0}; u16 hv[8]={0}; u32 fi[4];
#define PH2PS(name,H,CSR) csr=CSR; hv[0]=H; __asm__ volatile("ldmxcsr %[c]; vmovdqu %[h],%%xmm1; vcvtph2ps %%xmm1,%%xmm0; vmovups %%xmm0,%[f]; stmxcsr %[c]":[f]"=m"(fi),[c]"+m"(csr):[h]"m"(hv):"xmm0","xmm1"); ps(name " ");px(fi[0],8);ps(" csr ");px(csr,4);nl();
    PH2PS("ph2ps denormal",0x0001,0x1f80) PH2PS("ph2ps denormal daz",0x0001,0x1fc0) PH2PS("ph2ps snan",0x7c01,0x1f80)
#define PS2PH(name,F,CSR) csr=CSR; fi[0]=F;fi[1]=fi[2]=fi[3]=0; __asm__ volatile("ldmxcsr %[c]; vmovups %[f],%%xmm1; vcvtps2ph $0,%%xmm1,%%xmm0; vmovdqu %%xmm0,%[h]; stmxcsr %[c]":[h]"=m"(hv),[c]"+m"(csr):[f]"m"(fi):"xmm0","xmm1"); ps(name " ");px(hv[0],4);ps(" csr ");px(csr,4);nl();
    PS2PH("ps2ph tiny",0x33800000,0x1f80) PS2PH("ps2ph tiny ftz",0x33800000,0x9f80) PS2PH("ps2ph denormal in",0x00000001,0x1f80) PS2PH("ps2ph denormal in daz",0x00000001,0x1fc0)
    PS2PH("ps2ph half tiny ftz",0x33000001,0x9f80)
    csr=0x1f80; __asm__ volatile("ldmxcsr %0"::"m"(csr)); (void)f; }
  }

static sigjmp_buf jb; static volatile int sig, code; static volatile long addr, ipoff; static volatile unsigned long start;
static void h(int s, siginfo_t*i, void*u){ ucontext_t*c=u; sig=s; code=i->si_code; addr=(long)i->si_addr; ipoff=c->uc_mcontext.gregs[REG_RIP]-start; siglongjmp(jb,1);}
static char buf[128] __attribute__((aligned(64)));
#define A(name, asmtext) do { sig=0; if(!sigsetjmp(jb,1)) { __asm__ volatile(asmtext::"a"(buf+1),"d"(buf+16):"xmm0","memory"); P(name ": ran\n"); } \
  else P(name ": sig=%d code=%d addr=%ld\n", sig, code, (long)addr); } while(0)
static void aligned(void){
  A("movaps load","movaps (%%rax),%%xmm0"); A("movaps store","movaps %%xmm0,(%%rax)"); A("movdqa load","movdqa (%%rax),%%xmm0"); A("movapd store","movapd %%xmm0,(%%rax)");
  A("movntps","movntps %%xmm0,(%%rax)"); A("movntdq","movntdq %%xmm0,(%%rax)"); A("movntdqa","movntdqa (%%rax),%%xmm0");
  A("vmovaps y","vmovaps (%%rdx),%%ymm0"); A("vmovdqa y ok","vmovdqa 16(%%rdx),%%ymm0"); A("vmovaps x","vmovaps %%xmm0,(%%rax)");
  A("movups","movups (%%rax),%%xmm0"); A("movaps ok","movaps (%%rdx),%%xmm0"); }

#define T(name, asmtext) do { extern char name##_s[]; start=(unsigned long)name##_s; sig=0; \
  if(!sigsetjmp(jb,1)) { __asm__ volatile(#name "_s: " asmtext); P(#name ": ran\n"); } \
  else P(#name ": sig=%d code=%d addr=%s ip+%ld\n", sig, code, addr==0?"0":(addr==(long)start+ipoff?"ip":"other"), (long)ipoff); } while(0)
static void traps(void){
  T(int5,"int $5"); T(int1,"int $1"); T(int3,"int $3"); T(int3b,"int3"); T(int4,"int $4"); T(icebp,".byte 0xf1"); T(int255,"int $255");
  T(cli,"cli"); T(sti,"sti"); T(inb,"inb $0x80,%al"); T(outb,"outb %al,$0x80"); T(inw,"inw %dx,%ax"); T(outl,"outl %eax,%dx"); T(insb,"insb"); T(outsl,"outsl");
  T(rdmsr,"rdmsr"); T(wrmsr,"wrmsr"); T(movcr,"mov %cr0,%rax"); T(movtocr,"mov %rax,%cr3"); T(movdr,"mov %rax,%dr7"); T(movfromdr,"mov %dr0,%rax");
  T(iretq,"iretq"); T(sysretq,"sysretq"); T(sysret,"sysretl"); T(lgdt,"lgdt (%rsp)"); T(lidt,"lidt (%rsp)"); T(ltr,"ltr %ax"); T(lldt,"lldt %ax"); T(invlpg,"invlpg (%rsp)");
  T(swapgs,"swapgs"); T(clts,"clts"); T(rdpmc,"rdpmc"); T(vmcall,"vmcall"); T(vmmcall,"vmmcall"); T(sysenter,"sysenter"); T(hlt,"hlt"); T(wbinvd,"wbinvd"); T(invd,"invd"); T(lmsw,"lmsw %ax"); T(sysexit,"sysexit");
  T(badds,"mov $0x1234,%eax; mov %eax,%ds"); T(nullds,"xor %eax,%eax; mov %eax,%ds; mov %eax,%es"); T(userds,"mov $0x2b,%eax; mov %eax,%ds; xor %eax,%eax; mov %eax,%ds");
  T(badss,"xor %eax,%eax; mov %eax,%ss"); T(ldtds,"mov $0x7,%eax; mov %eax,%es"); T(movcs,".byte 0x8e,0xc8");
  T(ud2,"ud2"); T(clac,"clac"); T(xsetbv,"xor %ecx,%ecx; xsetbv"); T(vmxoff,"vmxoff");
  { long r; __asm__ volatile("int $0x80":"=a"(r):"a"(20)); P("int80 getpid: %s\n", r==getpid()?"pid":"other"); 
    static const char m[]="by int80\n"; long rcx;
    register long r8 __asm__("r8")=0x1122334455667788; register long r11r __asm__("r11")=0x6666;
    r=4; rcx=(long)m; __asm__ volatile("int $0x80":"+a"(r),"+c"(rcx),"+r"(r8),"+r"(r11r):"b"(1L),"d"(sizeof m-1));
    P("int80 write: %ld rcx %s r8 %lx r11 %lx\n", r, rcx==(long)m?"kept":"changed", r8, r11r);
    r=1000; __asm__ volatile("int $0x80":"+a"(r)); P("int80 1000: %ld\n", r);
  }
  { register unsigned long rcx __asm__("rcx")=1; register unsigned long r11 __asm__("r11")=2; unsigned long rax=SYS_getpid; extern char sc_after[]; unsigned long fl;
    __asm__ volatile("pushfq; pop %[fl]; syscall; sc_after:":"+a"(rax),"+r"(rcx),"+r"(r11),[fl]"=&r"(fl)::"memory");
    P("syscall rcx %s r11 %s\n", rcx==(unsigned long)sc_after?"after":"other", r11==fl?"flags":"other"); }
  { unsigned a,d; __asm__ volatile("xgetbv":"=a"(a),"=d"(d):"c"(0)); P("xgetbv %x %x\n", a&3, d); }
  T(xgetbv1,"mov $5,%ecx; xgetbv");
  { unsigned long v=0; __asm__ volatile("smsw %%eax":"+a"(v)); P("smsw %lx\n", v); unsigned short m=0; __asm__ volatile("smsw %0":"=m"(m)); P("smsw m %x\n", m);
    v=~0UL; __asm__ volatile("smsw %%rax":"+a"(v)); P("smsw q %lx\n", v);  v=~0UL; __asm__ volatile("smsw %%ax":"+a"(v)); P("smsw w %lx\n", v); }
  { unsigned long v=0x11111111deadbeef, f; long s=0x2b; __asm__ volatile("lsl %%ecx,%%eax; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); P("lsl 2b %lx zf=%lu\n", v, (f>>6)&1);
    v=0x11111111deadbeef; s=0x33; __asm__ volatile("lsl %%rcx,%%rax; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); P("lsl 33 %lx zf=%lu\n", v, (f>>6)&1);
    v=0x11111111deadbeef; s=0; __asm__ volatile("lsl %%ecx,%%eax; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); P("lsl 0 %lx zf=%lu\n", v, (f>>6)&1);
    v=0x11111111deadbeef; s=0x1234; __asm__ volatile("lsl %%cx,%%ax; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); P("lsl 1234 %lx zf=%lu\n", v, (f>>6)&1);
    v=0x11111111deadbeef; s=0x10; __asm__ volatile("lsl %%ecx,%%eax; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); P("lsl 10 %lx zf=%lu\n", v, (f>>6)&1); }
  { unsigned long v=3; __asm__ volatile(".byte 0xd1,0xf0":"+a"(v)); P("d1 /6: %lx\n", v); unsigned long f; v=0x80;
    __asm__ volatile(".byte 0xf6,0xc8,0x80; pushfq; pop %%rdx":"+a"(v),"=d"(f)); P("f6 /1: %lx zf=%lu\n", v, (f>>6)&1);
    __asm__ volatile(".byte 0xf7,0xc8,0x00,0x01,0x00,0x00; pushfq; pop %%rdx":"+a"(v),"=d"(f)); P("f7 /1: %lx zf=%lu\n", v, (f>>6)&1);
    v=5; __asm__ volatile(".byte 0x48,0xc1,0xf0,0x04":"+a"(v)); P("c1 /6: %lx\n", v);
    __asm__ volatile(".byte 0x0f,0x19,0xc0; .byte 0x0f,0x1a,0x00; .byte 0x0f,0x1b,0x04,0x24; .byte 0x0f,0x1c,0xc0; .byte 0x0f,0x1d,0x40,0x10; .byte 0x0f,0x1e,0xc0; .byte 0x66,0x0f,0x19,0x84,0x00,0,0,0,0":::"memory"); P("hint nops\n"); }
  }

// LAR, VERR and VERW of the selectors that a program can see, and SLDT and STR.
static void tables(void){ u64 v,f; long s;
#define LAR(S,insn) v=0x11111111deadbeefull; s=S; __asm__ volatile(insn "; pushfq; pop %%rdx":"+a"(v),"=d"(f):"c"(s)); ps(insn " ");px(S,4);pc(' ');px(v,16);ps(" zf=");px((f>>6)&1,1);nl();
  LAR(0x2b,"lar %%ecx,%%eax") LAR(0x33,"lar %%ecx,%%eax") LAR(0x23,"lar %%ecx,%%eax") LAR(0x7b,"lar %%ecx,%%eax") LAR(0,"lar %%ecx,%%eax") LAR(0x10,"lar %%ecx,%%eax") LAR(0x2f,"lar %%ecx,%%eax")
  LAR(0x33,"lar %%rcx,%%rax") LAR(0x2b,"lar %%cx,%%ax")
  LAR(0x2b,"verr %%cx") LAR(0x33,"verr %%cx") LAR(0x7b,"verr %%cx") LAR(0,"verr %%cx") LAR(0x10,"verr %%cx")
  LAR(0x2b,"verw %%cx") LAR(0x33,"verw %%cx") LAR(0x7b,"verw %%cx") LAR(0x1234,"verw %%cx")
  v=~0ull; __asm__ volatile("sldt %%eax":"+a"(v)); ps("sldt ");px(v&0xffff,4);nl();
  v=~0ull; __asm__ volatile("str %%ax":"+a"(v)); ps("str ");px(v&0xffff,4);nl(); }

typedef int (*fn)(int);
static void fetch(void){
  static const unsigned char insns[]={0xb8,1,0,0,0,0x01,0xf8,0xc3};
  // Unmapped after the page, not executable after it, and that once both have run.
  for (int way = 0; way < 3; way++) {
    unsigned char *y=mmap(0,8192,PROT_READ|PROT_WRITE|PROT_EXEC,MAP_PRIVATE|MAP_ANONYMOUS,-1,0);
    memcpy(y+4096-3,insns,sizeof insns); memcpy(y+4096+64,insns,sizeof insns);
    if (way == 2) { long s=0; for(int i=0;i<300;i++){ s+=((fn)(y+4096-3))(1); s+=((fn)(y+4096+64))(1);} P("hot %ld\n",s); }
    if (way == 0) munmap(y+4096,4096); else mprotect(y+4096,4096,PROT_READ|PROT_WRITE);
    if(!sigsetjmp(jb,1)){ P("second page ran %d\n",((fn)(y+4096+64))(1)); } else P("second sig=%d code=%d off=%ld\n",sig,code,(long)((char*)addr-(char*)y));
    if(!sigsetjmp(jb,1)){ P("straddle ran %d\n",((fn)(y+4096-3))(1)); } else P("straddle sig=%d code=%d off=%ld\n",sig,code,(long)((char*)addr-(char*)y));
  } }

int main(void){
  struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_sigaction=h; sa.sa_flags=SA_SIGINFO;
  for(int s=1;s<32;s++) if(s!=SIGKILL&&s!=SIGSTOP) sigaction(s,&sa,0);
  state(); x87(); ftz(); prefixes(); frames(); aligned(); traps(); tables(); fetch();
  flush();
  return 0; }
