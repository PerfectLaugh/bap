// The instructions of floating point of AVX-512 that `Bap.Float` didn't serve, and the masks and the conversions of unsigned integers
// with them: VCVT(T)SD2USI, VCVTUSI2SD, VRNDSCALE, VGETEXP, VGETMANT, VSCALEF, VRANGE, VREDUCE, VRCP14, VRSQRT14, VFPCLASS and
// VFIXUPIMM, each with the flags of MXCSR that it raises. No processor here has AVX-512: what each line should say
// (testsuite/data) is worked out by hand from the manual, volume 2 (the pseudocode of each, and tables 5-21 to 5-23 and 5-31), and
// of VGETMANT of a negative infinity without the bit of its immediate that makes a NaN of it, -1, as Bochs has it.
// Built with -mavx512f -mavx512dq -mavx512vl -mavx512fp16 -mavx10.2.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>
typedef unsigned long long u64; typedef unsigned int u32; typedef unsigned short u16; typedef unsigned char u8;
static char obuf[1<<16]; static int opos;
static void flush(void){if(opos)write(1,obuf,opos);opos=0;}
static void pc(char c){obuf[opos++]=c;}
static void ps(const char*s){while(*s)pc(*s++);}
static void px(u64 v,int n){for(int i=n-1;i>=0;i--)pc("0123456789abcdef"[(v>>(4*i))&15]);}
static void nl(void){pc('\n');}
static sigjmp_buf jb; static volatile int caughtSignal, caughtCode;
static void caught(int s, siginfo_t*i, void*u){ caughtSignal=s; caughtCode=i->si_code; siglongjmp(jb,1); }
typedef union{double d;u64 u;} D;
static u32 csr0=0x1f80;
#define RESET __asm__ volatile("ldmxcsr %0"::"m"(csr0))
static u32 flags(void){u32 c;__asm__ volatile("stmxcsr %0":"=m"(c));return c&0x3f;}
static void out(const char*n,u64 v){ps(n);pc(' ');px(v,16);ps(" f=");px(flags(),2);nl();}
#define SD2(name,insn,A,B) do{D a,b,r;a.u=A;b.u=B;RESET;__asm__ volatile(insn:"=x"(r.d):"x"(a.d),"x"(b.d));out(name,r.u);}while(0)
int main(void){ u64 a; D x,y,r;
  __asm__ volatile("kxnorw %%k0,%%k0,%%k1; kmovw %%k1,%%eax":"=a"(a)); ps("kxnorw ");px(a,16);nl();
  __asm__ volatile("kxorq %%k0,%%k0,%%k0; kmovq %%k0,%%rax":"=a"(a)); ps("kxorq ");px(a,16);nl();
#define TOU(name,insn,V) do{x.u=V;RESET;__asm__ volatile(insn:"=a"(a):"x"(x.d));out(name,a);}while(0)
  TOU("cvttsd2usi 3e9","vcvttsd2usi %1,%%eax",0x41e65a0bc0000000ull);
  TOU("cvttsd2usi -1","vcvttsd2usi %1,%%eax",0xbff0000000000000ull);
  TOU("cvttsd2usi 1e30","vcvttsd2usi %1,%%eax",0x46293e5939a08ceaull);
  TOU("cvttsd2usi 0.7","vcvttsd2usi %1,%%eax",0x3fe6666666666666ull);
  TOU("cvtsd2usi -0.3","vcvtsd2usi %1,%%eax",0xbfd3333333333333ull);
  TOU("cvtsd2usi -0.7","vcvtsd2usi %1,%%eax",0xbfe6666666666666ull);
  TOU("cvttsd2usi64 2^63","vcvttsd2usi %1,%%rax",0x43e0000000000000ull);
  TOU("cvttsd2usi64 nan","vcvttsd2usi %1,%%rax",0x7ff8000000000000ull);
  TOU("cvttsd2si64 2^63","vcvttsd2si %1,%%rax",0x43e0000000000000ull);
#define FROMU(name,insn,V) do{a=V;RESET;__asm__ volatile("vxorpd %%xmm0,%%xmm0,%%xmm0;" insn:"=Yz"(r.d):"a"(a));out(name,r.u);}while(0)
  FROMU("cvtusi2sd max","vcvtusi2sd %%rax,%%xmm0,%%xmm0",0xffffffffffffffffull);
  FROMU("cvtusi2sd 2^31","vcvtusi2sd %%eax,%%xmm0,%%xmm0",0x80000000ull);
  FROMU("cvtusi2sd 2^53+1","vcvtusi2sd %%rax,%%xmm0,%%xmm0",0x20000000000001ull);
  SD2("rndscale 2.3 M1","vrndscalesd $0x10,%2,%1,%0",0,0x4002666666666666ull);
  SD2("rndscale 2.3 M1 spe","vrndscalesd $0x18,%2,%1,%0",0,0x4002666666666666ull);
  SD2("rndscale -2.5 M0 up","vrndscalesd $0x02,%2,%1,%0",0,0xc004000000000000ull);
  SD2("rndscale snan","vrndscalesd $0x00,%2,%1,%0",0,0x7ff0000000000001ull);
  SD2("getexp 10","vgetexpsd %2,%1,%0",0,0x4024000000000000ull);
  SD2("getexp 0.1","vgetexpsd %2,%1,%0",0,0x3fb999999999999aull);
  SD2("getexp 0","vgetexpsd %2,%1,%0",0,0);
  SD2("getexp -inf","vgetexpsd %2,%1,%0",0,0xfff0000000000000ull);
  SD2("getexp denormal","vgetexpsd %2,%1,%0",0,1);
  SD2("getmant 10 i0","vgetmantsd $0x00,%2,%1,%0",0,0x4024000000000000ull);
  SD2("getmant 10 i1","vgetmantsd $0x01,%2,%1,%0",0,0x4024000000000000ull);
  SD2("getmant 10 i2","vgetmantsd $0x02,%2,%1,%0",0,0x4024000000000000ull);
  SD2("getmant 14 i3","vgetmantsd $0x03,%2,%1,%0",0,0x402c000000000000ull);
  SD2("getmant -10 nan","vgetmantsd $0x08,%2,%1,%0",0,0xc024000000000000ull);
  SD2("getmant -10 abs","vgetmantsd $0x04,%2,%1,%0",0,0xc024000000000000ull);
  SD2("getmant -inf","vgetmantsd $0x00,%2,%1,%0",0,0xfff0000000000000ull);
  SD2("getmant denormal","vgetmantsd $0x00,%2,%1,%0",0,3);
  SD2("scalef 3 2.7","vscalefsd %2,%1,%0",0x4008000000000000ull,0x400599999999999aull);
  SD2("scalef 1.5 -0.5","vscalefsd %2,%1,%0",0x3ff8000000000000ull,0xbfe0000000000000ull);
  SD2("scalef 1 2000","vscalefsd %2,%1,%0",0x3ff0000000000000ull,0x409f400000000000ull);
  SD2("scalef 0 inf","vscalefsd %2,%1,%0",0,0x7ff0000000000000ull);
  SD2("scalef 3 -1075","vscalefsd %2,%1,%0",0x4008000000000000ull,0xc090cc0000000000ull);
  SD2("scalef 1 nan","vscalefsd %2,%1,%0",0x3ff0000000000000ull,0x7ff8000000000001ull);
  SD2("range min 3 -5","vrangesd $0x00,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("range min sign","vrangesd $0x04,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("range max","vrangesd $0x05,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("range absmax abs","vrangesd $0x0b,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("range absmin","vrangesd $0x06,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("range min +0 -0","vrangesd $0x04,%2,%1,%0",0,0x8000000000000000ull);
  SD2("range max -0 +0","vrangesd $0x05,%2,%1,%0",0x8000000000000000ull,0);
  SD2("range absmin 2 -2","vrangesd $0x06,%2,%1,%0",0x4000000000000000ull,0xc000000000000000ull);
  SD2("range qnan 3","vrangesd $0x04,%2,%1,%0",0x7ff8000000000000ull,0x4008000000000000ull);
  SD2("range 3 snan","vrangesd $0x04,%2,%1,%0",0x4008000000000000ull,0x7ff0000000000005ull);
  SD2("reduce 2.75 M0","vreducesd $0x00,%2,%1,%0",0,0x4006000000000000ull);
  SD2("reduce 2.3 M1","vreducesd $0x10,%2,%1,%0",0,0x4002666666666666ull);
  SD2("reduce inf","vreducesd $0x00,%2,%1,%0",0,0x7ff0000000000000ull);
  SD2("reduce 3 dn","vreducesd $0x01,%2,%1,%0",0,0x4008000000000000ull);
  SD2("rcp14 4","vrcp14sd %2,%1,%0",0,0x4010000000000000ull);
  SD2("rsqrt14 4","vrsqrt14sd %2,%1,%0",0,0x4010000000000000ull);
  SD2("rcp14 0","vrcp14sd %2,%1,%0",0,0x8000000000000000ull);
#define CLS(name,imm,V) do{x.u=V;RESET;__asm__ volatile("vfpclasssd $" #imm ",%1,%%k1; kmovw %%k1,%%eax":"=a"(a):"x"(x.d));out(name,a);}while(0)
  CLS("fpclass inf",0x18,0x7ff0000000000000ull); CLS("fpclass neg",0x40,0xc008000000000000ull); CLS("fpclass pos",0x40,0x4008000000000000ull);
  CLS("fpclass denormal",0x20,5); CLS("fpclass snan",0x80,0x7ff0000000000001ull); CLS("fpclass qnan as snan",0x80,0x7ff8000000000000ull); CLS("fpclass -0",0x04,0x8000000000000000ull);
#define FIX(name,imm,OLD,SRC,TBL) do{D o,s2;o.u=OLD;s2.u=SRC;u64 t=TBL;RESET;__asm__ volatile("vmovq %%rax,%%xmm3; vfixupimmsd $" #imm ",%%xmm3,%2,%0":"+x"(o.d):"a"(t),"x"(s2.d):"xmm3");out(name,o.u);}while(0)
  FIX("fixup zero inf",0x01,0x4000000000000000ull,0,0xa0000500ull);
  FIX("fixup pos one",0x00,0x4000000000000000ull,0x401e000000000000ull,0xa0000500ull);
  FIX("fixup neg src",0x40,0x4000000000000000ull,0xc01e000000000000ull,0xa1000500ull);
  FIX("fixup qnan keep",0x00,0x4000000000000000ull,0x7ff8000000000000ull,0xa1000500ull);
  FIX("fixup one pi/2",0x00,0x4000000000000000ull,0x3ff0000000000000ull,0xa100d500ull);
  FIX("fixup -inf max",0x20,0x4000000000000000ull,0xfff0000000000000ull,0xa10ed500ull);
  { u32 v[16]={0xffffffff,1,0x80000000,3}; double d[8]; RESET;
    __asm__ volatile("vmovdqu %1,%%ymm1; vcvtudq2pd %%ymm1,%%zmm0; vmovupd %%zmm0,%0":"=m"(d):"m"(v):"xmm0","xmm1"); for(int i=0;i<3;i++){ps("udq2pd ");px(*(u64*)&d[i],16);nl();}
    double s[8]={3e9,-1.0,0.5,1e30,4e9,2.5,-0.2,7.0}; u32 o[8]; RESET;
    __asm__ volatile("vmovupd %1,%%zmm1; mov $0x7f,%%eax; kmovw %%eax,%%k2; vcvttpd2udq %%zmm1,%%ymm0%{%%k2%}%{z%}; vmovdqu %%ymm0,%0":"=m"(o):"m"(s):"xmm0","xmm1","rax"); ps("tpd2udq");for(int i=0;i<8;i++){pc(' ');px(o[i],8);} ps(" f=");px(flags(),2);nl(); }
    // AVX512-FP16 and AVX10.2: the complex product of halves, (1 + 2i)(3 + 4i) = -5 + 10i, with what is above it of the first
  // operand; the minimum and maximum of IEEE 754-2019; and the conversions that saturate.
  { u32 p[4]={0x40003c00,0x11112222,0x33334444,0x55556666}, q[4]={0x44004200,0,0,0}, o[4]; RESET;
    __asm__ volatile("vmovdqu %1,%%xmm1; vmovdqu %2,%%xmm2; vfmulcsh %%xmm2,%%xmm1,%%xmm0; vmovdqu %%xmm0,%0":"=m"(o):"m"(p),"m"(q):"xmm0","xmm1","xmm2");
    ps("fmulcsh ");px(o[0],8);pc(' ');px(o[1],8);ps(" f=");px(flags(),2);nl(); }
  SD2("minmax min 3 -5","vminmaxsd $0x04,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("minmax max 3 -5","vminmaxsd $0x05,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  SD2("minmax min -0 +0","vminmaxsd $0x04,%2,%1,%0",0,0x8000000000000000ull);
  SD2("minmax min qnan 3","vminmaxsd $0x04,%2,%1,%0",0x7ff8000000000000ull,0x4008000000000000ull);
  SD2("minmax minnum qnan 3","vminmaxsd $0x14,%2,%1,%0",0x7ff8000000000000ull,0x4008000000000000ull);
  SD2("minmax minnum 3 snan","vminmaxsd $0x14,%2,%1,%0",0x4008000000000000ull,0x7ff0000000000001ull);
  SD2("minmax maxmag 3 -5 abs","vminmaxsd $0x0b,%2,%1,%0",0x4008000000000000ull,0xc014000000000000ull);
  TOU("cvttsd2sis 1e30","vcvttsd2sis %1,%%eax",0x46293e5939a08ceaull);
  TOU("cvttsd2sis -1e30","vcvttsd2sis %1,%%eax",0xc6293e5939a08ceaull);
  TOU("cvttsd2sis nan","vcvttsd2sis %1,%%eax",0x7ff8000000000000ull);
  TOU("cvttsd2usis -1","vcvttsd2usis %1,%%eax",0xbff0000000000000ull);
  TOU("cvttsd2usis 5e9","vcvttsd2usis %1,%%eax",0x41f2a05f20000000ull);
  TOU("cvttsd2sis 2.5","vcvttsd2sis %1,%%eax",0x4004000000000000ull);
  // The aligned moves of EVEX fault of an address that isn't a multiple of the length of the vector: SIGSEGV of the kernel.
  { static char room[256] __attribute__((aligned(64))); struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_sigaction=caught; sa.sa_flags=SA_SIGINFO; sigaction(SIGSEGV,&sa,0);
#define AL(name, insn) do { if(!sigsetjmp(jb,1)) { __asm__ volatile(insn::"a"(room):"xmm0","memory"); ps(name ": ran"); } else { ps(name ": sig "); px(caughtSignal,2); ps(" code "); px(caughtCode,2); } nl(); } while(0)
    AL("vmovaps zmm +16","vmovaps 16(%%rax),%%zmm0"); AL("vmovaps zmm +64","vmovaps 64(%%rax),%%zmm0"); AL("vmovdqa64 ymm store +16","vmovdqa64 %%ymm0,16(%%rax)");
    AL("vmovdqa32 ymm +32","vmovdqa32 32(%%rax),%%ymm16"); AL("vmovapd xmm +8","vmovapd 8(%%rax),%%xmm16"); AL("vmovups zmm +1","vmovups 1(%%rax),%%zmm0"); AL("vmovntdq zmm +32","vmovntdq %%zmm0,32(%%rax)"); }
  flush();
  return 0;}
