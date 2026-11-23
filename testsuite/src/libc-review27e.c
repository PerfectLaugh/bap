// More of what a processor of x86-64 and Linux do that the machine didn't, each as an AMD of AVX2 under Linux says it (testsuite/data):
//   exceptions of floating point that aren't masked are SIGFPE: of SSE at the instruction, which leaves its destination, with the
//     code of what was raised; of x87 at the next instruction of x87 that waits, FWAIT too, and not after FNCLEX.
//   the legacy instructions of SSE with an operand of 128 bits in memory fault of an address that isn't aligned, but the moves that
//     say unaligned, the string comparisons, and what reads less than 128 bits; those of VEX don't.
//   the trap flag: each instruction that starts with it is followed by SIGTRAP of TRAP_TRACE, POPF that clears it too; the frame
//     of the handler has the flag, the handler runs without it, and one that clears it in its frame ends the steps.
//   CPUID says OSXSAVE and AVX, XGETBV their states; XSAVE, XSAVEC and XRSTOR keep and bring back what they are asked of them;
//     RDTSCP says the processor; CLZERO clears its line.
//   int $0x80 makes the calls of i386 with their layouts: stat64, iovec, timeval and timespec of 32 bits, _llseek.
//   BSWAP of 16 bits clears its register; a far return to the code segment it is in returns.
// Built with -mavx2 -maes -mpclmul -mxsave -mxsavec -mclzero. It is at addresses below 4 GiB, as the calls of i386 need.
#define _GNU_SOURCE
#include <fcntl.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>
#include <unistd.h>

typedef unsigned long long u64; typedef unsigned int u32; typedef unsigned short u16; typedef unsigned char u8;
static sigjmp_buf jb; static volatile int sig, code; static volatile long addr, ipoff; static volatile unsigned long start;
static void h(int s, siginfo_t*i, void*u){ ucontext_t*c=u; sig=s; code=i->si_code; addr=(long)i->si_addr; ipoff=c->uc_mcontext.gregs[REG_RIP]-start; siglongjmp(jb,1);}
double one=1.0, zero=0.0, three=3.0, big=1e308, tiny=1e-308, res;
unsigned csr; unsigned short cw, sw;
#define T(name, asmtext) do { extern char name##_s[]; start=(unsigned long)name##_s; sig=0; res=-7; \
  if(!sigsetjmp(jb,1)) { __asm__ volatile(asmtext); printf(#name ": ran\n"); } \
  else printf(#name ": sig=%d code=%d addr=%s ip+%ld res=%g\n", sig, code, addr==(long)start+ipoff?"ip":"other", (long)ipoff, res); \
  __asm__ volatile("fninit; movl $0x1f80,csr(%rip); ldmxcsr csr(%rip)"); } while(0)
static void exceptions(void){
  T(divz, "movl $0x1d80,csr(%rip); ldmxcsr csr(%rip); movsd one(%rip),%xmm0; movsd res(%rip),%xmm1; divz_s: divsd zero(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(inv, "movl $0x1f00,csr(%rip); ldmxcsr csr(%rip); movsd zero(%rip),%xmm0; inv_s: divsd zero(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(inex, "movl $0x0f80,csr(%rip); ldmxcsr csr(%rip); movsd one(%rip),%xmm0; inex_s: divsd three(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(ovf, "movl $0x1b80,csr(%rip); ldmxcsr csr(%rip); movsd big(%rip),%xmm0; ovf_s: mulsd big(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(unf, "movl $0x1780,csr(%rip); ldmxcsr csr(%rip); movsd tiny(%rip),%xmm0; unf_s: mulsd tiny(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(masked, "movsd one(%rip),%xmm0; masked_s: divsd zero(%rip),%xmm0; movsd %xmm0,res(%rip)");
  T(cvt, "movl $0x1f00,csr(%rip); ldmxcsr csr(%rip); movsd big(%rip),%xmm0; cvt_s: cvttsd2si %xmm0,%eax");
  T(x87divz, "movw $0x37b,cw(%rip); fldcw cw(%rip); fldl one(%rip); fdivl zero(%rip); fnstsw sw(%rip); x87divz_s: fstpl res(%rip)");
  printf("sw %x\n", sw & 0x80bf);
  T(x87wait, "movw $0x37e,cw(%rip); fldcw cw(%rip); fldz; fdivl zero(%rip); fnop; x87wait_s: fwait");
  T(x87inex, "movw $0x35f,cw(%rip); fldcw cw(%rip); fldl one(%rip); fdivl three(%rip); x87inex_s: fstpl res(%rip)");
  T(x87under, "movw $0x37e,cw(%rip); fldcw cw(%rip); faddp; x87under_s: fnop; fwait");
  T(x87clex, "movw $0x37b,cw(%rip); fldcw cw(%rip); fldl one(%rip); fdivl zero(%rip); fnclex; x87clex_s: fstpl res(%rip)");
}

static char buf[256] __attribute__((aligned(64)));
#define A(name, asmtext) do { sig=0; if(!sigsetjmp(jb,1)) { __asm__ volatile(asmtext::"a"(buf+1),"d"(buf+16):"xmm0","xmm1","memory"); printf(name ": ran\n"); } \
  else printf(name ": sig=%d code=%d\n", sig, code); } while(0)
static void aligned(void){
  A("paddb","paddb (%%rax),%%xmm0"); A("addps","addps (%%rax),%%xmm0"); A("andps","andps (%%rax),%%xmm0"); A("pshufb","pshufb (%%rax),%%xmm0"); A("cmpps","cmpps $1,(%%rax),%%xmm0");
  A("sqrtpd","sqrtpd (%%rax),%%xmm0"); A("aesenc","aesenc (%%rax),%%xmm0"); A("pclmul","pclmulqdq $0,(%%rax),%%xmm0"); A("shufps","shufps $1,(%%rax),%%xmm0"); A("packsswb","packsswb (%%rax),%%xmm0");
  A("pshufd","pshufd $1,(%%rax),%%xmm0"); A("cvtdq2ps","cvtdq2ps (%%rax),%%xmm0"); A("ptest","ptest (%%rax),%%xmm0"); A("pblendw","pblendw $1,(%%rax),%%xmm0"); A("rcpps","rcpps (%%rax),%%xmm0");
  A("pcmpistri","pcmpistri $0,(%%rax),%%xmm0"); A("movdqu","movdqu (%%rax),%%xmm0"); A("lddqu","lddqu (%%rax),%%xmm0"); A("addss","addss (%%rax),%%xmm0"); A("movddup","movddup (%%rax),%%xmm0"); A("pmovzxbw","pmovzxbw (%%rax),%%xmm0"); A("cvtps2pd","cvtps2pd (%%rax),%%xmm0");
  A("vpaddb","vpaddb (%%rax),%%xmm0,%%xmm0"); A("vaddps","vaddps (%%rax),%%ymm0,%%ymm0"); A("paddb ok","paddb (%%rdx),%%xmm0"); A("addps ok","addps (%%rdx),%%xmm0");
}

static volatile int traps, codes, tfin, tfframe, until; static volatile long offs[16]; extern char tf_s[];
static void stepped(int s, siginfo_t*i, void*u){ ucontext_t*c=u; unsigned long f; __asm__ volatile("pushfq; pop %0":"=r"(f));
  if(traps<16) offs[traps]=(long)i->si_addr-(long)tf_s; traps++; codes|=1<<i->si_code; tfin|=(f>>8)&1; tfframe+=(c->uc_mcontext.gregs[REG_EFL]>>8)&1;
  if(traps==until) c->uc_mcontext.gregs[REG_EFL]&=~0x100L; }
static void steps(void){ struct sigaction sa, old; memset(&sa,0,sizeof sa); sa.sa_sigaction=stepped; sa.sa_flags=SA_SIGINFO; sigaction(SIGTRAP,&sa,&old);
  long x=0;
  __asm__ volatile("pushfq; orl $0x100,(%%rsp); popfq; tf_s: nop; inc %%rax; inc %%rax; pushfq; andl $~0x100,(%%rsp); popfq; inc %%rax; nop":"+a"(x));
  printf("steps: x=%ld traps=%d codes=%x tf in the handler %d in its frames %d\n", x, traps, codes, tfin, tfframe);
  for(int i=0;i<traps&&i<16;i++) printf(" at +%ld\n", offs[i]);
  traps=0; until=3; x=0;
  __asm__ volatile("pushfq; orl $0x100,(%%rsp); popfq; nop; inc %%rax; inc %%rax; inc %%rax; inc %%rax; inc %%rax; nop":"+a"(x));
  printf("steps that the handler ends: x=%ld traps=%d\n", x, traps);
  sigaction(SIGTRAP,&old,0); }

static char obuf[1<<14]; static int opos;
static void pc(char c){obuf[opos++]=c;}
static void ps(const char*s){while(*s)pc(*s++);}
static void px(u64 v,int n){for(int i=n-1;i>=0;i--)pc("0123456789abcdef"[(v>>(4*i))&15]);}
static void nl(void){pc('\n');}
static void cpuid(u32 l,u32 s,u32*r){__asm__ volatile("cpuid":"=a"(r[0]),"=b"(r[1]),"=c"(r[2]),"=d"(r[3]):"a"(l),"c"(s));}
static u8 area[4096] __attribute__((aligned(64))); static u8 area2[4096] __attribute__((aligned(64)));
static void processor(void){ u32 r[4]; u64 a,d,c;
  cpuid(1,0,r); ps("osxsave ");px((r[2]>>26)&3,1);ps(" avx ");px((r[2]>>28)&1,1);nl();
  __asm__ volatile("xgetbv":"=a"(a),"=d"(d):"c"(0)); ps("xcr0 has x87 sse avx ");px(a&7,1);pc(' ');px(d,1);nl();
  cpuid(0xd,0,r); ps("xsave area fits ");px(r[1]<=sizeof area && r[1]>=576+256,1);ps(" avx at ");cpuid(0xd,2,r);px(r[1],4);pc(' ');px(r[0],4);nl();
  cpuid(0xd,1,r); u32 has_c=(r[0]>>1)&1; ps("xsavec ");px(has_c,1);nl();
  // xsave / xrstor of YMM
  u64 v[4]={0x1111111111111111ull,0x2222222222222222ull,0x3333333333333333ull,0x4444444444444444ull}, o[4];
  for(int i=0;i<4096;i++)area[i]=0;
  __asm__ volatile("vmovdqu %[v],%%ymm5; mov $7,%%eax; xor %%edx,%%edx; xsave %[m]; vpxor %%ymm5,%%ymm5,%%ymm5; mov $7,%%eax; xor %%edx,%%edx; xrstor %[m]; vmovdqu %%ymm5,%[o]":[o]"=m"(o),[m]"+m"(area):[v]"m"(v):"rax","rdx","xmm5");
  ps("xsave xrstor ");px(o[0],16);px(o[3],16);ps(" bv ");px(area[512]&6,1);ps(" in area ");px(*(u64*)(area+160+5*16),16);px(*(u64*)(area+576+5*16+8),16);nl();
  // only what is asked for is restored: SSE alone leaves the upper half
  __asm__ volatile("vmovdqu %[v],%%ymm5; mov $7,%%eax; xor %%edx,%%edx; xsave %[m]; vpxor %%ymm5,%%ymm5,%%ymm5; mov $2,%%eax; xor %%edx,%%edx; xrstor %[m]; vmovdqu %%ymm5,%[o]":[o]"=m"(o),[m]"+m"(area):[v]"m"(v):"rax","rdx","xmm5");
  ps("xrstor sse ");px(o[0],16);px(o[3],16);nl();
  // a component that the header says isn't there is as it starts
  *(u64*)(area+512)&=~4ull;
  __asm__ volatile("vmovdqu %[v],%%ymm5; mov $7,%%eax; xor %%edx,%%edx; xrstor %[m]; vmovdqu %%ymm5,%[o]":[o]"=m"(o):[m]"m"(area),[v]"m"(v):"rax","rdx","xmm5");
  ps("xrstor init avx ");px(o[0],16);px(o[3],16);nl();
  if(has_c){ for(int i=0;i<4096;i++)area2[i]=0;
    __asm__ volatile("vmovdqu %[v],%%ymm5; mov $6,%%eax; xor %%edx,%%edx; xsavec %[m]; vpxor %%ymm5,%%ymm5,%%ymm5; mov $7,%%eax; xor %%edx,%%edx; xrstor %[m]; vmovdqu %%ymm5,%[o]":[o]"=m"(o),[m]"+m"(area2):[v]"m"(v):"rax","rdx","xmm5");
    ps("xsavec xrstor ");px(o[0],16);px(o[3],16);ps(" compact ");px(area2[527]>>7,1);ps(" comp ");px(area2[520]&7,1);nl(); }
  // mxcsr and x87 through xsave
  { u32 csr=0x1fa0; u16 cw=0x27f; u32 csr2; u16 cw2;
    __asm__ volatile("ldmxcsr %[c]; fldcw %[w]; mov $3,%%eax; xor %%edx,%%edx; xsave %[m]; fninit; movl $0x1f80,%[c2]; ldmxcsr %[c2]; mov $3,%%eax; xor %%edx,%%edx; xrstor %[m]; stmxcsr %[c2]; fnstcw %[w2]; fninit; movl $0x1f80,%[c]; ldmxcsr %[c]":[c2]"=m"(csr2),[w2]"=m"(cw2),[m]"+m"(area),[c]"+m"(csr):[w]"m"(cw):"rax","rdx");
    ps("xsave words ");px(csr2,4);pc(' ');px(cw2,4);nl(); }
  __asm__ volatile("rdtscp":"=a"(a),"=d"(d),"=c"(c)); ps("rdtscp aux small ");px(c<4096,1);nl();
  { u8 line[192]; for(int i=0;i<192;i++)line[i]=0xee; u8*p=(u8*)(((u64)line+64)&~63ull)+17; __asm__ volatile("clzero"::"a"(p):"memory"); p-=17; ps("clzero ");px(p[-1],2);px(p[0],2);px(p[63],2);px(p[64],2);nl(); }

  a=0x1122334455667788ull; __asm__ volatile(".byte 0x66,0x0f,0xc8":"+a"(a)); ps("bswap16 ");px(a,16);nl();
  { u64 b; __asm__ volatile("mov %%cs,%%eax; lea 1f(%%rip),%%rcx; push %%rax; push %%rcx; lretq; 1: mov $7,%%ebx":"=b"(b)::"rax","rcx"); ps("lretq ");px(b,2);nl(); }
  fwrite(obuf,1,opos,stdout); }

static long c80(long n,long a,long b,long c,long d,long e){ long r; __asm__ volatile("int $0x80":"=a"(r):"a"(n),"b"(a),"c"(b),"d"(c),"S"(d),"D"(e):"memory"); return r; }
static char path[]="review27-int80.tmp", text[]="hello int80\n", cbuf[64], names[512];
static unsigned st[32]; static struct { unsigned base, len; } iov[2]; static unsigned tv[2], ts[2]; static char un[6][65]; static int fds[2]; static long long off;
static void compat(void){
  long fd=c80(5,(long)path,O_CREAT|O_RDWR|O_TRUNC,0600,0,0); printf("open %s\n", fd>=0?"ok":"failed");
  printf("write %ld\n", c80(4,fd,(long)text,12,0,0));
  iov[0].base=(unsigned)(long)text; iov[0].len=5; iov[1].base=(unsigned)(long)(text+5); iov[1].len=7;
  printf("writev %ld\n", c80(146,fd,(long)iov,2,0,0));
  printf("fstat64 %ld size %u mode %o\n", c80(197,fd,(long)st,0,0,0), st[11], st[4]&0777777);
  memset(st,0,sizeof st); printf("stat64 %ld size %u\n", c80(195,(long)path,(long)st,0,0,0), st[11]);
  printf("llseek %ld at %lld\n", c80(140,fd,0,6,(long)&off,0), off);
  iov[0].base=(unsigned)(long)cbuf; iov[0].len=3; iov[1].base=(unsigned)(long)(cbuf+10); iov[1].len=3;
  printf("readv %ld %.3s %.3s\n", c80(145,fd,(long)iov,2,0,0), cbuf, cbuf+10);
  printf("lseek %ld read %ld %.5s\n", c80(19,fd,0,0,0,0), c80(3,fd,(long)cbuf,5,0,0), cbuf);
  printf("close %ld unlink %ld\n", c80(6,fd,0,0,0,0), c80(10,(long)path,0,0,0,0));
  printf("gettimeofday %ld %s\n", c80(78,(long)tv,0,0,0,0), tv[0]>1000000000u&&tv[1]<1000000u?"plausible":"odd");
  printf("clock_gettime %ld %s\n", c80(265,0,(long)ts,0,0,0), ts[0]>1000000000u&&ts[1]<1000000000u?"plausible":"odd");
  printf("uname %ld %s\n", c80(122,(long)un,0,0,0,0), un[0]);
  printf("pipe %ld %s\n", c80(42,(long)fds,0,0,0,0), fds[1]>fds[0]&&fds[0]>2?"two":"odd");
  printf("getcwd %s\n", c80(183,(long)names,512,0,0,0)>0&&names[0]=='/'?"absolute":"odd");
  printf("getuid32 %s getpid %s\n", c80(199,0,0,0,0,0)==getuid()?"same":"other", c80(20,0,0,0,0,0)==getpid()?"same":"other");
  printf("fstat64 of a bad descriptor %ld, no call %ld\n", c80(197,99,(long)st,0,0,0), c80(1000,0,0,0,0,0));
}

int main(void){
  struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_sigaction=h; sa.sa_flags=SA_SIGINFO;
  for(int s=1;s<32;s++) if(s!=SIGKILL&&s!=SIGSTOP) sigaction(s,&sa,0);
  setvbuf(stdout,0,_IONBF,0);
  exceptions(); aligned(); steps(); processor(); compat();
  return 0; }
