// What only the mode of 32 bits has, as a kernel of 64 bits on an AMD has it of a process of 32 (testsuite/data): the adjustments
// of decimal arithmetic, AAA, AAS, DAA, DAS, AAM and AAD with the flags that the manual defines of each, and SALC; AAM of 0 divides
// by it, SIGFPE; PUSHA and POPA of 16 bits; BOUND of an index outside its bounds is SIGSEGV of the kernel; ARPL; the selectors
// that a process starts with; and a far return to the code segment it is in.
#define _GNU_SOURCE
#include <stdio.h>
#include <signal.h>
#include <setjmp.h>
#include <string.h>
unsigned saved_esp, saved_ebp;
static sigjmp_buf jb; static volatile int sig, code;
static void h(int s, siginfo_t*i, void*u){ sig=s; code=i->si_code; siglongjmp(jb,1);}
static unsigned bcd(int op, unsigned ax, unsigned fl){ unsigned f; 
  switch(op){
  case 0: __asm__ volatile("push %%ecx; popf; aaa; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 1: __asm__ volatile("push %%ecx; popf; aas; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 2: __asm__ volatile("push %%ecx; popf; daa; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 3: __asm__ volatile("push %%ecx; popf; das; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 4: __asm__ volatile("push %%ecx; popf; aam; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 5: __asm__ volatile("push %%ecx; popf; aad; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 6: __asm__ volatile("push %%ecx; popf; aam $7; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 7: __asm__ volatile("push %%ecx; popf; aad $7; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  case 8: __asm__ volatile("push %%ecx; popf; .byte 0xd6; pushf; pop %%ecx":"+a"(ax),"+c"(fl)); break;
  }
  f=fl; return (ax&0xffff)|((f&0x11)<<16)|((f&0xc4)<<24); }
int main(void){ struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_sigaction=h; sa.sa_flags=SA_SIGINFO; sigaction(SIGSEGV,&sa,0); sigaction(SIGFPE,&sa,0); sigaction(SIGILL,&sa,0);
  setvbuf(stdout,0,_IONBF,0);
  static const unsigned vals[]={0x0000,0x0009,0x000a,0x010f,0x0099,0x009a,0x00ff,0x1234,0xff05,0x0260,0x0066,0x809f};
  static const unsigned fls[]={0x202,0x203,0x212,0x213};
  // the flags that the manual defines of each: AF and CF of aaa/aas; all but OF of daa/das; SF ZF PF of aam/aad
  static const unsigned mask[]={0x00110000,0x00110000,0xc4110000,0xc4110000,0xc4000000,0xc4000000,0xc4000000,0xc4000000,0};
  for(int op=0;op<9;op++){ printf("op %d:",op); for(unsigned i=0;i<12;i++) for(unsigned j=0;j<4;j++) printf(" %x", bcd(op,vals[i],fls[j])&(mask[op]|0xffff)); printf("\n"); }
  sig=0; if(!sigsetjmp(jb,1)){ __asm__ volatile("aam $0":::"eax"); printf("aam 0 ran\n"); } else printf("aam 0: sig=%d code=%d\n", sig, code);
  { unsigned st[16]; for(int i=0;i<16;i++)st[i]=0x11110000u+i; unsigned esp;
    __asm__ volatile("mov %%esp,%%esi; lea 48(%[st]),%%esp; mov $0x12345678,%%eax; .byte 0x66,0x60; mov %%esp,%%ecx; mov %%esi,%%esp":"=c"(esp):[st]"b"(st):"esi","eax","memory");
    printf("pushaw esp+%d ax %04x sp %d\n", (int)(esp-(unsigned)st), st[11]>>16, (st[9]>>16)==(((unsigned)st+48)&0xffff));
    for(int i=0;i<16;i++)st[i]=0x11110000u+i;
    unsigned a,c,d;
    __asm__ volatile("mov %%esp,saved_esp; mov %%ebp,saved_ebp; mov %%ebx,%%esp; add $32,%%esp; mov $-1,%%eax; mov $-1,%%ecx; mov $-1,%%edx; .byte 0x66,0x61; mov saved_esp,%%esp; mov saved_ebp,%%ebp":"=a"(a),"=c"(c),"=d"(d):"b"(st):"esi","edi","memory");
    printf("popaw %08x %08x %08x\n", a, c, d); }
  { int bounds[2]={-5,10};
    sig=0; if(!sigsetjmp(jb,1)){ __asm__ volatile("bound %%eax,%0"::"m"(bounds),"a"(7)); printf("bound in: ran\n"); } else printf("bound in: sig=%d code=%d\n", sig, code);
    sig=0; if(!sigsetjmp(jb,1)){ __asm__ volatile("bound %%eax,%0"::"m"(bounds),"a"(11)); printf("bound out: ran\n"); } else printf("bound out: sig=%d code=%d\n", sig, code);
    sig=0; if(!sigsetjmp(jb,1)){ __asm__ volatile("bound %%eax,%0"::"m"(bounds),"a"(-6)); printf("bound below: ran\n"); } else printf("bound below: sig=%d code=%d\n", sig, code); }
  { unsigned a=0x1230, f; __asm__ volatile("arpl %%cx,%%ax; pushf; pop %%edx":"+a"(a),"=d"(f):"c"(0x4563)); printf("arpl %x zf=%u\n", a, (f>>6)&1);
    a=0x1233; __asm__ volatile("arpl %%cx,%%ax; pushf; pop %%edx":"+a"(a),"=d"(f):"c"(0x4561)); printf("arpl %x zf=%u\n", a, (f>>6)&1); }
  { unsigned v; __asm__ volatile("mov %%cs,%%eax":"=a"(v)); unsigned w; __asm__ volatile("mov %%ss,%%eax":"=a"(w)); unsigned x; __asm__ volatile("mov %%ds,%%eax":"=a"(x)); printf("cs %x ss %x ds %x\n", v, w, x);
    unsigned r=0; __asm__ volatile("push %%cs; push $1f; lret; 1: mov $7,%%ebx":"+b"(r)); printf("lret %u\n", r); }
  return 0; }
