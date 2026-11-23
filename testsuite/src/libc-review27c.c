// What a review found of the traps of x86 that the machine didn't do as a processor and Linux do, of a program of 32 bits: what is
// privileged, and INT to a gate that isn't the program's, is SIGSEGV of the kernel; INT 3 and INT1 are SIGTRAP, INT 4 and INTO of an
// overflow SIGSEGV after the instruction; SYSENTER outside of the vDSO, of an AMD, and the instructions of a monitor are SIGILL;
// INT 0x80 is the system call; and LEAVE and ENTER of 16 bits, LOOP of CX and XLAT of BX with the address-size prefix. What each
// line says is what a kernel of 64 bits on an AMD says of it.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/syscall.h>
#include <ucontext.h>
#include <unistd.h>
static sigjmp_buf jb; static volatile int sig, code; static volatile long addr, ipoff; static volatile unsigned long start;
static void h(int s, siginfo_t*i, void*u){ ucontext_t*c=u; sig=s; code=i->si_code; addr=(long)i->si_addr; ipoff=c->uc_mcontext.gregs[REG_EIP]-start; siglongjmp(jb,1);}
#define T(name, asmtext) do { extern char name##_s[]; start=(unsigned long)name##_s; sig=0; \
  if(!sigsetjmp(jb,1)) { __asm__ volatile(#name "_s: " asmtext); printf(#name ": ran\n"); } \
  else printf(#name ": sig=%d code=%d addr=%s ip+%ld\n", sig, code, addr==0?"0":(addr==(long)start+ipoff?"ip":"other"), (long)ipoff); } while(0)
int main(void){ struct sigaction sa; memset(&sa,0,sizeof sa); sa.sa_sigaction=h; sa.sa_flags=SA_SIGINFO;
  for(int s=1;s<32;s++) if(s!=SIGKILL&&s!=SIGSTOP) sigaction(s,&sa,0);
  setvbuf(stdout,0,_IONBF,0);
  T(int5,"int $5"); T(int1,"int $1"); T(int3,"int $3"); T(int3b,"int3"); T(int4,"int $4"); T(icebp,".byte 0xf1"); T(int255,"int $255");
  T(into,"mov $0x7fffffff,%eax; add $1,%eax; into"); T(intono,"xor %eax,%eax; into");
  T(cli,"cli"); T(sti,"sti"); T(inb,"inb $0x80,%al"); T(outb,"outb %al,$0x80"); T(inw,"inw %dx,%ax"); T(outl,"outl %eax,%dx"); T(insb,"insb"); T(outsl,"outsl");
  T(rdmsr,"rdmsr"); T(wrmsr,"wrmsr"); T(movcr,"mov %cr0,%eax"); T(movtocr,"mov %eax,%cr3"); T(movdr,"mov %eax,%dr7"); T(movfromdr,"mov %dr0,%eax");
  T(iret,"iret"); T(sysret,"sysretl"); T(lgdt,"lgdt (%esp)"); T(lidt,"lidt (%esp)"); T(ltr,"ltr %ax"); T(lldt,"lldt %ax"); T(invlpg,"invlpg (%esp)");
  T(clts,"clts"); T(rdpmc,"rdpmc"); T(vmcall,"vmcall"); T(vmmcall,"vmmcall"); T(hlt,"hlt"); T(wbinvd,"wbinvd"); T(invd,"invd"); T(lmsw,"lmsw %ax"); T(sysexit,"sysexit");
  T(ud2,"ud2"); T(xsetbv,"xor %ecx,%ecx; xsetbv"); T(vmxoff,"vmxoff");
  { long r; __asm__ volatile("int $0x80":"=a"(r):"a"(SYS_getpid)); printf("int80 getpid: %s\n", r==getpid()?"pid":"other"); }
  { unsigned a,d; __asm__ volatile("xgetbv":"=a"(a),"=d"(d):"c"(0)); printf("xgetbv %x %x\n", a&3, d); }
  { unsigned v=0; __asm__ volatile("smsw %%eax":"+a"(v)); printf("smsw %x\n", v); }
  { unsigned st[16]; for(int i=0;i<16;i++)st[i]=0x11110000u+i; unsigned ebp,esp;
    __asm__ volatile("mov %%esp,%%esi; mov %%ebp,%%edi; lea 32(%[st]),%%ebp; mov $0x77777777,%%esp; .byte 0x66,0xc9; mov %%esp,%%ecx; mov %%ebp,%%edx; mov %%esi,%%esp; mov %%edi,%%ebp":"=c"(esp),"=d"(ebp):[st]"b"(st):"esi","edi","memory");
    printf("leavew esp+%x ebp %d\n", esp-(unsigned)st, ebp==((((unsigned)st+32)&~0xffffu)+8));
    __asm__ volatile("mov %%esp,%%esi; mov %%ebp,%%edi; lea 32(%[st]),%%esp; mov $0x77771234,%%ebp; .byte 0x66,0xc8,0x10,0x00,0x00; mov %%esp,%%ecx; mov %%ebp,%%edx; mov %%esi,%%esp; mov %%edi,%%ebp":"=c"(esp),"=d"(ebp):[st]"b"(st):"esi","edi","memory");
    printf("enterw esp+%x ebp %x %d pushed %x\n", esp-(unsigned)st, ebp>>16, (ebp&0xffff)==(((unsigned)st+30)&0xffff), st[7]); }
  { unsigned c=0xffff0003, a=0; __asm__ volatile("1: inc %%eax; addr16 loop 1b":"+a"(a),"+c"(c)); printf("loopw %u %x\n", a, c);
    static unsigned char tab[64]; for(int i=0;i<64;i++)tab[i]=i*5; a=0x1107; __asm__ volatile("xlat":"+a"(a):"b"(tab)); printf("xlat %x\n", a); }
  return 0; }
