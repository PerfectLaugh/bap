// What a processor raises of an instruction, as Linux has a program see it:
//   division: of x86, a division by zero and one whose quotient the destination can't hold are SIGFPE of FPE_INTDIV at the
//     instruction, with the registers as they were; of MIPS, the trap that a compiler puts after a division is, by its code.
//   traps: int3 is SIGTRAP of SI_KERNEL after it, and hlt SIGSEGV of SI_KERNEL at it; brk of AArch64 is SIGTRAP of
//     TRAP_BRKPT at it; break and the traps of MIPS are SIGTRAP but for the codes of a division.
//   unhandled: a child that nothing handles the trap of dies of the signal, as its parent sees.
//   repeated: of x86, a rep that faults leaves the iterations that completed, in the registers and in memory, as the
//     handler sees, and goes on from there when it returns; and one of more bytes than a loop may go round runs.
// What is recorded of MIPS is what do_trap_or_bp of Linux says, as qemu makes SIGTRAP of the codes of a division too.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>

static sigjmp_buf back;
static volatile int signal_, code;
static volatile long at, address;
// Where the instruction that is expected to raise is, and where what follows it is.
static volatile unsigned long raises, follows;
static volatile int resumes;

#if defined(__x86_64__)
#define PC(context) ((context)->uc_mcontext.gregs[REG_RIP])
#elif defined(__aarch64__)
#define PC(context) ((context)->uc_mcontext.pc)
#elif defined(__mips__)
#define PC(context) ((context)->uc_mcontext.pc)
#endif

static volatile unsigned long saved[4];
// A page that a handler lets a repeated instruction go on into, if there is one.
static unsigned char *opened;

static void handler(int number, siginfo_t *info, void *data) {
  ucontext_t *context = data;
  signal_ = number;
  code = info->si_code;
  // Where the thread is, from the instruction that raised: 0 at it.
  at = (long)(PC(context) - raises);
  address = number == SIGSEGV || info->si_addr == 0 ? (long)(unsigned long)info->si_addr : (long)((unsigned long)info->si_addr - raises);
#if defined(__x86_64__)
  saved[0] = context->uc_mcontext.gregs[REG_RAX];
  saved[1] = context->uc_mcontext.gregs[REG_RDX];
  saved[2] = context->uc_mcontext.gregs[REG_RCX];
  saved[3] = context->uc_mcontext.gregs[REG_RDI];
  if (opened) {
    // The instruction runs again from where it is, with what it has left to do.
    saved[0] = context->uc_mcontext.gregs[REG_RSI];
    mprotect(opened, 4096, PROT_READ | PROT_WRITE);
    opened = 0;
    return;
  }
#endif
  if (resumes) {
    PC(context) = follows;
    return;
  }
  siglongjmp(back, 1);
}

static void report(const char *what) {
  printf("%s: signal %d code %d, the thread %ld from the instruction, si_addr %ld\n", what, signal_, code, at, address);
}

#if defined(__x86_64__)
// Runs one instruction with the registers given, which raises or not.
#define RAISING(what, instruction, a, d, c)                                                                                     \
  do {                                                                                                                          \
    signal_ = 0;                                                                                                                \
    if (!sigsetjmp(back, 1)) {                                                                                                  \
      unsigned long ra = (a), rd = (d), rc = (c);                                                                               \
      __asm__ volatile("lea 1f(%%rip), %%rsi\n mov %%rsi, raises(%%rip)\n 1: " instruction : "+a"(ra), "+d"(rd), "+c"(rc)       \
                       : : "rsi", "memory", "cc");                                                                              \
      printf("%s: rax %lx rdx %lx\n", what, ra, rd);                                                                            \
    } else {                                                                                                                    \
      report(what);                                                                                                             \
      printf("  rax %lx rdx %lx rcx %lx\n", saved[0], saved[1], saved[2]);                                                      \
    }                                                                                                                           \
  } while (0)

static void division(void) {
  RAISING("div of 7 by 2", "div %%rcx", 7, 0, 2);
  RAISING("div by zero", "div %%rcx", 7, 0, 0);
  RAISING("div of 2^64 by 1", "div %%rcx", 0, 1, 1);
  RAISING("div of 2^64 + 5 by 2", "div %%rcx", 5, 1, 2);
  RAISING("div of 3 * 2^64 by 2", "div %%rcx", 0, 3, 2);
  RAISING("idiv by zero", "idiv %%rcx", 7, 0, 0);
  RAISING("idiv of the least by -1", "idiv %%rcx", 0x8000000000000000ul, -1ul, -1ul);
  RAISING("idiv of -7 by 2", "idiv %%rcx", -7ul, -1ul, 2);
  RAISING("idiv of 2^63 by 1", "idiv %%rcx", 0x8000000000000000ul, 0, 1);
  RAISING("idiv of 2^63 by -1", "idiv %%rcx", 0x8000000000000000ul, 0, -1ul);
  RAISING("idiv of 2^63 + 1 by -1", "idiv %%rcx", 0x8000000000000001ul, 0, -1ul);
  RAISING("div of 32 bits by zero", "div %%ecx", 7, 0, 0x100000000ul);
  RAISING("div of 32 bits that fits", "div %%ecx", 0xfffffffe, 0x1, 2);
  RAISING("div of 32 bits that doesn't", "div %%ecx", 0, 0x2, 2);
  RAISING("idiv of 32 bits of the least by -1", "idiv %%ecx", 0x80000000, 0xffffffff, 0xffffffff);
  RAISING("idiv of 32 bits of -2^31 - 1 by 1", "idiv %%ecx", 0x7fffffff, 0xffffffff, 1);
  RAISING("div of 16 bits that doesn't fit", "div %%cx", 0x1234, 0x10, 0x10);
  RAISING("idiv of 16 bits of 2^15 by 1", "idiv %%cx", 0x8000, 0, 1);
  RAISING("idiv of 16 bits of -2^15 by 1", "idiv %%cx", 0x8000, 0xffff, 1);
  RAISING("div of 8 bits by zero", "div %%cl", 0x1234, 0, 0);
  RAISING("div of 8 bits that doesn't fit", "div %%cl", 0x1234, 0, 0x12);
  RAISING("div of 8 bits that fits", "div %%cl", 0x1234, 0, 0x13);
  RAISING("idiv of 8 bits of -128 by -1", "idiv %%cl", 0xff80, 0, 0xff);
  RAISING("idiv of 8 bits of -129 by 1", "idiv %%cl", 0xff7f, 0, 1);
  RAISING("idiv of 8 bits of -128 by 1", "idiv %%cl", 0xff80, 0, 1);
  // What a compiler makes of a division, and of a remainder.
  volatile int zero = 0, one = 1;
  signal_ = 0;
  if (!sigsetjmp(back, 1)) printf("1 %% 0 is %d\n", one % zero);
  else printf("1 %% 0: signal %d code %d\n", signal_, code);
}

static void traps(void) {
  RAISING("int3", "int3", 1, 2, 3);
  RAISING("hlt", "hlt", 1, 2, 3);
  // A handler that returns goes on after int3, which doesn't run again.
  resumes = 0;
  struct sigaction old, returning = {0};
  returning.sa_sigaction = handler;
  returning.sa_flags = SA_SIGINFO;
  sigaction(SIGTRAP, &returning, &old);
  volatile int after = 0;
  signal_ = 0;
  if (!sigsetjmp(back, 0)) {
    // The handler's siglongjmp is replaced by a return for this one.
    __asm__ volatile("lea 1f(%%rip), %%rsi\n mov %%rsi, raises(%%rip)\n lea 2f(%%rip), %%rsi\n mov %%rsi, follows(%%rip)\n"
                     "movl $1, resumes(%%rip)\n 1: int3\n 2: movl $0, resumes(%%rip)" : : : "rsi", "memory");
    after = 1;
  }
  printf("after an int3 whose handler returned: signal %d, went on %d\n", signal_, after);
}

static unsigned long sum(const unsigned char *bytes, unsigned long count) {
  unsigned long total = 0;
  for (unsigned long index = 0; index < count; index++) total = total * 131 + bytes[index];
  return total;
}

static void repeated(void) {
  unsigned char *pages = mmap(0, 3 * 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  for (int index = 0; index < 4096; index++) pages[index] = index * 7 + 3;
  mprotect(pages + 2 * 4096, 4096, PROT_NONE);
  // Ten bytes go where they can, and the eleventh faults: the registers are of ten rounds.
  signal_ = 0;
  if (!sigsetjmp(back, 1)) {
    unsigned char *from = pages, *to = pages + 2 * 4096 - 10;
    unsigned long count = 100;
    __asm__ volatile("lea 1f(%%rip), %%rax\n mov %%rax, raises(%%rip)\n 1: rep movsb" : "+S"(from), "+D"(to), "+c"(count) : : "rax", "memory");
    printf("rep movsb into a page that isn't there: nothing\n");
  } else {
    printf("rep movsb into a page that isn't there: signal %d code %d, the thread %ld from the instruction\n", signal_, code, at);
    printf("  %ld left, the destination %ld into its page, the fault %ld; what was written %lx\n", (long)saved[2],
           (long)(saved[3] - (unsigned long)(pages + 2 * 4096)), (long)(address - (long)(pages + 2 * 4096)), sum(pages + 2 * 4096 - 16, 16));
  }
  // Of quad words, the one that straddles the pages isn't written at all.
  signal_ = 0;
  if (!sigsetjmp(back, 1)) {
    unsigned char *to = pages + 2 * 4096 - 20;
    unsigned long count = 100;
    __asm__ volatile("lea 1f(%%rip), %%rdx\n mov %%rdx, raises(%%rip)\n 1: rep stosq" : "+D"(to), "+c"(count) : "a"(0x1122334455667788ul) : "rdx", "memory");
    printf("rep stosq into a page that isn't there: nothing\n");
  } else {
    printf("rep stosq into a page that isn't there: signal %d code %d; %ld left, the destination %ld into its page; what was written %lx\n",
           signal_, code, (long)saved[2], (long)(saved[3] - (unsigned long)(pages + 2 * 4096)), sum(pages + 2 * 4096 - 24, 24));
  }
  // Backward, from a page that isn't there to read.
  signal_ = 0;
  if (!sigsetjmp(back, 1)) {
    unsigned char *from = pages + 2 * 4096 + 5, *to = pages + 100;
    unsigned long count = 50;
    __asm__ volatile("std\n rep movsb\n cld" : "+S"(from), "+D"(to), "+c"(count) : : "memory");
    printf("rep movsb backward from a page that isn't there: nothing\n");
  } else {
    __asm__ volatile("cld");
    printf("rep movsb backward from a page that isn't there: signal %d code %d; %ld left\n", signal_, code, (long)saved[2]);
  }
  // A handler that maps the page returns to the instruction, which does the rest.
  for (int index = 0; index < 4096; index++) pages[index] = index * 5 + 1;
  opened = pages + 2 * 4096;
  signal_ = 0;
  {
    unsigned char *from = pages, *to = pages + 2 * 4096 - 1000;
    unsigned long count = 3000;
    __asm__ volatile("rep movsb" : "+S"(from), "+D"(to), "+c"(count) : : "memory");
    printf("rep movsb that a handler let go on: signal %d, %ld left when it was raised, the source %ld on; %ld left, and it copied %d\n", signal_,
           (long)saved[2], (long)(saved[0] - (unsigned long)pages), (long)count, !memcmp(pages, pages + 2 * 4096 - 1000, 3000));
  }
  // The conditions of the repetitions.
  {
    unsigned char *from = pages, *to = pages + 2 * 4096 - 1000;
    unsigned long count = 3000;
    pages[2 * 4096 - 1000 + 1234] ^= 1;
    __asm__ volatile("repe cmpsb" : "+S"(from), "+D"(to), "+c"(count) : : "memory", "cc");
    printf("repe cmpsb stops with %ld left\n", (long)count);
    to = pages;
    count = 4096;
    __asm__ volatile("repne scasb" : "+D"(to), "+c"(count) : "a"(pages[777]) : "memory", "cc");
    printf("repne scasb stops with %ld left\n", (long)count);
    count = 0;
    to = pages;
    __asm__ volatile("rep stosb" : "+D"(to), "+c"(count) : "a"(0) : "memory");
    printf("rep stosb of nothing: %ld on, the first byte %d\n", (long)(to - pages), pages[0]);
  }
  munmap(pages, 3 * 4096);
  // More bytes than a loop may go round.
  unsigned long size = 17ul << 20;
  unsigned char *much = mmap(0, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  unsigned char *to = much;
  unsigned long count = size;
  __asm__ volatile("rep stosb" : "+D"(to), "+c"(count) : "a"(0x41) : "memory");
  printf("rep stosb of 17 MiB: %ld left, %ld on, the first %x, the last %x\n", (long)count, (long)(to - much), much[0], much[size - 1]);
  munmap(much, size);
}
#elif defined(__aarch64__)
static void division(void) {
  // A division by zero is zero, and nothing is raised.
  volatile long zero = 0, one = 1;
  printf("1 / 0 is %ld\n", one / zero);
}

static void traps(void) {
  signal_ = 0;
  if (!sigsetjmp(back, 1)) {
    __asm__ volatile("adr x9, 1f\n adrp x10, raises\n str x9, [x10, :lo12:raises]\n 1: brk #0x3e8" : : : "x9", "x10", "memory");
    printf("brk: nothing\n");
  } else report("brk");
  volatile int after = 0;
  signal_ = 0;
  // A handler that returns after the brk goes on, as it moved the thread, which is at the instruction.
  __asm__ volatile("adr x9, 1f\n adrp x10, raises\n str x9, [x10, :lo12:raises]\n adr x9, 2f\n adrp x10, follows\n"
                   "str x9, [x10, :lo12:follows]\n mov w9, #1\n adrp x10, resumes\n str w9, [x10, :lo12:resumes]\n"
                   "1: brk #1\n 2: adrp x10, resumes\n str wzr, [x10, :lo12:resumes]" : : : "x9", "x10", "memory");
  after = 1;
  printf("after a brk whose handler moved on: signal %d code %d, went on %d\n", signal_, code, after);
}
#elif defined(__mips__)
static void division(void) {
  volatile int zero = 0, one = 1, least = -2147483647 - 1, minus = -1;
  signal_ = 0;
  if (!sigsetjmp(back, 1)) printf("1 / 0 is %d\n", one / zero);
  else printf("1 / 0: signal %d code %d\n", signal_, code);
  signal_ = 0;
  if (!sigsetjmp(back, 1)) printf("1 %% 0 is %d\n", one % zero);
  else printf("1 %% 0: signal %d code %d\n", signal_, code);
  signal_ = 0;
  if (!sigsetjmp(back, 1)) printf("the least / -1 is %d\n", least / minus);
  else printf("the least / -1: signal %d code %d\n", signal_, code);
}

#define TRAPPING(what, instruction)                                                                                             \
  do {                                                                                                                          \
    signal_ = 0;                                                                                                                \
    if (!sigsetjmp(back, 1)) {                                                                                                  \
      __asm__ volatile(".set push\n .set noreorder\n" instruction "\n .set pop" : : "r"(one), "r"(zero) : "memory");            \
      printf("%s: nothing\n", what);                                                                                            \
    } else printf("%s: signal %d code %d\n", what, signal_, code);                                                              \
  } while (0)

static void traps(void) {
  volatile long one = 1, zero = 0;
  TRAPPING("break 7", "break 7");
  TRAPPING("break 6", "break 6");
  TRAPPING("break 0", "break 0");
  TRAPPING("break 0, 7", "break 0, 7");
  TRAPPING("teq of equals, 7", "teq %0, %0, 7");
  TRAPPING("teq of equals, 6", "teq %0, %0, 6");
  TRAPPING("teq of equals", "teq %0, %0");
  TRAPPING("teq of others, 7", "teq %0, %1, 7");
  TRAPPING("tne of others, 7", "tne %0, %1, 7");
  TRAPPING("tge of 1 and 0", "tge %0, %1");
  TRAPPING("tlt of 1 and 0", "tlt %0, %1");
  TRAPPING("tltu of 0 and 1, 7", "tltu %1, %0, 7");
  TRAPPING("teqi of 1 and 1", "teqi %0, 1");
  TRAPPING("tnei of 1 and 1", "tnei %0, 1");
}
#endif

static void unhandled(void) {
  int signals[] = {SIGTRAP, SIGFPE, SIGSEGV};
  for (int index = 0; index < 3; index++) {
    fflush(stdout);
    pid_t child = fork();
    if (child == 0) {
      signal(signals[index], SIG_DFL);
#if defined(__x86_64__)
      if (index == 0) __asm__ volatile("int3");
      volatile int zero = 0, one = 1;
      if (index == 1) one = one / zero;
      if (index == 2) __asm__ volatile("hlt");
#elif defined(__aarch64__)
      if (index == 0) __asm__ volatile("brk #0");
#elif defined(__mips__)
      if (index == 0) __asm__ volatile("break 0");
      if (index == 1) __asm__ volatile("break 7");
#endif
      _exit(index);
    }
    int status = 0;
    waitpid(child, &status, 0);
    if (WIFSIGNALED(status)) printf("a child died of the signal %d\n", WTERMSIG(status));
    else printf("a child left with %d\n", WEXITSTATUS(status));
  }
  // One that ignores or blocks what an instruction raises dies of it all the same.
  fflush(stdout);
  pid_t child = fork();
  if (child == 0) {
    signal(SIGTRAP, SIG_IGN);
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, SIGTRAP);
    sigprocmask(SIG_BLOCK, &set, 0);
#if defined(__x86_64__)
    __asm__ volatile("int3");
#elif defined(__aarch64__)
    __asm__ volatile("brk #0");
#elif defined(__mips__)
    __asm__ volatile("break 0");
#endif
    _exit(0);
  }
  int status = 0;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("a child that ignored it died of the signal %d\n", WTERMSIG(status));
  else printf("a child that ignored it left with %d\n", WEXITSTATUS(status));
}

int main(void) {
  struct sigaction action = {0};
  action.sa_sigaction = handler;
  action.sa_flags = SA_SIGINFO | SA_NODEFER;
  sigaction(SIGFPE, &action, 0);
  sigaction(SIGTRAP, &action, 0);
  sigaction(SIGSEGV, &action, 0);
  sigaction(SIGILL, &action, 0);
  division();
  traps();
  unhandled();
#if defined(__x86_64__)
  repeated();
#endif
  return 0;
}
