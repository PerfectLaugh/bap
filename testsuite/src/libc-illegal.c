// What AArch64 does at EL0 with what only EL1 may run, and with encodings that are UNDEFINED: each raises SIGILL, which a handler
// catches and jumps back from, but for `dc civac`, which EL0 may run.
//   dc isw, ic iallu, at s1e1r: maintenance by set and way, of all the caches and of a translation, which are of EL1.
//   mrs S3_0_c15_c0_0: a register of the implementation, of EL1, that Linux doesn't emulate a read of.
//   msr SCTLR_EL1: a register of EL1, which EL0 can't write.
//   dc civac: the clean and invalidate by address, which SCTLR_EL1.UCI lets EL0 run, as Linux sets it.
//   ldp x9,x9: a load pair to the same register twice, which Linux's processors take as UNDEFINED.
// With an argument, what else Linux does of SIGILL, as qemu has it too:
//   info: what a handler of SA_SIGINFO is told: ILL_ILLOPC, and the instruction as where it was and as the address.
//   default: nothing handles it, and the process ends of it.
//   blocked: it is blocked, which doesn't keep it from the thread, and the process ends of it.
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

static sigjmp_buf back;

static void handler(int signal) { siglongjmp(back, signal); }

static long buffer[8] __attribute__((aligned(64)));

#define PROBE(name, word)                                                                                                            \
  do {                                                                                                                               \
    if (sigsetjmp(back, 1) == 0) {                                                                                                   \
      register long x0 __asm__("x0") = (long)buffer;                                                                                 \
      register long x10 __asm__("x10") = (long)buffer;                                                                               \
      __asm__ volatile(".inst " #word : "+r"(x0) : "r"(x10) : "x9", "memory");                                                       \
      printf("%s: ok\n", name);                                                                                                      \
    } else {                                                                                                                         \
      printf("%s: fault\n", name);                                                                                                   \
    }                                                                                                                                \
  } while (0)

// `ic iallu`, then a return.
void illegal(void);
__asm__(".text\n.globl illegal\n.type illegal, %function\nillegal:\n.inst 0xd508751f\nret\n");

static void informed(int signal, siginfo_t *info, void *context) {
  ucontext_t *ucontext = context;
  printf("signal %d code %d at %d pc %d\n", signal, info->si_code, info->si_addr == (void *)illegal,
         ucontext->uc_mcontext.pc == (unsigned long)illegal);
  siglongjmp(back, 1);
}

int main(int argc, char **argv) {
  setvbuf(stdout, 0, _IONBF, 0);
  if (argc > 1 && strcmp(argv[1], "info") == 0) {
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_sigaction = informed;
    action.sa_flags = SA_SIGINFO;
    sigaction(SIGILL, &action, 0);
    if (sigsetjmp(back, 1) == 0) illegal();
    return 0;
  }
  if (argc > 1 && strcmp(argv[1], "default") == 0) {
    illegal();
    printf("went on\n");
    return 0;
  }
  if (argc > 1 && strcmp(argv[1], "blocked") == 0) {
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, SIGILL);
    sigprocmask(SIG_BLOCK, &set, 0);
    illegal();
    printf("went on\n");
    return 0;
  }
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  sigaction(SIGILL, &action, 0);
  PROBE("dc isw", 0xd50b7620);
  PROBE("ic iallu", 0xd508751f);
  PROBE("at s1e1r", 0xd5180800);
  PROBE("mrs S3_0_c15_c0_0", 0xd538f000);
  PROBE("msr SCTLR_EL1", 0xd5181000);
  PROBE("dc civac", 0xd50b7e20);
  PROBE("ldp x9,x9", 0xa9402549);
  printf("done\n");
  return 0;
}
