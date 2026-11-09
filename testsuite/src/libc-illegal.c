// What an instruction that is UNDEFINED where a program runs does: it raises SIGILL, which a handler catches and jumps back from.
// On AArch64, as a device has it, at EL0:
//   dc isw, ic iallu, at s1e1r: maintenance by set and way, of all the caches and of a translation, which are of EL1.
//   mrs S3_0_c15_c0_0: a register of the implementation, of EL1, that Linux doesn't emulate a read of.
//   msr SCTLR_EL1: a register of EL1, which EL0 can't write.
//   dc civac: the clean and invalidate by address, which SCTLR_EL1.UCI lets EL0 run, as Linux sets it.
//   ldp x9,x9: a load pair to the same register twice, which Linux's processors take as UNDEFINED.
// Elsewhere, as qemu has it: what each architecture has as its undefined instruction, and what it has no meaning for.
// With an argument, what else Linux does of SIGILL:
//   info: what a handler of SA_SIGINFO is told: the code, which is ILL_ILLOPC but on x86, where it is ILL_ILLOPN, and on MIPS, where it is
//     SI_KERNEL, with no address; and whether the address and where the thread was are the instruction, or, on MIPS, where it is in the
//     delay slot of a branch, the branch.
//   default: nothing handles it, and the process ends of it.
//   blocked: it is blocked, which doesn't keep it from the thread, and the process ends of it.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

static sigjmp_buf back;

static void handler(int signal) { siglongjmp(back, signal); }

static long buffer[8] __attribute__((aligned(64)));

#define PROBE(name, code)                                                                                                            \
  do {                                                                                                                               \
    if (sigsetjmp(back, 1) == 0) {                                                                                                   \
      code;                                                                                                                          \
      printf("%s: ok\n", name);                                                                                                      \
    } else {                                                                                                                         \
      printf("%s: fault\n", name);                                                                                                   \
    }                                                                                                                                \
  } while (0)

// An instruction of 32 bits, as a word of the architecture.
#define WORD(word) __asm__ volatile(".4byte " #word ::: "memory")

#if defined(__aarch64__)
#define INST(word)                                                                                                                   \
  do {                                                                                                                               \
    register long x0 __asm__("x0") = (long)buffer;                                                                                   \
    register long x10 __asm__("x10") = (long)buffer;                                                                                 \
    __asm__ volatile(".inst " #word : "+r"(x0) : "r"(x10) : "x9", "memory");                                                         \
  } while (0)
// `ic iallu`, then a return.
__asm__(".text\n.globl illegal\n.type illegal, %function\nillegal:\n.inst 0xd508751f\nret\n");
static void probes(void) {
  PROBE("dc isw", INST(0xd50b7620));
  PROBE("ic iallu", INST(0xd508751f));
  PROBE("at s1e1r", INST(0xd5180800));
  PROBE("mrs S3_0_c15_c0_0", INST(0xd538f000));
  PROBE("msr SCTLR_EL1", INST(0xd5181000));
  PROBE("dc civac", INST(0xd50b7e20));
  PROBE("ldp x9,x9", INST(0xa9402549));
}
#elif defined(__x86_64__) || defined(__i386__)
// `ud2`, then a return.
__asm__(".text\n.globl illegal\n.type illegal, @function\nillegal:\nud2\nret\n");
static void probes(void) {
  PROBE("ud2", __asm__ volatile(".byte 0x0f, 0x0b" ::: "memory"));
  PROBE("ud1", __asm__ volatile(".byte 0x0f, 0xb9, 0xc0" ::: "memory"));
}
#elif defined(__thumb__)
// `udf`, then a return.
__asm__(".text\n.globl illegal\n.type illegal, %function\n.thumb_func\nillegal:\n.inst.n 0xde00\nbx lr\n");
static void probes(void) {
  PROBE("udf", __asm__ volatile(".inst.n 0xde00" ::: "memory"));
  // Not `udf.w #0`, 0xf7f0a000, which is the breakpoint of Linux, and raises SIGTRAP.
  PROBE("udf.w", __asm__ volatile(".inst.w 0xf7f1a000" ::: "memory"));
}
#elif defined(__arm__)
// `udf`, then a return.
__asm__(".text\n.globl illegal\n.type illegal, %function\n.arm\nillegal:\n.inst 0xe7f000f0\nbx lr\n");
static void probes(void) { PROBE("udf", __asm__ volatile(".inst 0xe7f000f0" ::: "memory")); }
#elif defined(__riscv)
// `unimp`, which is `csrrw zero, cycle, zero`, then a return.
__asm__(".text\n.globl illegal\n.type illegal, @function\nillegal:\n.4byte 0xc0001073\nret\n");
static void probes(void) {
  PROBE("unimp", WORD(0xc0001073));
  PROBE("csrr mcycle", __asm__ volatile(".4byte 0xb0002573" ::: "a0", "memory"));
}
#elif defined(__mips__)
// A return, with a reserved instruction in its delay slot: SPECIAL with the function 0x0e, which has none before release 6.
__asm__(".text\n.globl illegal\n.type illegal, @function\n.set push\n.set noreorder\nillegal:\njr $ra\n.4byte 0x0000000e\n"
        ".set pop\n");
static void probes(void) {
  PROBE("special 0x0e", WORD(0x0000000e));
  PROBE("special 0x28", WORD(0x00000028));
  PROBE("opcode 0x3b", WORD(0xec000000));
  PROBE("mfc0 $2, $12", __asm__ volatile(".4byte 0x40026000" ::: "$2", "memory"));
}
#elif defined(__powerpc__)
// A word of the primary opcode 0, which has no instruction, then a return.
__asm__(".text\n.globl illegal\n.type illegal, @function\nillegal:\n.4byte 0\nblr\n");
static void probes(void) { PROBE("opcode 0", WORD(0)); }
#endif

void illegal(void);

static unsigned long pcOf(ucontext_t *context) {
#if defined(__x86_64__)
  return context->uc_mcontext.gregs[REG_RIP];
#elif defined(__i386__)
  return context->uc_mcontext.gregs[REG_EIP];
#elif defined(__aarch64__)
  return context->uc_mcontext.pc;
#elif defined(__arm__)
  return context->uc_mcontext.arm_pc;
#elif defined(__riscv)
  return context->uc_mcontext.__gregs[0];
#elif defined(__mips__)
  return context->uc_mcontext.pc;
#elif defined(__powerpc64__)
  return context->uc_mcontext.gp_regs[32];
#elif defined(__powerpc__)
  return context->uc_mcontext.gregs[32];
#endif
}

static void informed(int signal, siginfo_t *info, void *context) {
  // Of Thumb, the address of the function says so in its lowest bit, which the instruction's doesn't.
  unsigned long at = (unsigned long)illegal & ~1ul;
  printf("signal %d code %d at %d pc %d\n", signal, info->si_code, (unsigned long)info->si_addr == at, pcOf(context) == at);
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
  probes();
  printf("done\n");
  return 0;
}
