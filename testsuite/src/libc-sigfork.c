// What the child of fork has of the signals of the thread that made it: the handlers it is in, which it goes back from, and the
// alternate stack, which a child of vfork keeps too and a new thread doesn't have; the mask, which a new thread of a raw clone has of
// the thread that made it; and the flags of sigaltstack, of which SS_AUTODISARM takes the alternate stack away in a handler until it
// returns, as sigreturn sets again what the context says. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static void say(const char *label, int count, long a, long b) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static char alternate[65536];

// Whether the alternate stack is the one above, and its flags.
static void sayAlternate(const char *label) {
  stack_t old;
  sigaltstack(0, &old);
  say(label, 2, old.ss_sp == alternate && old.ss_size == sizeof alternate, old.ss_flags);
}

// The status of the child, as its parent finds it.
static void sayChild(const char *label, int child) {
  int status = 0;
  waitpid(child, &status, 0);
  say(label, 2, WIFEXITED(status), WIFEXITED(status) ? WEXITSTATUS(status) : WTERMSIG(status));
}

static volatile int child = -1;

static void forks(int number) { child = fork(); }

static void forksOnAlternate(int number) {
  child = fork();
  if (child == 0) sayAlternate("child in a handler on the alternate stack: same alternate stack, flags");
}

// What a handler on the alternate stack finds: the alternate stack, the one of its context, and whether it may set another.
static long inHandler[5];

static void onAlternate(int number, siginfo_t *info, void *context) {
  stack_t old;
  sigaltstack(0, &old);
  inHandler[0] = old.ss_sp == alternate && old.ss_size == sizeof alternate;
  inHandler[1] = old.ss_flags;
  ucontext_t *user = context;
  inHandler[2] = user->uc_stack.ss_sp == alternate && user->uc_stack.ss_size == sizeof alternate;
  inHandler[3] = user->uc_stack.ss_flags;
  stack_t other = {0};
  other.ss_sp = alternate;
  other.ss_size = sizeof alternate / 2;
  inHandler[4] = sigaltstack(&other, 0) ? -errno : 0;
}

// A thread of a raw clone, which makes only system calls, as it has the thread pointer of main: its mask, what is pending for it, and
// its alternate stack, which it says by a word that main waits for.
static volatile unsigned long rawMask, rawPending;
static volatile long rawFlags, rawDone;
static long rawStack[2048] __attribute__((aligned(16)));

static void rawThread(long unused) {
  unsigned long mask = 0, pending = 0;
  stack_t old;
  syscall(SYS_rt_sigprocmask, SIG_BLOCK, 0, &mask, 8);
  syscall(SYS_rt_sigpending, &pending, 8);
  syscall(SYS_sigaltstack, 0, &old);
  rawMask = mask;
  rawPending = pending;
  rawFlags = old.ss_flags;
  __atomic_store_n(&rawDone, 1, __ATOMIC_SEQ_CST);
}

// clone, whose child runs fn(arg) on its stack and exits, as threads-arch.h has it.
static long spawn(long flags, void *stack, void (*fn)(long), long arg) {
#if defined(__x86_64__)
  long r;
  register long r10 __asm__("r10") = 0;
  register long r8 __asm__("r8") = 0;
  register long r12 __asm__("r12") = arg;
  register long r13 __asm__("r13") = (long)fn;
  __asm__ volatile("syscall\n"
                   "test %%rax, %%rax\n"
                   "jnz 1f\n"
                   "xor %%ebp, %%ebp\n"
                   "mov %%r12, %%rdi\n"
                   "call *%%r13\n"
                   "mov $60, %%eax\n"
                   "xor %%edi, %%edi\n"
                   "syscall\n"
                   "1:\n"
                   : "=a"(r)
                   : "a"(SYS_clone), "D"(flags), "S"(stack), "d"(0), "r"(r10), "r"(r8), "r"(r12), "r"(r13)
                   : "rcx", "r11", "memory");
  return r;
#elif defined(__aarch64__)
  register long x8 __asm__("x8") = SYS_clone;
  register long x0 __asm__("x0") = flags;
  register long x1 __asm__("x1") = (long)stack;
  register long x2 __asm__("x2") = 0;
  register long x3 __asm__("x3") = 0;
  register long x4 __asm__("x4") = 0;
  register long x19 __asm__("x19") = arg;
  register long x20 __asm__("x20") = (long)fn;
  __asm__ volatile("svc #0\n"
                   "cbnz x0, 1f\n"
                   "mov x29, #0\n"
                   "mov x0, x19\n"
                   "blr x20\n"
                   "mov x8, #93\n"
                   "mov x0, #0\n"
                   "svc #0\n"
                   "1:\n"
                   : "+r"(x0)
                   : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x19), "r"(x20)
                   : "x30", "memory");
  return x0;
#else
#error "no raw clone for this target"
#endif
}

static void *thread(void *unused) {
  stack_t old;
  sigaltstack(0, &old);
  say("new thread: alternate stack disabled", 1, old.ss_flags == SS_DISABLE, 0);
  return 0;
}

int main(void) {
  struct sigaction action = {0};
  action.sa_handler = forks;
  sigaction(SIGUSR1, &action, 0);
  raise(SIGUSR1);
  if (child == 0) { say("child back from the handler it was forked in", 0, 0, 0); _exit(7); }
  sayChild("fork in a handler: exited, code", child);

  stack_t given = {0};
  given.ss_sp = alternate;
  given.ss_size = sizeof alternate;
  say("sigaltstack", 1, sigaltstack(&given, 0), 0);
  child = fork();
  if (child == 0) { sayAlternate("child of fork: same alternate stack, flags"); _exit(0); }
  sayChild("fork: exited, code", child);

  child = vfork();
  if (child == 0) {
    stack_t old;
    sigaltstack(0, &old);
    _exit(old.ss_sp == alternate && old.ss_size == sizeof alternate && old.ss_flags == 0 ? 3 : 4);
  }
  sayChild("vfork: exited, code (3 if the same alternate stack)", child);

  pthread_t made;
  pthread_create(&made, 0, thread, 0);
  pthread_join(made, 0);
  sayAlternate("main thread after it: same alternate stack, flags");

  action.sa_handler = forksOnAlternate;
  action.sa_flags = SA_ONSTACK;
  sigaction(SIGUSR2, &action, 0);
  child = -1;
  raise(SIGUSR2);
  if (child == 0) { say("child back from the handler on the alternate stack", 0, 0, 0); _exit(9); }
  sayChild("fork in a handler on the alternate stack: exited, code", child);
  sayAlternate("parent back from it: same alternate stack, flags");

  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  raise(SIGUSR1);
  child = fork();
  if (child == 0) {
    sigset_t pending, mask;
    sigpending(&pending);
    sigprocmask(SIG_BLOCK, 0, &mask);
    say("child: SIGUSR1 pending, blocked", 2, sigismember(&pending, SIGUSR1), sigismember(&mask, SIGUSR1));
    _exit(0);
  }
  sayChild("fork with SIGUSR1 pending: exited, code", child);

  // SIGUSR1 is still blocked and pending for main, and SIGUSR2 is blocked too.
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR2);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  long made2 = spawn(CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD | CLONE_SYSVSEM, rawStack + 2048, rawThread, 0);
  say("raw clone", 1, made2 > 0, 0);
  while (!__atomic_load_n(&rawDone, __ATOMIC_SEQ_CST)) sched_yield();
  say("raw clone thread: SIGUSR1, SIGUSR2 blocked", 2, rawMask >> (SIGUSR1 - 1) & 1, rawMask >> (SIGUSR2 - 1) & 1);
  say("raw clone thread: SIGUSR1 pending, alternate stack disabled", 2, rawPending >> (SIGUSR1 - 1) & 1, rawFlags == SS_DISABLE);
  sigprocmask(SIG_UNBLOCK, &blocked, 0);

  // The flags of sigaltstack, by the system call, as musl takes SS_ONSTACK for an error itself: what it gives, and then whether the alternate stack is the one above, and its flags.
  static const unsigned flags[] = {0, SS_ONSTACK, SS_DISABLE, SS_AUTODISARM, SS_ONSTACK | SS_AUTODISARM, 3, 4};
  static const char *names[] = {"0", "SS_ONSTACK", "SS_DISABLE", "SS_AUTODISARM", "SS_ONSTACK|SS_AUTODISARM", "3", "4"};
  for (int index = 0; index < 7; index++) {
    stack_t none = {0};
    none.ss_flags = SS_DISABLE;
    sigaltstack(&none, 0);
    given.ss_flags = flags[index];
    char label[64] = "sigaltstack ";
    size_t n = 12;
    for (const char *name = names[index]; *name; name++) label[n++] = *name;
    label[n] = 0;
    say(label, 1, syscall(SYS_sigaltstack, &given, 0) ? -errno : 0, 0);
    sayAlternate("  then: same alternate stack, flags");
  }

  action.sa_sigaction = onAlternate;
  action.sa_flags = SA_ONSTACK | SA_SIGINFO;
  sigaction(SIGUSR2, &action, 0);
  given.ss_flags = 0;
  sigaltstack(&given, 0);
  raise(SIGUSR2);
  say("handler on the alternate stack: it has the alternate stack, flags", 2, inHandler[0], inHandler[1]);
  say("  its context: the alternate stack, flags", 2, inHandler[2], inHandler[3]);
  say("  sigaltstack in it", 1, inHandler[4], 0);
  given.ss_flags = SS_AUTODISARM;
  sigaltstack(&given, 0);
  raise(SIGUSR2);
  say("SS_AUTODISARM, in the handler: it has the alternate stack, flags", 2, inHandler[0], inHandler[1]);
  say("  its context: the alternate stack, flags", 2, inHandler[2], inHandler[3]);
  say("  sigaltstack in it", 1, inHandler[4], 0);
  sayAlternate("SS_AUTODISARM, after the handler: same alternate stack, flags");
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGUSR2, &action, 0);
  given.ss_flags = 0;
  sigaltstack(&given, 0);
  raise(SIGUSR2);
  say("handler on the stack, which sets another alternate stack", 1, inHandler[4], 0);
  sayAlternate("  after it: same alternate stack, flags");
  return 0;
}
