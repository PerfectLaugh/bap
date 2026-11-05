// seccomp: a filter of each action, what it reads of a call, what a process that it makes has, strict mode, and SECCOMP_RET_TRACE to a
// tracer. It says what it found, the same on each target. The libc of the tests has no seccomp, prctl or ptrace, so they are called
// by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

struct filter { uint16_t code; uint8_t jt, jf; uint32_t k; };
struct program { unsigned short length; struct filter *filters; };

#define STATEMENT(code, k) { (code), 0, 0, (k) }
#define JUMP(code, k, jt, jf) { (code), (jt), (jf), (k) }
#define LOAD 0x20
#define AND 0x54
#define EQUALS 0x15
#define RETURN 0x06
#define KILL_PROCESS 0x80000000u
#define KILL_THREAD 0x00000000u
#define TRAP 0x00030000u
#define ERRNO 0x00050000u
#define TRACE 0x7ff00000u
#define ALLOW 0x7fff0000u

#if defined(__x86_64__)
#define ARCH 0xC000003Eu
#elif defined(__aarch64__)
#define ARCH 0xC00000B7u
#elif defined(__arm__)
#define ARCH 0x40000028u
#elif defined(__riscv)
#define ARCH 0xC00000F3u
#endif

static void say(const char *label, int count, long a, long b, long c, long d) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[4] = {a, b, c, d};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int digit = 0;
    do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (digit) line[n++] = digits[--digit];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c) {
  long result = syscall(number, a, b, c, 0L, 0L, 0L);
  return result < 0 ? -errno : result;
}

static struct filter filters[] = {
  STATEMENT(LOAD, 4),
  JUMP(EQUALS, ARCH, 1, 0),
  STATEMENT(RETURN, KILL_PROCESS),
  STATEMENT(LOAD, 0),
  JUMP(EQUALS, SYS_getppid, 0, 1),
  STATEMENT(RETURN, ERRNO | 77),
  JUMP(EQUALS, SYS_getuid, 0, 1),
  STATEMENT(RETURN, TRAP | 0x42),
  JUMP(EQUALS, SYS_gettid, 0, 1),
  STATEMENT(RETURN, TRACE | 7),
  JUMP(EQUALS, SYS_sched_yield, 0, 1),
  STATEMENT(RETURN, KILL_THREAD),
  JUMP(EQUALS, SYS_getegid, 0, 1),
  STATEMENT(RETURN, KILL_PROCESS),
  JUMP(EQUALS, SYS_dup, 0, 4),
  STATEMENT(LOAD, 16),
  STATEMENT(AND, 0xffff),
  JUMP(EQUALS, 0x1234, 0, 1),
  STATEMENT(RETURN, ERRNO | 55),
  STATEMENT(RETURN, ALLOW),
};
static struct program program = { sizeof filters / sizeof filters[0], filters };

static volatile int trapped[4];

static void onSigsys(int signal, siginfo_t *info, void *context) {
  (void)context;
  trapped[0] = signal == SIGSYS && info->si_code == 1;
  trapped[1] = info->si_syscall == SYS_getuid;
  trapped[2] = info->si_arch == ARCH;
  trapped[3] = info->si_errno;
}

static int endOf(pid_t child) {
  int status = 0;
  waitpid(child, &status, 0);
  return WIFSIGNALED(status) ? -WTERMSIG(status) : WEXITSTATUS(status);
}

int main(void) {
  say("no_new_privs", 2, call(SYS_prctl, 38, 1, 0), call(SYS_prctl, 39, 0, 0), 0, 0);
  struct filter wrong[] = { JUMP(EQUALS, 0, 5, 0), STATEMENT(RETURN, ALLOW) };
  struct program bad = { 2, wrong };
  say("a filter that jumps out isn't taken", 1, call(SYS_seccomp, 1, 0, (long)&bad) == -EINVAL, 0, 0, 0);
  uint32_t action = KILL_PROCESS;
  say("an action that there is", 1, call(SYS_seccomp, 2, 0, (long)&action), 0, 0, 0);
  action = 0x12340000;
  say("and one that there isn't", 1, call(SYS_seccomp, 2, 0, (long)&action) == -EOPNOTSUPP, 0, 0, 0);

  // A process with the filter, which what it makes has too.
  pid_t child = fork();
  if (child == 0) {
    struct sigaction handler = {0};
    handler.sa_sigaction = onSigsys;
    handler.sa_flags = SA_SIGINFO;
    sigaction(SIGSYS, &handler, 0);
    say("filter", 2, call(SYS_seccomp, 1, 0, (long)&program), call(SYS_prctl, 21, 0, 0), 0, 0);
    say("errno", 1, call(SYS_getppid, 0, 0, 0), 0, 0, 0);
    say("of an argument", 2, call(SYS_dup, 0x51234, 0, 0), call(SYS_dup, 1, 0, 0) >= 0, 0, 0);
    say("trace without a tracer", 1, call(SYS_gettid, 0, 0, 0) == -ENOSYS, 0, 0, 0);
    call(SYS_getuid, 0, 0, 0);
    say("trap", 4, trapped[0], trapped[1], trapped[2], trapped[3]);
    // SIGSYS of a trap can't be blocked or ignored: the process ends by it.
    pid_t made = fork();
    if (made == 0) {
      sigset_t set;
      sigemptyset(&set);
      sigaddset(&set, SIGSYS);
      sigprocmask(SIG_BLOCK, &set, 0);
      call(SYS_getuid, 0, 0, 0);
      _exit(0);
    }
    say("trap with SIGSYS blocked", 1, endOf(made) == -SIGSYS, 0, 0, 0);
    made = fork();
    if (made == 0) {
      signal(SIGSYS, SIG_IGN);
      call(SYS_getuid, 0, 0, 0);
      _exit(0);
    }
    say("trap with SIGSYS ignored", 1, endOf(made) == -SIGSYS, 0, 0, 0);
    made = fork();
    if (made == 0) _exit((int)-call(SYS_getppid, 0, 0, 0));
    say("what it makes has it", 1, endOf(made), 0, 0, 0);
    made = fork();
    if (made == 0) { call(SYS_sched_yield, 0, 0, 0); _exit(0); }
    say("kill thread", 1, endOf(made) == -SIGSYS, 0, 0, 0);
    made = fork();
    if (made == 0) { call(SYS_getegid, 0, 0, 0); _exit(0); }
    say("kill process", 1, endOf(made) == -SIGSYS, 0, 0, 0);
    _exit(0);
  }
  say("the filtered process ends", 1, endOf(child), 0, 0, 0);

  // Strict mode: write, and then anything but read, write, exit and sigreturn is SIGKILL.
  child = fork();
  if (child == 0) {
    call(SYS_prctl, 22, 1, 0);
    write(1, "strict mode writes\n", 19);
    call(SYS_getpid, 0, 0, 0);
    _exit(0);
  }
  say("and then is killed", 1, endOf(child), 0, 0, 0);

  // SECCOMP_RET_TRACE stops a tracee for its tracer, which lets the call go through.
  child = fork();
  if (child == 0) {
    syscall(SYS_ptrace, 0, 0, 0, 0);
    raise(SIGSTOP);
    call(SYS_seccomp, 1, 0, (long)&program);
    _exit(call(SYS_gettid, 0, 0, 0) == call(SYS_getpid, 0, 0, 0) ? 3 : 4);
  }
  int status = 0;
  waitpid(child, &status, 0);
  syscall(SYS_ptrace, 0x4200, child, 0, 0x80);
  syscall(SYS_ptrace, 7, child, 0, 0);
  waitpid(child, &status, 0);
  unsigned long message = 0;
  syscall(SYS_ptrace, 0x4201, child, 0, &message);
  say("a tracer hears of it", 2, status >> 16, (long)message, 0, 0);
  syscall(SYS_ptrace, 7, child, 0, 0);
  say("and the call is made", 1, endOf(child), 0, 0, 0);
  return 0;
}
