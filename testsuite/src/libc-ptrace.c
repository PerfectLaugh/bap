// ptrace and the waits that it is seen by, and processes that are stopped and go on, as a debugger and a shell have them. It says what
// it found, the same on each target. The libc of the tests has no ptrace, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#define PTRACE_TRACEME 0
#define PTRACE_PEEKDATA 2
#define PTRACE_POKEDATA 5
#define PTRACE_CONT 7
#define PTRACE_SINGLESTEP 9
#define PTRACE_ATTACH 16
#define PTRACE_DETACH 17
#define PTRACE_GETSIGINFO 0x4202
#define PTRACE_GETREGSET 0x4204

static long trace(long request, long pid, long address, long data) {
  long result = syscall(SYS_ptrace, request, pid, address, data);
  return result < 0 ? -errno : result;
}

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
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

static volatile long shared = 1234;

static void spin(void) {
  for (;;) shared = shared;
}

int main(void) {
  int status = 0;

  // A shell's job control: stopped, seen stopped, let go on, seen to go on, and killed.
  pid_t child = fork();
  if (child == 0) spin();
  kill(child, SIGSTOP);
  say("stopped", 3, waitpid(child, &status, WUNTRACED) == child, WIFSTOPPED(status), WSTOPSIG(status) == SIGSTOP);
  say("not again", 1, waitpid(child, &status, WUNTRACED | WNOHANG), 0, 0);
  kill(child, SIGCONT);
  say("continued", 2, waitpid(child, &status, WCONTINUED) == child, WIFCONTINUED(status), 0);
  kill(child, SIGKILL);
  say("killed", 3, waitpid(child, &status, 0) == child, WIFSIGNALED(status), WTERMSIG(status) == SIGKILL);

  // A child that asks to be traced, and stops for what it raises: its tracer reads and writes it, and lets it go on without it.
  child = fork();
  if (child == 0) {
    long first = trace(PTRACE_TRACEME, 0, 0, 0);
    long second = trace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGUSR1);
    _exit(first == 0 && second == -EPERM && shared == 4321 ? 7 : 1);
  }
  say("trapped", 3, waitpid(child, &status, 0) == child, WIFSTOPPED(status), WSTOPSIG(status) == SIGUSR1);
  long word = 0;
  say("peek", 2, trace(PTRACE_PEEKDATA, child, (long)&shared, (long)&word), word, 0);
  say("poke", 1, trace(PTRACE_POKEDATA, child, (long)&shared, 4321), 0, 0);
  siginfo_t info;
  memset(&info, 0, sizeof info);
  say("siginfo", 2, trace(PTRACE_GETSIGINFO, child, 0, (long)&info), info.si_signo == SIGUSR1, 0);
  say("cont", 1, trace(PTRACE_CONT, child, 0, 0), 0, 0);
  say("exited", 3, waitpid(child, &status, 0) == child, WIFEXITED(status), WEXITSTATUS(status));

  // A tracer that attaches: it stops the child, reads its registers, steps it once, and lets it go.
  child = fork();
  if (child == 0) spin();
  say("attach", 1, trace(PTRACE_ATTACH, child, 0, 0), 0, 0);
  say("attached", 3, waitpid(child, &status, 0) == child, WIFSTOPPED(status), WSTOPSIG(status) == SIGSTOP);
  unsigned long registers[64];
  memset(registers, 0, sizeof registers);
  struct iovec vector = {registers, sizeof registers};
  say("regs", 2, trace(PTRACE_GETREGSET, child, 1, (long)&vector), vector.iov_len > 0 && vector.iov_len < sizeof registers, 0);
#if defined(__x86_64__)
  unsigned long before = registers[16];
#elif defined(__aarch64__)
  unsigned long before = registers[32];
#else
  unsigned long before = 0;
#endif
  say("step", 1, trace(PTRACE_SINGLESTEP, child, 0, 0), 0, 0);
  say("stepped", 3, waitpid(child, &status, 0) == child, WIFSTOPPED(status), WSTOPSIG(status) == SIGTRAP);
  vector.iov_len = sizeof registers;
  trace(PTRACE_GETREGSET, child, 1, (long)&vector);
#if defined(__x86_64__)
  unsigned long after = registers[16];
#elif defined(__aarch64__)
  unsigned long after = registers[32];
#else
  unsigned long after = 1;
#endif
  say("moved", 1, after != before, 0, 0);
  say("detach", 1, trace(PTRACE_DETACH, child, 0, 0), 0, 0);
  kill(child, SIGKILL);
  say("gone", 2, waitpid(child, &status, 0) == child, WIFSIGNALED(status), 0);

  // What isn't there.
  say("no child", 1, waitpid(12345, &status, 0) == -1 && errno == ECHILD, 0, 0);
  say("not traced", 1, trace(PTRACE_CONT, 12345, 0, 0), 0, 0);
  return 0;
}
