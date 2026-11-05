// Signals sent to a child that has exited and that nothing has waited for yet, a zombie, as Linux has them: kill, tkill, tgkill and
// rt_sigqueueinfo succeed and do nothing to it, as does kill of a process group that has only it, until it is reaped, after which
// there is no such process. It says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

static long result(long value) { return value < 0 ? -errno : value; }

// Waits until the child has exited, and leaves it a zombie: what this says is the code that it exited with.
static long exited(int child) {
  siginfo_t info;
  memset(&info, 0, sizeof info);
  long r = syscall(SYS_waitid, P_PID, child, &info, WEXITED | WNOWAIT, 0);
  return r < 0 ? -errno : (info.si_pid == child && info.si_code == CLD_EXITED ? info.si_status : -1000);
}

static long queue(int pid, int signal) {
  siginfo_t info;
  memset(&info, 0, sizeof info);
  info.si_signo = signal;
  info.si_code = SI_QUEUE;
  info.si_pid = getpid();
  return result(syscall(SYS_rt_sigqueueinfo, pid, signal, &info));
}

int main(void) {
  int child = fork();
  if (child == 0) _exit(3);
  say("zombie", exited(child));
  say("kill 0", result(kill(child, 0)));
  say("kill SIGTERM", result(kill(child, SIGTERM)));
  say("kill SIGKILL", result(kill(child, SIGKILL)));
  say("tkill SIGUSR1", result(syscall(SYS_tkill, child, SIGUSR1)));
  say("tgkill SIGUSR1", result(syscall(SYS_tgkill, child, child, SIGUSR1)));
  say("tgkill 0 of another process", result(syscall(SYS_tgkill, getpid(), child, 0)));
  say("rt_sigqueueinfo SIGUSR2", queue(child, SIGUSR2));
  // What was sent changed nothing of it: it still exited with 3.
  say("still zombie", exited(child));
  int status = 0;
  say("reaped", waitpid(child, &status, 0) == child);
  say("exited", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  say("reaped kill 0", result(kill(child, 0)));
  say("reaped tgkill 0", result(syscall(SYS_tgkill, child, child, 0)));
  say("reaped rt_sigqueueinfo SIGUSR2", queue(child, SIGUSR2));

  // A process group of which the one process is a zombie.
  child = fork();
  if (child == 0) {
    syscall(SYS_setpgid, 0, 0);
    _exit(4);
  }
  syscall(SYS_setpgid, child, child);
  say("group zombie", exited(child));
  say("group kill 0", result(kill(-child, 0)));
  say("group kill SIGTERM", result(kill(-child, SIGTERM)));
  say("group reaped", waitpid(child, &status, 0) == child);
  say("group exited", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  say("group reaped kill 0", result(kill(-child, 0)));
  return 0;
}
