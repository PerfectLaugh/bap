// Who may send a signal to whom, as Linux's `kill_ok_by_cred` has it, which a review found the machine didn't ask: a process that
// is no longer root may send one only to a process of its own user, but SIGCONT to any of its session, and root to any. It runs as
// root, as a program of the machine does, and gives up being root in a child, which a user namespace of the host has no other
// user to do in: what is expected of it is by `check_kill_permission` and `kill_something_info` of Linux's `kernel/signal.c`, and
// not from a run of it.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
  errno = 0;
}

int main(void) {
  setvbuf(stdout, 0, _IOLBF, 0);
  if (getuid() != 0) {
    printf("not root\n");
    return 0;
  }
  pid_t root = getpid();
  /* another process of root, for a signal to every process to have one to go to */
  pid_t other = fork();
  if (!other) { pause(); _exit(0); }
  pid_t child = fork();
  if (!child) {
    said("setuid", setuid(1000));
    said("a signal of none to a process of root", kill(root, 0));
    said("SIGUSR1 to it", kill(root, SIGUSR1));
    said("SIGCONT to it, which is of the same session", kill(root, SIGCONT));
    said("tgkill of it", syscall(SYS_tgkill, root, root, 0));
    siginfo_t info = {0};
    info.si_signo = SIGUSR1;
    info.si_code = SI_QUEUE;
    said("rt_sigqueueinfo of it", syscall(SYS_rt_sigqueueinfo, root, SIGUSR1, &info));
    said("a signal of none to itself", kill(getpid(), 0));
    said("to its process group, of which it may send to itself", kill(0, 0));
    said("to every process, of which it may send to none", kill(-1, 0));
    said("to a process that there isn't", kill(999999, 0));
    pid_t own = fork();
    if (!own) { pause(); _exit(0); }
    said("to a child of its own", kill(own, SIGKILL));
    waitpid(own, 0, 0);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  pid_t user = fork();
  if (!user) { setuid(1000); pause(); _exit(0); }
  usleep(10000);
  said("root to a process of another user", kill(user, SIGKILL));
  waitpid(user, &status, 0);
  kill(other, SIGKILL);
  waitpid(other, &status, 0);
  return 0;
}
