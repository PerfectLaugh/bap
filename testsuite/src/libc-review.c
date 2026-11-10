// What Linux does that a review found the machine didn't, each in a process of its own:
//   waitpid: a parent with a handler of SIGCHLD that waits for a child gets the child, not EINTR, as the kernel finds the zombie before
//     it looks at the signal.
//   sigsuspend: a handler that it delivers runs with the mask that sigsuspend set, and what it blocks, so that another signal that the
//     temporary mask lets through isn't blocked in it.
//   SIG_DFL: an action whose handler is SIG_DFL keeps its flags, as SA_NOCLDWAIT, which then has the children reaped.
//   dotdot: `..` after a symbolic link is of where the link leads.
//   devices: /dev/zero and /dev/null may be read at an offset and sought.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static void nothing(int signal) { (void)signal; }

static int otherBlocked = -1;
static void first(int signal) {
  (void)signal;
  sigset_t current;
  sigprocmask(SIG_BLOCK, 0, &current);
  otherBlocked = sigismember(&current, SIGUSR2);
}

static void waitpidWithHandler(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = nothing;
  sigaction(SIGCHLD, &action, 0);
  pid_t child = fork();
  if (child == 0) _exit(3);
  int status = 0;
  pid_t got = waitpid(child, &status, 0);
  if (got == child) printf("waitpid with a handler: the child, status %d\n", WEXITSTATUS(status));
  else printf("waitpid with a handler: %d, errno %d\n", (int)got, errno);
}

static void handlerOfSigsuspend(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = first;
  sigaction(SIGUSR1, &action, 0);
  action.sa_handler = nothing;
  sigaction(SIGUSR2, &action, 0);
  sigset_t both;
  sigemptyset(&both);
  sigaddset(&both, SIGUSR1);
  sigaddset(&both, SIGUSR2);
  sigprocmask(SIG_BLOCK, &both, 0);
  raise(SIGUSR1);
  sigset_t none;
  sigemptyset(&none);
  sigsuspend(&none);
  printf("in a handler of sigsuspend the other signal is %s\n", otherBlocked ? "blocked" : "not blocked");
}

static void defaultKeepsFlags(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = SIG_DFL;
  action.sa_flags = SA_NOCLDWAIT;
  sigaction(SIGCHLD, &action, 0);
  struct sigaction now;
  sigaction(SIGCHLD, 0, &now);
  printf("SIG_DFL keeps SA_NOCLDWAIT: %d\n", (now.sa_flags & SA_NOCLDWAIT) != 0);
  pid_t child = fork();
  if (child == 0) _exit(0);
  pid_t got = wait(0);
  printf("SA_NOCLDWAIT reaps: %s\n", got == -1 && errno == ECHILD ? "ECHILD" : "a zombie was left");
}

static void dotdotAfterLink(void) {
  // In the directory that it runs in, with a link that is relative too.
  mkdir("review", 0755);
  mkdir("review/real", 0755);
  mkdir("review/real/sub", 0755);
  mkdir("review/real/bin", 0755);
  close(open("review/real/bin/x", O_CREAT | O_WRONLY, 0644));
  symlink("real/sub", "review/link");
  int fd = open("review/link/../bin/x", O_RDONLY);
  printf(".. after a symbolic link: %s\n", fd >= 0 ? "where it leads" : "where it is");
}

static void devices(void) {
  char buffer[16];
  int zero = open("/dev/zero", O_RDONLY);
  int null = open("/dev/null", O_RDWR);
  printf("pread of /dev/zero %zd, lseek of /dev/null %ld, pwrite of /dev/null %zd\n", pread(zero, buffer, sizeof buffer, 7),
         (long)lseek(null, 0, SEEK_END), pwrite(null, buffer, 4, 9));
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  void (*parts[])(void) = {waitpidWithHandler, handlerOfSigsuspend, defaultKeepsFlags, dotdotAfterLink, devices};
  for (unsigned index = 0; index < sizeof parts / sizeof parts[0]; index++) {
    pid_t part = fork();
    if (part == 0) {
      parts[index]();
      _exit(0);
    }
    waitpid(part, 0, 0);
  }
  printf("done\n");
  return 0;
}
