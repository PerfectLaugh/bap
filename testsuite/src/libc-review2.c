// More of what Linux does that a review found the machine didn't, each in a process of its own:
//   sigtimedwait: a signal that it waits for, which wasn't blocked, and whose action is the default, ends the process as Linux has it.
//   alarm: what is left of an alarm is rounded to the nearest second.
//   sigaltstack: a stack smaller than MINSIGSTKSZ is ENOMEM.
//   chown: of a file that is setuid and setgid, takes those away.
//   mkdir: keeps no setuid or setgid that its mode asks for, of a directory whose parent has none.
//   rmdir: of the root is EBUSY.
//   timerfd_create: of a clock that it has no timers of is EINVAL.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/timerfd.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void sigtimedwaitFatal(void) {
  pid_t child = fork();
  if (child == 0) {
    alarm(1);
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, SIGALRM);
    struct timespec limit = {5, 0};
    sigtimedwait(&set, 0, &limit);
    _exit(0);
  }
  int status = 0;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("sigtimedwait of an unblocked fatal signal: killed by %d\n", WTERMSIG(status));
  else printf("sigtimedwait of an unblocked fatal signal: exited %d\n", WEXITSTATUS(status));
}

static void alarmRounds(void) {
  alarm(10);
  struct timespec pause = {2, 700000000};
  nanosleep(&pause, 0);
  printf("alarm left after 2.7 s of 10: %u\n", alarm(0));
}

static void smallAltstack(void) {
  static char small[1024];
  stack_t stack = {.ss_sp = small, .ss_size = sizeof small, .ss_flags = 0};
  int result = sigaltstack(&stack, 0);
  printf("sigaltstack of 1 KiB: %d %s\n", result, result == 0 ? "" : errno == ENOMEM ? "ENOMEM" : "other");
}

static void chownClearsSetuid(void) {
  close(open("review2-file", O_CREAT | O_WRONLY, 0755));
  chmod("review2-file", 06755);
  chown("review2-file", getuid(), getgid());
  struct stat status;
  stat("review2-file", &status);
  printf("chown leaves the mode %o\n", status.st_mode & 07777);
  unlink("review2-file");
}

static void mkdirMode(void) {
  umask(0);
  mkdir("review2-dir", 06777);
  struct stat status;
  stat("review2-dir", &status);
  printf("mkdir of 6777 makes %o\n", status.st_mode & 07777);
  rmdir("review2-dir");
}

static void rmdirRoot(void) {
  int result = rmdir("/");
  printf("rmdir of the root: %d %s\n", result, errno == EBUSY ? "EBUSY" : errno == EPERM ? "EPERM" : "other");
}

static void timerfdClock(void) {
  int fd = timerfd_create(CLOCK_PROCESS_CPUTIME_ID, 0);
  printf("timerfd of a CPU clock: %s\n", fd >= 0 ? "made" : errno == EINVAL ? "EINVAL" : "other");
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  void (*parts[])(void) = {sigtimedwaitFatal, alarmRounds, smallAltstack, chownClearsSetuid, mkdirMode, rmdirRoot, timerfdClock};
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
