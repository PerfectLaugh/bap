// A parent that doesn't wait for its children, as Linux has it: when SIGCHLD is ignored, or its action has SA_NOCLDWAIT, a child that
// exits goes at once, without being a zombie, and a wait for it, or for any child, waits until there are none and fails with ECHILD.
// With SA_NOCLDWAIT and a handler, the handler still runs. Ignoring SIGCHLD by default is not this: a wait gets the child. It says
// what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
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

static void sleepMs(long ms) {
  struct timespec span = {0, ms * 1000000};
  nanosleep(&span, 0);
}

static void setAction(void (*handler)(int), int flags) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  action.sa_flags = flags;
  sigaction(SIGCHLD, &action, 0);
}

static volatile int heard;
static void onChild(int number) { heard += number == SIGCHLD; }

int main(void) {
  int status = 0;

  // Ignored: the child is gone as it exits.
  setAction(SIG_IGN, 0);
  int child = fork();
  if (child == 0) _exit(3);
  say("ignored waitpid any", result(waitpid(-1, &status, 0)));
  say("ignored waitpid child", result(waitpid(child, &status, 0)));
  say("ignored kill 0", result(kill(child, 0)));

  // A child of vfork, the same.
  child = vfork();
  if (child == 0) _exit(5);
  say("ignored vfork waitpid", result(waitpid(child, &status, 0)));
  say("ignored vfork kill 0", result(kill(child, 0)));

  // A wait waits for all of them to have exited, and then there is none.
  int first = fork();
  if (first == 0) { sleepMs(20); _exit(1); }
  int second = fork();
  if (second == 0) { sleepMs(60); _exit(2); }
  say("ignored waitpid two", result(waitpid(-1, &status, 0)));
  say("first kill 0", result(kill(first, 0)));
  say("second kill 0", result(kill(second, 0)));
  siginfo_t info;
  memset(&info, 0, sizeof info);
  say("ignored waitid", result(syscall(SYS_waitid, P_ALL, 0, &info, WEXITED, 0)));

  // SA_NOCLDWAIT with a handler: the handler runs, and there is nothing to wait for.
  setAction(onChild, SA_NOCLDWAIT | SA_RESTART);
  child = fork();
  if (child == 0) _exit(3);
  say("nocldwait waitpid", result(waitpid(-1, &status, 0)));
  say("nocldwait handler", heard);
  say("nocldwait kill 0", result(kill(child, 0)));

  // By default it is ignored too, but the child waits to be reaped.
  setAction(SIG_DFL, 0);
  child = fork();
  if (child == 0) _exit(3);
  say("default waitpid", result(waitpid(-1, &status, 0)) == child);
  say("default exited", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  say("default kill 0", result(kill(child, 0)));
  return 0;
}
