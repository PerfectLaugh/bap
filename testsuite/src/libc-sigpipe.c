// A write to a pipe or a socket that nothing reads any more: SIGPIPE, which ends a process that does nothing else with it, and EPIPE for
// one that ignores or handles it, or that sends with MSG_NOSIGNAL. Each is a child, of which the parent says how it ended, the same on
// each target. The libc of the tests has no sockets, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#define MSG_NOSIGNAL 0x4000

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

enum { WRITE, WRITEV, SEND, QUIET, IGNORED, HANDLED };

static volatile int handled;
static void handler(int number) { handled = number == SIGPIPE; }

// How a child that writes to what nobody reads ends: whether a signal ended it, whether that was SIGPIPE, and its status otherwise,
// which is 1 for EPIPE, and 2 more for a handler that ran.
static void run(const char *label, int how) {
  int ends[2];
  if (how == SEND || how == QUIET) syscall(SYS_socketpair, 1, 1, 0, ends);
  else pipe(ends);
  close(ends[0]);
  pid_t child = fork();
  if (child == 0) {
    signal(SIGPIPE, how == IGNORED ? SIG_IGN : how == HANDLED ? handler : SIG_DFL);
    long result;
    if (how == WRITEV) {
      struct iovec piece = {"x", 1};
      result = writev(ends[1], &piece, 1);
    } else if (how == SEND || how == QUIET) {
      result = syscall(SYS_sendto, ends[1], "x", 1, how == QUIET ? MSG_NOSIGNAL : 0, 0, 0);
    } else {
      result = write(ends[1], "x", 1);
    }
    _exit((result == -1 && errno == EPIPE ? 1 : 0) + (handled ? 2 : 0));
  }
  int status = 0;
  waitpid(child, &status, 0);
  close(ends[1]);
  say(label, 3, WIFSIGNALED(status), WIFSIGNALED(status) && WTERMSIG(status) == SIGPIPE, WIFEXITED(status) ? WEXITSTATUS(status) : -1);
}

int main(void) {
  run("write", WRITE);
  run("writev", WRITEV);
  run("send", SEND);
  run("send with MSG_NOSIGNAL", QUIET);
  run("write with SIGPIPE ignored", IGNORED);
  run("write with a handler", HANDLED);
  return 0;
}
