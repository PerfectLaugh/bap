// The events that a tracer asks to hear of: a tracee that forks, vforks, clones and ends stops for each, the processes that it makes
// are traced too and stop before they run, by SIGSTOP or, if it was seized, as PTRACE_INTERRUPT has it, and PTRACE_GETEVENTMSG says
// of what. It says what it found, the same on each target. The libc of the tests has no ptrace, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#define PTRACE_TRACEME 0
#define PTRACE_POKEDATA 5
#define PTRACE_CONT 7
#define PTRACE_SETOPTIONS 0x4200
#define PTRACE_GETEVENTMSG 0x4201
#define PTRACE_SEIZE 0x4206
#define PTRACE_INTERRUPT 0x4207
#define OPTIONS (0x2 | 0x4 | 0x8 | 0x20 | 0x40)
#define ALL 0x40000000

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

static volatile long go = 0;

// Makes a process of each kind, each of which ends at once, and ends with 3.
static void makeEach(void) {
  if (fork() == 0) _exit(0);
  if (vfork() == 0) _exit(0);
  if (syscall(SYS_clone, 0, 0, 0, 0, 0) == 0) _exit(0);
  _exit(3);
}

int main(void) {
  int status = 0;

  // A tracee by PTRACE_TRACEME, which stops itself for its tracer to say what to hear of.
  pid_t child = fork();
  if (child == 0) {
    trace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    makeEach();
  }
  waitpid(child, &status, 0);
  say("options", 1, trace(PTRACE_SETOPTIONS, child, 0, OPTIONS), 0, 0);
  trace(PTRACE_CONT, child, 0, 0);
  long made[3] = {0, 0, 0};
  int events = 0, stoppedBySigstop = 0, ended = 0;
  long vforked = 0;
  for (;;) {
    pid_t pid = waitpid(-1, &status, ALL);
    if (pid < 0) break;
    if (pid == child) {
      if (WIFEXITED(status)) { say("exited", 1, WEXITSTATUS(status), 0, 0); if (ended == 3) break; continue; }
      int event = status >> 16;
      // A signal that it is given, as SIGCHLD of what it made, whenever that ends, goes through to it.
      if (event == 0) { trace(PTRACE_CONT, child, 0, WSTOPSIG(status)); continue; }
      unsigned long message = 0;
      trace(PTRACE_GETEVENTMSG, child, 0, (long)&message);
      say("event", 2, event, WSTOPSIG(status) == SIGTRAP, 0);
      if (event == 1 || event == 2 || event == 3) made[events++] = (long)message;
      if (event == 2) vforked = (long)message;
      if (event == 5) say("vfork done of the vforked", 1, (long)message == vforked, 0, 0);
      if (event == 6) say("exit message", 1, (long)message == (3 << 8), 0, 0);
      trace(PTRACE_CONT, child, 0, 0);
    } else if (WIFSTOPPED(status)) {
      int known = pid == made[0] || pid == made[1] || pid == made[2];
      if (known && WSTOPSIG(status) == SIGSTOP) stoppedBySigstop++;
      trace(PTRACE_CONT, pid, 0, 0);
    } else {
      ended++;
      if (ended == 3 && waitpid(child, &status, WNOHANG | ALL) == child) { say("exited", 1, WEXITSTATUS(status), 0, 0); break; }
    }
  }
  say("made and stopped by SIGSTOP", 2, events, stoppedBySigstop, 0);

  // A seized tracee: what it makes stops as PTRACE_INTERRUPT has it, and goes on when it is let.
  child = fork();
  if (child == 0) {
    while (!go) {}
    if (fork() == 0) _exit(0);
    _exit(4);
  }
  say("seized", 1, trace(PTRACE_SEIZE, child, 0, 0x2), 0, 0);
  trace(PTRACE_INTERRUPT, child, 0, 0);
  waitpid(child, &status, ALL);
  say("interrupted", 1, status >> 16 == 128, 0, 0);
  trace(PTRACE_POKEDATA, child, (long)&go, 1);
  trace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, ALL);
  unsigned long forked = 0;
  trace(PTRACE_GETEVENTMSG, child, 0, (long)&forked);
  say("fork event", 1, status >> 16, 0, 0);
  pid_t grandchild = waitpid((pid_t)forked, &status, ALL);
  say("what it made stops", 2, grandchild == (pid_t)forked, status >> 16 == 128 && WSTOPSIG(status) == SIGTRAP, 0);
  trace(PTRACE_CONT, (pid_t)forked, 0, 0);
  trace(PTRACE_CONT, child, 0, 0);
  waitpid((pid_t)forked, &status, ALL);
  say("and ends", 1, WIFEXITED(status) && WEXITSTATUS(status) == 0, 0, 0);
  waitpid(child, &status, ALL);
  say("as does the tracee", 1, WEXITSTATUS(status), 0, 0);
  return 0;
}
