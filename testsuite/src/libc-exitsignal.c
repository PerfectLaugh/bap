// The signal that a process sends its parent when it exits, as clone asks for it, and what waits for it, as Linux has it: a child of
// clone with SIGUSR1 sends SIGUSR1 and not SIGCHLD, and one with 0 sends nothing; a wait sees such a child, a clone child, only with
// __WCLONE or __WALL, and a wait without them sees only the others, failing with ECHILD if there are none; a clone child isn't reaped as
// it exits when SIGCHLD is ignored, which only a child that sends SIGCHLD is; and the parent of a child that another process traces hears
// of its exit only once that tracer has waited for it. It says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#ifndef __WCLONE
#define __WCLONE 0x80000000
#endif
#ifndef __WALL
#define __WALL 0x40000000
#endif
#ifndef SYS_clone3
#define SYS_clone3 435
#endif
#define PTRACE_CONT 7
#define PTRACE_ATTACH 16

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

static long result(long value) { return value < 0 ? -errno : value; }

// A process of a raw clone, with a copy of the memory and the stack, which returns as fork does: 0 in the child.
static long cloneWith(long flags) { return syscall(SYS_clone, flags, 0, 0, 0, 0); }

static long clone3With(uint64_t flags, uint64_t exitSignal) {
  uint64_t args[8];
  memset(args, 0, sizeof args);
  args[0] = flags;
  args[4] = exitSignal;
  return syscall(SYS_clone3, args, sizeof args);
}

static volatile int usr1;
static volatile int chld;
static void onUsr1(int number) { usr1 += number == SIGUSR1; }
static void onChld(int number) { chld += number == SIGCHLD; }

static void setAction(int number, void (*handler)(int)) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  action.sa_flags = SA_RESTART;
  sigaction(number, &action, 0);
}

// What a wait of `pid` with `options` gave, and the code that the child exited with, or -1.
static void waited(const char *label, int pid, int options) {
  int status = 0;
  long got = result(waitpid(pid, &status, options));
  say(label, 2, got <= 0 ? got : got == pid || pid < 0, got > 0 && WIFEXITED(status) ? WEXITSTATUS(status) : -1);
}

int main(void) {
  setAction(SIGUSR1, onUsr1);
  setAction(SIGCHLD, onChld);

  // SIGUSR1: the parent is sent that, and only a wait with __WCLONE sees the child.
  long child = cloneWith(SIGUSR1);
  if (child == 0) _exit(7);
  say("usr1 clone", 1, child > 0, 0);
  waited("usr1 waitpid any", -1, 0);
  waited("usr1 waitpid child", child, 0);
  waited("usr1 waitpid wclone", child, __WCLONE);
  say("usr1 heard usr1 chld", 2, usr1, chld);
  waited("usr1 waitpid wclone again", -1, __WCLONE);

  // With a child of fork that runs, a wait without __WCLONE has something to wait for, and one with it sees only the clone child.
  int hold[2];
  pipe(hold);
  int forked = fork();
  if (forked == 0) {
    char byte;
    close(hold[1]);
    read(hold[0], &byte, 1);
    _exit(2);
  }
  close(hold[0]);
  child = cloneWith(SIGUSR1);
  if (child == 0) _exit(8);
  waited("mixed waitpid nohang", -1, WNOHANG);
  waited("mixed waitpid wclone", -1, __WCLONE);
  close(hold[1]);
  waited("mixed waitpid fork", -1, 0);
  say("mixed heard usr1 chld", 2, usr1, chld);

  // 0: nothing is sent, and __WALL sees it as it sees all.
  child = cloneWith(0);
  if (child == 0) _exit(4);
  waited("none waitpid any", -1, 0);
  waited("none waitpid wall", child, __WALL);
  say("none heard usr1 chld", 2, usr1, chld);

  // clone3 has it in exit_signal, and not in flags.
  child = clone3With(SIGUSR1, 0);
  if (child == 0) _exit(0);
  say("clone3 signal in flags", 1, child < 0 ? -errno : 0, 0);
  // Nor CLONE_DETACHED, whose bit clone3 keeps for itself.
  child = clone3With(0x400000, 0);
  if (child == 0) _exit(0);
  say("clone3 CLONE_DETACHED", 1, child < 0 ? -errno : 0, 0);
  child = clone3With(0, SIGUSR1);
  if (child == 0) _exit(9);
  waited("clone3 waitpid any", -1, 0);
  waited("clone3 waitpid wclone", child, __WCLONE);
  say("clone3 heard usr1 chld", 2, usr1, chld);

  // SIGCHLD ignored: a clone child stays to be waited for, and a child of fork goes.
  setAction(SIGCHLD, SIG_IGN);
  child = cloneWith(SIGUSR1);
  if (child == 0) _exit(5);
  waited("ignored clone waitpid wclone", child, __WCLONE);
  forked = fork();
  if (forked == 0) _exit(6);
  waited("ignored fork waitpid", -1, 0);
  say("ignored heard usr1", 1, usr1, 0);
  setAction(SIGCHLD, onChld);
  chld = 0;

  // A child traced by another child: its parent hears of its exit, and can wait for it, once the tracer has waited for it.
  int toTraced[2], toTracer[2], fromTracer[2];
  pipe(toTraced);
  pipe(toTracer);
  pipe(fromTracer);
  int traced = fork();
  if (traced == 0) {
    char byte;
    read(toTraced[0], &byte, 1);
    _exit(3);
  }
  int tracer = fork();
  if (tracer == 0) {
    char byte = 0;
    int status = 0;
    // It hears of the exit by SIGCHLD, which needn't interrupt it.
    setAction(SIGCHLD, SIG_DFL);
    if (syscall(SYS_ptrace, PTRACE_ATTACH, traced, 0, 0) == 0 && waitpid(traced, &status, 0) == traced) {
      syscall(SYS_ptrace, PTRACE_CONT, traced, 0, 0);
      byte = 1;
    }
    write(fromTracer[1], &byte, 1);
    // That it exited, which it doesn't wait for yet.
    siginfo_t info;
    memset(&info, 0, sizeof info);
    byte = syscall(SYS_waitid, P_PID, traced, &info, WEXITED | WNOWAIT, 0) == 0 && info.si_pid == traced;
    write(fromTracer[1], &byte, 1);
    read(toTracer[0], &byte, 1);
    byte = waitpid(traced, &status, 0) == traced && WIFEXITED(status) ? WEXITSTATUS(status) : 100;
    write(fromTracer[1], &byte, 1);
    read(toTracer[0], &byte, 1);
    _exit(0);
  }
  char byte = 0;
  read(fromTracer[0], &byte, 1);
  say("traced attached", 1, byte, 0);
  write(toTraced[1], &byte, 1);
  read(fromTracer[0], &byte, 1);
  say("traced exit seen by tracer", 1, byte, 0);
  waited("traced waitpid nohang before", traced, WNOHANG);
  say("traced heard chld before", 1, chld, 0);
  write(toTracer[1], &byte, 1);
  read(fromTracer[0], &byte, 1);
  say("traced tracer waited", 1, byte, 0);
  say("traced heard chld after", 1, chld, 0);
  waited("traced waitpid", traced, 0);
  write(toTracer[1], &byte, 1);
  waited("tracer waitpid", tracer, 0);
  return 0;
}
