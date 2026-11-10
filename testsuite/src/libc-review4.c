// What Linux does of tracing and of terminals that a second review found the machine didn't, each in a process of its own, with an alarm
// that ends what would hang:
//   groupstop: a tracee that its tracer lets have SIGSTOP stops, which its tracer's wait says, and goes on when it is let go.
//   syscallstops: PTRACE_CONT from where a call was entered, then PTRACE_SYSCALL from a signal, stops at the next call as it is entered:
//     as many stops as it takes, each entered and left, to the end.
//   siginfo: what PTRACE_GETSIGINFO says of a stop at a call of PTRACE_O_TRACESYSGOOD: SIGTRAP | 0x80.
//   ttou: a process of the background with SIGTTOU ignored writes to its terminal of TOSTOP.
//   tcsetattr: a process of the background that sets its terminal stops of SIGTTOU.
//   hangup: the leader of a session hears SIGHUP when the master of its terminal closes.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ptrace.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

static void part(const char *name, void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(3);
    run();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("%s: ended by signal %d\n", name, WTERMSIG(status));
}

static void groupStop(void) {
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    _exit(7);
  }
  int status;
  waitpid(child, &status, 0);
  long passed = ptrace(PTRACE_CONT, child, 0, SIGSTOP);
  waitpid(child, &status, 0);
  int stopped = WIFSTOPPED(status) ? WSTOPSIG(status) : -1;
  long resumed = ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  printf("group stop of a tracee: passed %ld, stopped by %d, let go %ld, exited %d\n", passed, stopped, resumed,
         WIFEXITED(status) ? WEXITSTATUS(status) : -1);
}

static void syscallStops(void) {
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    getppid();
    raise(SIGUSR1);
    getppid();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACESYSGOOD);
  // To where a call is entered, and on from there with PTRACE_CONT.
  ptrace(PTRACE_SYSCALL, child, 0, 0);
  waitpid(child, &status, 0);
  siginfo_t info;
  memset(&info, 0, sizeof info);
  ptrace(PTRACE_GETSIGINFO, child, 0, &info);
  printf("a stop at a call: signal %d, code %#x\n", WSTOPSIG(status), info.si_code);
  ptrace(PTRACE_CONT, child, 0, 0);
  // To SIGUSR1, and from there by calls.
  waitpid(child, &status, 0);
  int stops = 0;
  ptrace(PTRACE_SYSCALL, child, 0, 0);
  while (waitpid(child, &status, 0) == child && WIFSTOPPED(status)) {
    if (WSTOPSIG(status) == (SIGTRAP | 0x80)) stops++;
    ptrace(PTRACE_SYSCALL, child, 0, 0);
  }
  printf("stops at calls from a signal to the end: %d, %s\n", stops, stops % 2 == 1 ? "each entered and left" : "one left unentered");
}

// A terminal of a session of its own, of a child that leads it, and what it runs in the background of it.
static int terminal(int *master) {
  *master = posix_openpt(O_RDWR | O_NOCTTY);
  grantpt(*master);
  unlockpt(*master);
  return 0;
}

static void backgroundWrite(void) {
  int master;
  terminal(&master);
  char *name = ptsname(master);
  setsid();
  int slave = open(name, O_RDWR);
  struct termios modes;
  tcgetattr(slave, &modes);
  modes.c_lflag |= TOSTOP;
  tcsetattr(slave, TCSANOW, &modes);
  pid_t child = fork();
  if (child == 0) {
    setpgid(0, 0);
    signal(SIGTTOU, SIG_IGN);
    ssize_t written = write(slave, "x", 1);
    printf("a write of the background with SIGTTOU ignored: %zd %s\n", written, written < 0 && errno == EIO ? "EIO" : "");
    _exit(0);
  }
  waitpid(child, 0, 0);
}

static void backgroundSet(void) {
  int master;
  terminal(&master);
  char *name = ptsname(master);
  setsid();
  int slave = open(name, O_RDWR);
  pid_t child = fork();
  if (child == 0) {
    setpgid(0, 0);
    struct termios modes;
    tcgetattr(slave, &modes);
    tcsetattr(slave, TCSANOW, &modes);
    _exit(0);
  }
  int status;
  waitpid(child, &status, WUNTRACED);
  printf("tcsetattr of the background: %s %d\n", WIFSTOPPED(status) ? "stopped by" : "exited", WIFSTOPPED(status) ? WSTOPSIG(status) : 0);
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

static int heard[2];
static void onHangup(int signal) {
  (void)signal;
  write(heard[1], "h", 1);
}

static void hangup(void) {
  int master;
  terminal(&master);
  char *name = ptsname(master);
  pipe(heard);
  pid_t child = fork();
  if (child == 0) {
    // Only the parent has the master, whose close is the last.
    close(master);
    setsid();
    signal(SIGHUP, onHangup);
    int slave = open(name, O_RDWR);
    (void)slave;
    write(heard[1], "r", 1);
    pause();
    _exit(0);
  }
  char got;
  read(heard[0], &got, 1);
  close(master);
  ssize_t size = read(heard[0], &got, 1);
  printf("the leader of a session when its master closes: %s\n", size == 1 && got == 'h' ? "SIGHUP" : "nothing");
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part("groupstop", groupStop);
  part("syscallstops", syscallStops);
  part("ttou", backgroundWrite);
  part("tcsetattr", backgroundSet);
  part("hangup", hangup);
  printf("done\n");
  return 0;
}
