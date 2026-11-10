// What Linux does of signals, terminals, tracing and timers that a fourth review found the machine didn't, each in a process of its own,
// with an alarm that ends what would hang (testLinuxRaises):
//   signalfd: a signal that another process sends with kill wakes a read of a signalfd.
//   canon: a terminal that becomes canonical gives what it had as a line, and one that becomes raw gives what it had of a line.
//   leader: a job of a terminal that the leader of its session leaves stopped and orphaned as it exits hears SIGHUP.
//   seccomp: PTRACE_SYSCALL from a stop of SECCOMP_RET_TRACE stops where the call is left, not where it is entered again.
//   alarm: what is left of an alarm is rounded to the nearest second.
//   altstack: sigaltstack of less than MINSIGSTKSZ is ENOMEM, but to disable.
//   waitid: si_status of a stop of a tracee is all of what it stopped with.
//   timerdrop: the signal of a timer that was armed again, or deleted, isn't delivered.
//   cpuclock: clock_nanosleep of the clock of a thread is EOPNOTSUPP, of the call itself.
//   tty: TIOCSCTTY of its own terminal is 0, and TIOCSPGRP of a group that there isn't ESRCH.
//   queueinfo: rt_sigqueueinfo of signal 0 says that the process is there; of a code of the kernel to another process, EPERM.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/filter.h>
#include <linux/ptrace.h>
#include <linux/seccomp.h>
#include <signal.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/signalfd.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static void part(const char *name, void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(5);
    run();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("%s: ended by signal %d\n", name, WTERMSIG(status));
}

static const char *error(long result) { return result >= 0 ? "ok" : strerror(errno); }

static void signalfdKill(void) {
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigprocmask(SIG_BLOCK, &set, 0);
  int fd = signalfd(-1, &set, 0);
  int go[2];
  pipe(go);
  pid_t child = fork();
  if (child == 0) {
    char got;
    read(go[0], &got, 1);
    kill(getppid(), SIGUSR1);
    _exit(0);
  }
  write(go[1], "g", 1);
  struct signalfd_siginfo info;
  ssize_t size = read(fd, &info, sizeof info);
  printf("signalfd: a read that kill wakes %zd, of SIGUSR1 %d\n", size, info.ssi_signo == SIGUSR1);
  waitpid(child, 0, 0);
}

static void canon(void) {
  int master = posix_openpt(O_RDWR | O_NOCTTY);
  grantpt(master);
  unlockpt(master);
  int slave = open(ptsname(master), O_RDWR | O_NOCTTY);
  struct termios modes;
  tcgetattr(slave, &modes);
  modes.c_lflag &= ~(ICANON | ECHO);
  modes.c_cc[VMIN] = 1;
  modes.c_cc[VTIME] = 0;
  tcsetattr(slave, TCSANOW, &modes);
  write(master, "abc", 3);
  usleep(100000);
  modes.c_lflag |= ICANON;
  tcsetattr(slave, TCSANOW, &modes);
  char buffer[100];
  printf("canon: what raw had, read as a line %zd, ", read(slave, buffer, sizeof buffer));
  write(master, "xyz", 3);
  usleep(100000);
  modes.c_lflag &= ~ICANON;
  tcsetattr(slave, TCSANOW, &modes);
  fcntl(slave, F_SETFL, O_NONBLOCK);
  printf("what a line had, read raw %zd\n", read(slave, buffer, sizeof buffer));
}

static int heard[2];
static void onHangup(int signal) {
  (void)signal;
  write(heard[1], "H", 1);
}

static void leader(void) {
  pipe(heard);
  int master = posix_openpt(O_RDWR | O_NOCTTY);
  grantpt(master);
  unlockpt(master);
  char *name = ptsname(master);
  pid_t first = fork();
  if (first == 0) {
    setsid();
    int slave = open(name, O_RDWR);
    pid_t job = fork();
    if (job == 0) {
      signal(SIGHUP, onHangup);
      setpgid(0, 0);
      tcsetpgrp(slave, getpid());
      usleep(300000);
      _exit(0);
    }
    setpgid(job, job);
    // Once its job stopped, of SIGTTOU as it set the foreground from the background, which leaves it orphaned and stopped as this exits.
    waitpid(job, 0, WUNTRACED);
    _exit(0);
  }
  waitpid(first, 0, 0);
  close(heard[1]);
  char got = 0;
  ssize_t size = read(heard[0], &got, 1);
  printf("leader: the foreground job hears SIGHUP as the leader exits %s\n", size == 1 && got == 'H' ? "yes" : "no");
}

static void seccompTrace(void) {
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    struct sock_filter filter[] = {BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
                                   BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_getppid, 0, 1),
                                   BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRACE | 7), BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)};
    struct sock_fprog program = {4, filter};
    prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
    prctl(PR_SET_SECCOMP, 2, &program);
    syscall(SYS_getppid);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACESECCOMP | PTRACE_O_TRACESYSGOOD);
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  printf("seccomp: a stop of it %#x, ", status >> 8);
  ptrace(PTRACE_SYSCALL, child, 0, 0);
  waitpid(child, &status, 0);
  struct ptrace_syscall_info info;
  memset(&info, 0, sizeof info);
  ptrace(PTRACE_GET_SYSCALL_INFO, child, sizeof info, &info);
  printf("then %#x where the call is %s\n", status >> 8, info.op == 2 ? "left" : info.op == 1 ? "entered" : "other");
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

// The call itself, as musl's alarm() is setitimer, which it rounds up; of a target that has it.
static void alarms(void) {
#ifdef SYS_alarm
  syscall(SYS_alarm, 3);
  usleep(700000);
  printf("alarm: of 3 after 0.7 s %ld, ", syscall(SYS_alarm, 0));
  syscall(SYS_alarm, 3);
  usleep(300000);
  printf("after 0.3 s %ld\n", syscall(SYS_alarm, 0));
#else
  printf("alarm: no call of it\n");
#endif
}

static void altstack(void) {
  static char memory[16384];
  stack_t small = {.ss_sp = memory, .ss_size = 100, .ss_flags = 0};
  printf("altstack: of 100 bytes %s, ", error(syscall(SYS_sigaltstack, &small, 0)));
  stack_t off = {.ss_sp = memory, .ss_size = 10, .ss_flags = SS_DISABLE};
  printf("to disable %s, ", error(syscall(SYS_sigaltstack, &off, 0)));
  stack_t enough = {.ss_sp = memory, .ss_size = sizeof memory, .ss_flags = 0};
  printf("of 16 KiB %s\n", error(syscall(SYS_sigaltstack, &enough, 0)));
}

static void waitidStatus(void) {
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    getppid();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACESYSGOOD);
  ptrace(PTRACE_SYSCALL, child, 0, 0);
  siginfo_t info;
  waitid(P_PID, child, &info, WEXITED | WSTOPPED);
  printf("waitid: of a stop at a call, code %d status %#x\n", info.si_code, info.si_status);
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

static void timerDrop(void) {
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGRTMIN);
  sigprocmask(SIG_BLOCK, &set, 0);
  struct sigevent event;
  memset(&event, 0, sizeof event);
  event.sigev_notify = SIGEV_SIGNAL;
  event.sigev_signo = SIGRTMIN;
  timer_t timer;
  timer_create(CLOCK_MONOTONIC, &event, &timer);
  struct itimerspec soon = {{0, 0}, {0, 1000000}}, late = {{0, 0}, {100, 0}};
  timer_settime(timer, 0, &soon, 0);
  usleep(20000);
  timer_settime(timer, 0, &late, 0);
  struct timespec none = {0, 0};
  siginfo_t info;
  printf("timerdrop: after it is armed again %s, ", sigtimedwait(&set, &info, &none) < 0 && errno == EAGAIN ? "EAGAIN" : "delivered");
  timer_settime(timer, 0, &soon, 0);
  usleep(20000);
  timer_delete(timer);
  printf("after it is deleted %s\n", sigtimedwait(&set, &info, &none) < 0 && errno == EAGAIN ? "EAGAIN" : "delivered");
}

static void cpuClock(void) {
  // The call itself, as musl says EINVAL of it without asking.
  struct timespec span = {0, 1000};
  long result = syscall(SYS_clock_nanosleep, CLOCK_THREAD_CPUTIME_ID, 0, &span, 0);
  printf("cpuclock: clock_nanosleep of the clock of a thread %s\n", result < 0 && errno == EINVAL ? "EINVAL" : strerror(errno));
}

static void tty(void) {
  int master = posix_openpt(O_RDWR | O_NOCTTY);
  grantpt(master);
  unlockpt(master);
  setsid();
  int slave = open(ptsname(master), O_RDWR);
  printf("tty: TIOCSCTTY of its own %s, ", error(ioctl(slave, TIOCSCTTY, 0)));
  pid_t nobody = 999999;
  printf("TIOCSPGRP of a group that there isn't %s\n", ioctl(slave, TIOCSPGRP, &nobody) < 0 && errno == ESRCH ? "ESRCH" : strerror(errno));
}

static void queueInfo(void) {
  siginfo_t info;
  memset(&info, 0, sizeof info);
  info.si_code = SI_QUEUE;
  printf("queueinfo: of signal 0 %s, ", error(syscall(SYS_rt_sigqueueinfo, getppid(), 0, &info)));
  pid_t child = fork();
  if (child == 0) {
    pause();
    _exit(0);
  }
  memset(&info, 0, sizeof info);
  info.si_code = 0;
  long result = syscall(SYS_rt_sigqueueinfo, child, SIGUSR1, &info);
  printf("of a code of the kernel to another %s\n", result < 0 && errno == EPERM ? "EPERM" : "sent");
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part("signalfd", signalfdKill);
  part("canon", canon);
  part("leader", leader);
  part("seccomp", seccompTrace);
  part("alarm", alarms);
  part("altstack", altstack);
  part("waitid", waitidStatus);
  part("timerdrop", timerDrop);
  part("cpuclock", cpuClock);
  part("tty", tty);
  part("queueinfo", queueInfo);
  printf("done\n");
  return 0;
}
