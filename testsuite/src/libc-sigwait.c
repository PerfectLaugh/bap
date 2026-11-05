// sigtimedwait gives up at its time, EAGAIN, while another process sleeps longer; a handled signal ends it with EINTR, timed or not;
// it takes the lowest signal that it waits for, the thread's own first; and a wait with a mask of its own goes on past a pending
// signal that is ignored. The waits are called by number, as the wrappers of musl go again on EINTR.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <sys/time.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a, long b) {
  char line[96];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < 2; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int digit = 0;
    do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (digit) line[n++] = digits[--digit];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long milliseconds(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

static volatile int alarms;

static void on_alarm(int signal) { (void)signal; alarms++; }

// SIGALRM in a fifth of a second, while what follows waits.
static void alarm_soon(void) {
  struct itimerval soon = {{0, 0}, {0, 200000}};
  setitimer(ITIMER_REAL, &soon, 0);
}

#ifdef SYS_rt_sigtimedwait_time64
#define TIMEDWAIT SYS_rt_sigtimedwait_time64
typedef long long seconds_t;
#else
#define TIMEDWAIT SYS_rt_sigtimedwait
typedef long seconds_t;
#endif

int main(void) {
  int child = fork();
  if (child == 0) {
    struct timespec second = {1, 0};
    nanosleep(&second, 0);
    _exit(0);
  }
  unsigned long set[2] = {1UL << (SIGUSR1 - 1), 0};
  sigprocmask(SIG_BLOCK, (sigset_t *)set, 0);
  seconds_t span[2] = {0, 100000000};
  long start = milliseconds();
  long got = syscall(TIMEDWAIT, (long)set, 0L, (long)span, 8L, 0L, 0L);
  long took = milliseconds() - start;
  say("sigtimedwait", got < 0 ? -errno : got, took >= 90 && took < 500);
  waitpid(child, 0, 0);

  // A handled SIGALRM comes while it waits for SIGUSR1.
  struct sigaction action = {0};
  action.sa_handler = on_alarm;
  sigaction(SIGALRM, &action, 0);
  span[0] = 10;
  span[1] = 0;
  alarm_soon();
  got = syscall(TIMEDWAIT, (long)set, 0L, (long)span, 8L, 0L, 0L);
  say("interrupted timed", got < 0 ? -errno : got, alarms);
  alarm_soon();
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("interrupted untimed", got < 0 ? -errno : got, alarms);

  // Of what is pending, the lowest first, whatever the order that it came in.
  set[0] |= 1UL << (SIGUSR2 - 1);
  sigprocmask(SIG_BLOCK, (sigset_t *)set, 0);
  raise(SIGUSR2);
  raise(SIGUSR1);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("thread first", got == SIGUSR1, 0);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("thread second", got == SIGUSR2, 0);
  kill(getpid(), SIGUSR2);
  kill(getpid(), SIGUSR1);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("process first", got == SIGUSR1, 0);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("process second", got == SIGUSR2, 0);
  // That of the thread before that of the process, though it is higher.
  kill(getpid(), SIGUSR1);
  raise(SIGUSR2);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("own first", got == SIGUSR2, 0);
  got = syscall(TIMEDWAIT, (long)set, 0L, 0L, 8L, 0L, 0L);
  say("then shared", got == SIGUSR1, 0);

  // SIGURG, which is ignored by default, and SIGUSR2, which is ignored by SIG_IGN, are pending while blocked; a wait that lets them
  // through drops them and goes on until SIGALRM.
  unsigned long none[2] = {0, 0};
  unsigned long ignored[2] = {(1UL << (SIGURG - 1)) | (1UL << (SIGUSR2 - 1)), 0};
  signal(SIGUSR2, SIG_IGN);
  sigprocmask(SIG_BLOCK, (sigset_t *)ignored, 0);
  raise(SIGURG);
  raise(SIGUSR2);
  alarm_soon();
  got = syscall(SYS_rt_sigsuspend, (long)none, 8L);
  say("sigsuspend", got < 0 ? -errno : got, alarms);
  raise(SIGURG);
  raise(SIGUSR2);
  alarm_soon();
  got = syscall(SYS_ppoll, 0L, 0L, 0L, (long)none, 8L);
  say("ppoll", got < 0 ? -errno : got, alarms);
  return 0;
}
