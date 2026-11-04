// Time that goes on: sleeps that take their time, in order between processes, a signal that ends one, a futex that times out, and
// the timers of setitimer, alarm and timer_create. It says what it found, the same on each target, of what doesn't depend on how fast
// it runs. The libc of the tests has no timer_create, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

// 32-bit targets have the calls of a 64-bit time_t apart, which is the one that the libc's structures have.
#ifdef SYS_timer_settime64
#define TIMER_SETTIME SYS_timer_settime64
#define TIMER_GETTIME SYS_timer_gettime64
#define FUTEX SYS_futex_time64
#else
#define FUTEX SYS_futex
#define TIMER_SETTIME SYS_timer_settime
#define TIMER_GETTIME SYS_timer_gettime
#endif

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
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

static long long nowNs(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (long long)now.tv_sec * 1000000000LL + now.tv_nsec;
}

static void sleepMs(long ms) {
  struct timespec span = { ms / 1000, (ms % 1000) * 1000000 };
  nanosleep(&span, 0);
}

static volatile int alarms = 0;
static void onAlarm(int signal) { (void)signal; alarms++; }

int main(void) {
  long long start = nowNs();
  sleepMs(50);
  long long slept = nowNs() - start;
  say("a sleep takes its time", 1, slept >= 50000000LL && slept < 5000000000LL, 0, 0);

  // Each process wakes when its time comes, the shorter sleep first.
  pid_t child = fork();
  if (child == 0) {
    sleepMs(30);
    say("the child wakes first", 0, 0, 0, 0);
    _exit(0);
  }
  sleepMs(90);
  say("then the parent", 0, 0, 0, 0);
  waitpid(child, 0, 0);

  // A signal ends a sleep with EINTR.
  struct sigaction action = {0};
  action.sa_handler = onAlarm;
  sigaction(SIGALRM, &action, 0);
  struct itimerval timer = { {0, 0}, {0, 20000} };
  say("setitimer", 1, setitimer(ITIMER_REAL, &timer, 0), 0, 0);
  start = nowNs();
  struct timespec long_ = { 5, 0 };
  int result = nanosleep(&long_, 0);
  long long waited = nowNs() - start;
  say("a signal ends a sleep", 3, result == -1 && errno == EINTR, alarms, waited >= 20000000LL && waited < 5000000000LL);

  // A timer of an interval: getitimer says it, and it goes on.
  struct itimerval every = { {0, 30000}, {0, 30000} };
  setitimer(ITIMER_REAL, &every, 0);
  struct itimerval current;
  getitimer(ITIMER_REAL, &current);
  say("getitimer", 2, current.it_interval.tv_usec, current.it_value.tv_usec <= 30000, 0);
  while (alarms < 4) sleepMs(1000);
  struct itimerval off = { {0, 0}, {0, 0} };
  setitimer(ITIMER_REAL, &off, 0);
  say("it went on", 1, alarms, 0, 0);

  // alarm says what was left of the one before.
  say("alarm", 2, alarm(5), alarm(0), 0);

  // An absolute time of clock_nanosleep.
  struct timespec target;
  clock_gettime(CLOCK_MONOTONIC, &target);
  start = (long long)target.tv_sec * 1000000000LL + target.tv_nsec;
  target.tv_nsec += 20000000;
  if (target.tv_nsec >= 1000000000) { target.tv_sec++; target.tv_nsec -= 1000000000; }
  clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &target, 0);
  say("until a time", 1, nowNs() - start >= 20000000LL, 0, 0);

  // A futex that nothing wakes times out.
  int word = 0;
  struct timespec timeout = { 0, 30000000 };
  start = nowNs();
  long futex = syscall(FUTEX, &word, 128, 0, &timeout, 0, 0);
  say("a futex times out", 2, futex == -1 && errno == ETIMEDOUT, nowNs() - start >= 30000000LL, 0);

  // A timer of timer_create, which signals with its value, as sigwaitinfo sees.
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigprocmask(SIG_BLOCK, &set, 0);
  struct { long value; int signal; int notify; int pad[16]; } event = { 77, SIGUSR1, 0 };
  int id = -1;
  say("timer_create", 1, syscall(SYS_timer_create, CLOCK_MONOTONIC, &event, &id), 0, 0);
  struct itimerspec periodic = { {0, 10000000}, {0, 10000000} };
  say("timer_settime", 1, syscall(TIMER_SETTIME, id, 0, &periodic, 0), 0, 0);
  int seen = 0;
  for (int index = 0; index < 3; index++) {
    siginfo_t info;
    if (sigwaitinfo(&set, &info) == SIGUSR1 && info.si_code == SI_TIMER && info.si_value.sival_int == 77) seen++;
  }
  struct itimerspec now_;
  syscall(TIMER_GETTIME, id, &now_);
  say("it signalled", 2, seen, now_.it_interval.tv_nsec, 0);
  say("timer_delete", 2, syscall(SYS_timer_delete, id), syscall(SYS_timer_delete, id) == -1 && errno == EINVAL, 0);
  return 0;
}
