// sigtimedwait gives up at its time, EAGAIN, while another process sleeps longer.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <time.h>
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
  return 0;
}
