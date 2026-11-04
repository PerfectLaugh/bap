// A sleep that a signal ends says what was left of it, so that sleeping again for that ends on time.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <sys/syscall.h>
#include <sys/time.h>
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

static volatile int alarms;
static void ring(int signal) { alarms++; (void)signal; }

static long milliseconds(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

int main(void) {
  struct sigaction action = {0};
  action.sa_handler = ring;
  sigaction(SIGALRM, &action, 0);
  struct itimerval every = {{0, 30000}, {0, 30000}};
  setitimer(ITIMER_REAL, &every, 0);
  struct timespec want = {1, 0}, left = {0, 0};
  long start = milliseconds();
  long got = nanosleep(&want, &left) < 0 ? -errno : 0;
  long leftMs = left.tv_sec * 1000 + left.tv_nsec / 1000000;
  say("interrupted", got, leftMs > 900 && leftMs < 1000);
  // Sleeping for what is left, each time, ends when the whole second is over.
  while (nanosleep(&left, &left) < 0 && errno == EINTR) {}
  long took = milliseconds() - start;
  say("whole second", took >= 990 && took < 1500, alarms > 10);
  struct itimerval off = {{0, 0}, {0, 0}};
  setitimer(ITIMER_REAL, &off, 0);
  return 0;
}
