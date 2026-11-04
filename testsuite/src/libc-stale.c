// A call that fails before it waits leaves nothing behind for the next: select of a closed descriptor, then poll's own timeout.
#define _GNU_SOURCE
#include <errno.h>
#include <time.h>
#include <sys/syscall.h>
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

#ifdef SYS_pselect6_time64
#define PSELECT SYS_pselect6_time64
typedef long long seconds_t;
#else
#define PSELECT SYS_pselect6
typedef long seconds_t;
#endif

static long wait_(int count, unsigned long *set, seconds_t seconds) {
  seconds_t span[2] = {seconds, 0};
  return syscall(PSELECT, count, (long)set, 0, 0, (long)span, 0);
}

int main(void) {
  unsigned long set[16] = {1UL << 9};
  long failed = wait_(10, set, 1);
  say("select closed", failed < 0 ? -errno : failed, 0);
  int pipes[2];
  pipe(pipes);
  unsigned long readable[16] = {1UL << pipes[0]};
  long start = milliseconds();
  long got = wait_(pipes[0] + 1, readable, 3);
  long took = milliseconds() - start;
  say("timed out", got, took >= 2900 && took < 3500);
  return 0;
}
