// What is left of the timeout of select, pselect6 and ppoll, which they write back as they return: nothing once it ran out, less than
// was given once a descriptor is ready, and less than was given once a signal ends the wait with EINTR. It says what it found, the same
// on each target: x86_64 has select of a timeval, which the others don't, and they say of pselect6 what it says of that.
#define _GNU_SOURCE
#include <errno.h>
#include <poll.h>
#include <signal.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

#ifdef SYS_ppoll_time64
#define PPOLL SYS_ppoll_time64
#define PSELECT SYS_pselect6_time64
#else
#define PPOLL SYS_ppoll
#define PSELECT SYS_pselect6
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

static void onSignal(int signal) { (void)signal; }

// A raw select of what is to read of `fd` for `seconds` and `micros`, as a result and what is left in microseconds; where there is no
// select, pselect6 of as long.
static long selectLeft(int fd, long seconds, long micros, long *left) {
  fd_set set;
  FD_ZERO(&set);
  FD_SET(fd, &set);
#ifdef SYS_select
  struct timeval time = { seconds, micros };
  long result = syscall(SYS_select, fd + 1, &set, 0, 0, &time);
  *left = time.tv_sec * 1000000 + time.tv_usec;
#else
  struct timespec time = { seconds, micros * 1000 };
  long result = syscall(PSELECT, fd + 1, &set, 0, 0, &time, 0);
  *left = time.tv_sec * 1000000 + time.tv_nsec / 1000;
#endif
  return result < 0 ? -errno : result;
}

int main(void) {
  int fds[2];
  pipe(fds);
  long left;

  // A timeout that runs out leaves nothing.
  long result = selectLeft(fds[0], 0, 30000, &left);
  say("select of 30 ms runs out", 2, result, left, 0);

  fd_set set;
  FD_ZERO(&set);
  FD_SET(fds[0], &set);
  struct timespec time = { 0, 30000000 };
  result = syscall(PSELECT, fds[0] + 1, &set, 0, 0, &time, 0);
  say("pselect6 of 30 ms runs out", 3, result, time.tv_sec, time.tv_nsec);

  struct pollfd poll_ = { fds[0], POLLIN, 0 };
  time.tv_sec = 0;
  time.tv_nsec = 30000000;
  result = syscall(PPOLL, &poll_, 1, &time, 0, 8);
  say("ppoll of 30 ms runs out", 3, result, time.tv_sec, time.tv_nsec);

  // What is ready leaves almost all of it, which is all of it of a clock that went on by nothing since the call.
  write(fds[1], "x", 1);
  time.tv_sec = 5;
  time.tv_nsec = 0;
  result = syscall(PPOLL, &poll_, 1, &time, 0, 8);
  long nanos = time.tv_sec * 1000000000L + time.tv_nsec;
  say("ppoll of 5 s ready, more than 4 s and at most 5 s left", 3, result, nanos > 4000000000L, nanos <= 5000000000L);
  result = selectLeft(fds[0], 5, 0, &left);
  say("select of 5 s ready, more than 4 s and at most 5 s left", 3, result, left > 4000000, left <= 5000000);
  char byte;
  read(fds[0], &byte, 1);

  // A signal that ends the wait leaves what was left then.
  struct sigaction action = {0};
  action.sa_handler = onSignal;
  sigaction(SIGALRM, &action, 0);
  struct itimerval timer = { { 0, 0 }, { 0, 50000 } };
  syscall(SYS_setitimer, ITIMER_REAL, &timer, 0);
  result = selectLeft(fds[0], 5, 0, &left);
  say("select of 5 s that SIGALRM ends, more than 4 s and less than 5 s left", 3, result == -EINTR, left > 4000000, left < 5000000);

  timer.it_value.tv_usec = 50000;
  syscall(SYS_setitimer, ITIMER_REAL, &timer, 0);
  time.tv_sec = 5;
  time.tv_nsec = 0;
  result = syscall(PPOLL, &poll_, 1, &time, 0, 8);
  nanos = time.tv_sec * 1000000000L + time.tv_nsec;
  say("ppoll of 5 s that SIGALRM ends, more than 4 s and less than 5 s left", 3, result == -1 && errno == EINTR,
      nanos > 4000000000L, nanos < 5000000000L);
  return 0;
}
