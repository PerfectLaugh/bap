// A wait with a mask of its own that lets through a signal that is already pending ends at once with EINTR, as the pselect pattern
// needs: pselect6, ppoll and epoll_pwait.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a, long b, long c) {
  char line[96];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < 3; index++) {
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

static volatile int heard;
static void hear(int signal) { heard++; (void)signal; }

static long milliseconds(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

#ifdef SYS_pselect6_time64
#define PSELECT SYS_pselect6_time64
#define PPOLL SYS_ppoll_time64
typedef long long seconds_t;
#else
#define PSELECT SYS_pselect6
#define PPOLL SYS_ppoll
typedef long seconds_t;
#endif

static void pend(void) {
  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  raise(SIGUSR1);
}

int main(void) {
  signal(SIGUSR1, hear);
  int pipes[2];
  pipe(pipes);
  unsigned long none[2] = {0, 0};
  seconds_t five[2] = {5, 0};

  pend();
  unsigned long readable[16] = {1UL << pipes[0]};
  struct { const unsigned long *set; unsigned long size; } with = {none, 8};
  long start = milliseconds();
  long got = syscall(PSELECT, (long)pipes[0] + 1, (long)readable, 0L, 0L, (long)five, (long)&with);
  say("pselect6", got < 0 ? -errno : got, heard, milliseconds() - start < 1000);

  pend();
  struct { int fd; short events, revents; } entry = {pipes[0], 1, 0};
  start = milliseconds();
  got = syscall(PPOLL, (long)&entry, 1L, (long)five, (long)none, 8L, 0L);
  say("ppoll", got < 0 ? -errno : got, heard, milliseconds() - start < 1000);

  pend();
  int poller = (int)syscall(SYS_epoll_create1, 0L, 0L, 0L, 0L, 0L, 0L);
  struct { unsigned events; unsigned long long data; } __attribute__((packed)) event = {1, 7};
  syscall(SYS_epoll_ctl, (long)poller, 1L, (long)pipes[0], (long)&event, 0L, 0L);
  char out[32];
  start = milliseconds();
  got = syscall(SYS_epoll_pwait, (long)poller, (long)out, 2L, 5000L, (long)none, 8L);
  say("epoll_pwait", got < 0 ? -errno : got, heard, milliseconds() - start < 1000);

  // Still blocked after: the mask was only the call's.
  raise(SIGUSR1);
  say("blocked after", heard, 0, 0);
  return 0;
}
