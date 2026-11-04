// An epoll that watches an epoll that watches a timerfd: a wait on the outer one wakes when the timer expires.
#define _GNU_SOURCE
#include <errno.h>
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

#ifdef SYS_timerfd_settime64
#define SETTIME SYS_timerfd_settime64
typedef long long seconds_t;
#else
#define SETTIME SYS_timerfd_settime
typedef long seconds_t;
#endif

int main(void) {
  int timer = (int)syscall(SYS_timerfd_create, 1L, 0L, 0L, 0L, 0L, 0L);
  seconds_t when[4] = {0, 0, 0, 50000000};
  syscall(SETTIME, (long)timer, 0L, (long)when, 0L, 0L, 0L);
  int inner = (int)syscall(SYS_epoll_create1, 0L, 0L, 0L, 0L, 0L, 0L);
  int outer = (int)syscall(SYS_epoll_create1, 0L, 0L, 0L, 0L, 0L, 0L);
  struct { unsigned events; unsigned long long data; }
#ifdef __x86_64__
    __attribute__((packed))
#endif
    event = {1, 7};
  syscall(SYS_epoll_ctl, (long)inner, 1L, (long)timer, (long)&event, 0L, 0L);
  event.data = 8;
  syscall(SYS_epoll_ctl, (long)outer, 1L, (long)inner, (long)&event, 0L, 0L);
  char out[64];
  long got = syscall(SYS_epoll_pwait, (long)outer, (long)out, 4L, -1L, 0L, 8L);
  say("outer wakes", got < 0 ? -errno : got, 0);
  return 0;
}
