// epoll with EPOLLET: what is ready is told of again each time that more comes, whether or not the reader took all that was there
// before, and not when nothing came; of a pipe, a pair of sockets and an eventfd, and of a pipe that has room to write. It says what it
// found, the same on each target. The libc of the tests has no epoll, eventfd or socketpair, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

#ifndef SYS_epoll_wait
#define EPOLL_WAIT(fd, events, count, timeout) syscall(SYS_epoll_pwait, fd, events, count, timeout, 0, 8)
#else
#define EPOLL_WAIT(fd, events, count, timeout) syscall(SYS_epoll_wait, fd, events, count, timeout)
#endif

#define EPOLLIN 1u
#define EPOLLOUT 4u
#define EPOLLET (1u << 31)

struct event { uint32_t events; uint64_t data; }
#if defined(__x86_64__) || defined(__i386__)
__attribute__((packed))
#endif
;

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

static long call(long number, long a, long b, long c, long d) {
  long result = syscall(number, a, b, c, d, 0L, 0L);
  return result < 0 ? -errno : result;
}

// How many items an epoll instance has ready now.
static long ready(int epoll) {
  struct event events[4];
  return EPOLL_WAIT(epoll, events, 4, 0);
}

// What of `fd` an epoll instance tells of with EPOLLET, as `put` adds to it and `drain` takes all of it, to EAGAIN: once it comes,
// once more after a drain, not again without more, and again with more while it is still ready.
static void edges(const char *label, const char *more_, int fd, void (*put)(void), void (*drain)(void)) {
  int epoll = (int)call(SYS_epoll_create1, 0, 0, 0, 0);
  struct event watch = { EPOLLIN | EPOLLET, 7 };
  call(SYS_epoll_ctl, epoll, 1, fd, (long)&watch);
  put();
  long first = ready(epoll);
  drain();
  put();
  long afterDrain = ready(epoll);
  long again = ready(epoll);
  put();
  long more = ready(epoll);
  say(label, 3, first, afterDrain, again);
  say(more_, 1, more, 0, 0);
  close(epoll);
}

static int pipeFds[2], pair[2], counter;

static void putPipe(void) { write(pipeFds[1], "ab", 2); }
static void drainPipe(void) {
  char buffer[16];
  while (read(pipeFds[0], buffer, sizeof buffer) > 0) {}
}
static void putPair(void) { write(pair[1], "ab", 2); }
static void drainPair(void) {
  char buffer[16];
  while (read(pair[0], buffer, sizeof buffer) > 0) {}
}
static void putCounter(void) {
  uint64_t one = 1;
  write(counter, &one, 8);
}
static void drainCounter(void) {
  uint64_t value;
  while (read(counter, &value, 8) > 0) {}
}

int main(void) {
  pipe(pipeFds);
  fcntl(pipeFds[0], F_SETFL, O_NONBLOCK);
  edges("pipe", "pipe with more", pipeFds[0], putPipe, drainPipe);

  call(SYS_socketpair, 1, 1, 0, (long)pair);
  fcntl(pair[0], F_SETFL, O_NONBLOCK);
  edges("socketpair", "socketpair with more", pair[0], putPair, drainPair);

  counter = (int)call(SYS_eventfd2, 0, O_NONBLOCK, 0, 0);
  edges("eventfd", "eventfd with more", counter, putCounter, drainCounter);

  // The end of a pipe that writes, with room: told of once, and not again while nothing is read.
  int other[2];
  pipe(other);
  int epoll = (int)call(SYS_epoll_create1, 0, 0, 0, 0);
  struct event watch = { EPOLLOUT | EPOLLET, 9 };
  call(SYS_epoll_ctl, epoll, 1, other[1], (long)&watch);
  long once_ = ready(epoll);
  say("pipe to write", 2, once_, ready(epoll), 0);
  return 0;
}
