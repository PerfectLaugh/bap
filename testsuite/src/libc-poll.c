// Waiting for descriptors: poll, select, epoll and ppoll on pipes, what eventfd, timerfd and signalfd make, a signal that ends a wait
// with EINTR, and a read that SA_RESTART has go on. It says what it found, the same on each target. The libc of the tests has no
// epoll, eventfd, timerfd or signalfd, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <sys/select.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

#ifdef SYS_timerfd_settime64
#define TIMERFD_SETTIME SYS_timerfd_settime64
#define PPOLL SYS_ppoll_time64
#define PSELECT SYS_pselect6_time64
#else
#define TIMERFD_SETTIME SYS_timerfd_settime
#define PPOLL SYS_ppoll
#define PSELECT SYS_pselect6
#endif
#ifndef SYS_epoll_wait
#define EPOLL_WAIT(fd, events, count, timeout) syscall(SYS_epoll_pwait, fd, events, count, timeout, 0, 8)
#else
#define EPOLL_WAIT(fd, events, count, timeout) syscall(SYS_epoll_wait, fd, events, count, timeout)
#endif

#define EPOLLIN 1u
#define EPOLLONESHOT (1u << 30)
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

static long long nowNs(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (long long)now.tv_sec * 1000000000LL + now.tv_nsec;
}

static void sleepMs(long ms) {
  struct timespec span = { 0, ms * 1000000 };
  nanosleep(&span, 0);
}

// poll and select of what every target has, ppoll and pselect6.
static int pollMs(struct pollfd *fds, long count, long ms) {
  struct timespec span = { ms / 1000, (ms % 1000) * 1000000 };
  return (int)syscall(PPOLL, fds, count, ms < 0 ? 0 : &span, 0, 8);
}

static int selectNow(int count, fd_set *readable, fd_set *writable) {
  struct timespec none = { 0, 0 };
  return (int)syscall(PSELECT, count, readable, writable, 0, &none, 0);
}

static long call(long number, long a, long b, long c, long d) {
  long result = syscall(number, a, b, c, d, 0L, 0L);
  return result < 0 ? -errno : result;
}

static volatile int caught = 0;
static void onSignal(int signal) { (void)signal; caught++; }

int main(void) {
  int fds[2];
  pipe(fds);
  struct pollfd one = { fds[0], POLLIN, 0 };
  say("poll of an empty pipe", 2, pollMs(&one, 1, 0), one.revents, 0);
  long long start = nowNs();
  say("times out", 2, pollMs(&one, 1, 30), nowNs() - start >= 30000000LL, 0);
  write(fds[1], "x", 1);
  say("and of one that has something", 2, pollMs(&one, 1, -1), one.revents, 0);
  char byte;
  read(fds[0], &byte, 1);

  // What another process writes ends a wait.
  pid_t child = fork();
  if (child == 0) { sleepMs(20); write(fds[1], "y", 1); _exit(0); }
  say("a wait that something ends", 2, pollMs(&one, 1, -1), one.revents, 0);
  read(fds[0], &byte, 1);
  waitpid(child, 0, 0);

  // select: what can be read and written.
  fd_set readable, writable;
  FD_ZERO(&readable); FD_ZERO(&writable);
  FD_SET(fds[0], &readable); FD_SET(fds[1], &writable);
  int found = selectNow(fds[1] + 1, &readable, &writable);
  say("select", 3, found, FD_ISSET(fds[0], &readable) != 0, FD_ISSET(fds[1], &writable) != 0);

  // A pipe that nothing writes any more hangs up.
  close(fds[1]);
  say("a pipe that nothing writes", 2, pollMs(&one, 1, 0), one.revents, 0);
  close(fds[0]);

  // eventfd: counts, and as a semaphore, one at a time.
  int counter = (int)call(SYS_eventfd2, 3, 0, 0, 0);
  uint64_t value = 0;
  read(counter, &value, 8);
  struct pollfd ofCounter = { counter, POLLIN | POLLOUT, 0 };
  say("eventfd", 3, (long)value, pollMs(&ofCounter, 1, 0), ofCounter.revents);
  value = 5;
  write(counter, &value, 8);
  read(counter, &value, 8);
  say("eventfd counts", 1, (long)value, 0, 0);
  int semaphore = (int)call(SYS_eventfd2, 2, 1 | O_NONBLOCK, 0, 0);
  uint64_t first = 0, second = 0;
  read(semaphore, &first, 8);
  read(semaphore, &second, 8);
  long empty = read(semaphore, &value, 8);
  say("one at a time", 3, (long)(first + second), empty == -1 && errno == EAGAIN, 0);

  // timerfd: a read waits until it expires, and says how many times it did.
  int timer = (int)call(SYS_timerfd_create, CLOCK_MONOTONIC, 0, 0, 0);
  struct itimerspec once = { {0, 0}, {0, 20000000} };
  call(TIMERFD_SETTIME, timer, 0, (long)&once, 0);
  start = nowNs();
  uint64_t expirations = 0;
  read(timer, &expirations, 8);
  say("timerfd", 2, (long)expirations, nowNs() - start >= 20000000LL, 0);
  struct itimerspec every = { {0, 10000000}, {0, 10000000} };
  call(TIMERFD_SETTIME, timer, 0, (long)&every, 0);
  sleepMs(35);
  read(timer, &expirations, 8);
  say("as many times as it expired", 1, (long)expirations, 0, 0);
  close(timer);

  // signalfd: a signal that is blocked is read.
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigprocmask(SIG_BLOCK, &set, 0);
  int signals = (int)call(SYS_signalfd4, -1, (long)&set, 8, 0);
  struct pollfd ofSignals = { signals, POLLIN, 0 };
  say("signalfd with nothing", 1, pollMs(&ofSignals, 1, 0), 0, 0);
  kill(getpid(), SIGUSR1);
  say("and with a signal", 2, pollMs(&ofSignals, 1, 0), ofSignals.revents, 0);
  uint32_t info[32];
  say("reads it", 2, read(signals, info, sizeof info), info[0] == SIGUSR1, 0);
  sigprocmask(SIG_UNBLOCK, &set, 0);

  // epoll: what is ready, once of EPOLLET until it isn't, and of EPOLLONESHOT until EPOLL_CTL_MOD.
  pipe(fds);
  int epoll = (int)call(SYS_epoll_create1, 0, 0, 0, 0);
  struct event watch = { EPOLLIN, 42 };
  say("epoll_ctl", 1, call(SYS_epoll_ctl, epoll, 1, fds[0], (long)&watch), 0, 0);
  struct event events[4];
  say("epoll_wait of nothing", 1, EPOLL_WAIT(epoll, events, 4, 0), 0, 0);
  write(fds[1], "z", 1);
  long got = EPOLL_WAIT(epoll, events, 4, -1);
  say("epoll_wait", 3, got, events[0].events, (long)events[0].data);
  watch.events = EPOLLIN | EPOLLET;
  call(SYS_epoll_ctl, epoll, 3, fds[0], (long)&watch);
  say("edge", 2, EPOLL_WAIT(epoll, events, 4, 0), EPOLL_WAIT(epoll, events, 4, 0), 0);
  watch.events = EPOLLIN | EPOLLONESHOT;
  call(SYS_epoll_ctl, epoll, 3, fds[0], (long)&watch);
  long once_ = EPOLL_WAIT(epoll, events, 4, 0);
  write(fds[1], "w", 1);
  say("one shot", 2, once_, EPOLL_WAIT(epoll, events, 4, 0), 0);
  call(SYS_epoll_ctl, epoll, 3, fds[0], (long)&watch);
  say("until it is changed", 1, EPOLL_WAIT(epoll, events, 4, 0), 0, 0);
  say("an eventfd is watched", 1, call(SYS_epoll_ctl, epoll, 1, counter, (long)&watch) >= 0, 0, 0);
  call(SYS_epoll_ctl, epoll, 2, fds[0], 0);
  say("nor what was taken away", 1, EPOLL_WAIT(epoll, events, 4, 0), 0, 0);

  // A signal ends a wait of ppoll, which has the mask that it gives while it waits.
  struct sigaction action = {0};
  action.sa_handler = onSignal;
  sigaction(SIGUSR1, &action, 0);
  sigprocmask(SIG_BLOCK, &set, 0);
  child = fork();
  if (child == 0) { sleepMs(20); kill(getppid(), SIGUSR1); _exit(0); }
  sigset_t open_;
  sigemptyset(&open_);
  struct timespec long_ = { 5, 0 };
  int result = (int)syscall(PPOLL, 0, 0, &long_, &open_, 8);
  say("a signal ends ppoll", 2, result == -1 && errno == EINTR, caught, 0);
  waitpid(child, 0, 0);
  sigprocmask(SIG_UNBLOCK, &set, 0);

  // A read that a signal comes to: EINTR without SA_RESTART, and it goes on with it.
  child = fork();
  if (child == 0) { sleepMs(20); kill(getppid(), SIGUSR1); sleepMs(20); write(fds[1], "v", 1); _exit(0); }
  char buffer[4];
  read(fds[0], buffer, 4);
  long interrupted = read(fds[0], buffer, 4);
  say("a read without SA_RESTART", 2, interrupted == -1 && errno == EINTR, caught, 0);
  read(fds[0], buffer, 4);
  waitpid(child, 0, 0);
  action.sa_flags = SA_RESTART;
  sigaction(SIGUSR1, &action, 0);
  child = fork();
  if (child == 0) { sleepMs(20); kill(getppid(), SIGUSR1); sleepMs(20); write(fds[1], "u", 1); _exit(0); }
  long restarted = read(fds[0], buffer, 4);
  say("and with it", 3, restarted, buffer[0] == 'u', caught);
  waitpid(child, 0, 0);
  return 0;
}
