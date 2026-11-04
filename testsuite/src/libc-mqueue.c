// POSIX message queues: what mq_open makes and opens again, messages by priority, a queue that is full or empty, sizes and
// deadlines that are wrong, mq_notify's signal when a message comes to it empty, a receive that waits for a child, and mq_unlink, after
// which what is open stays. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b, long c) {
  char line[160];
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

static void sayText(const char *label, const char *text, long size) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  for (long index = 0; index < size; index++) line[n++] = text[index];
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

struct attributes { long flags, capacity, size, held, pad[4]; };

#ifdef SYS_mq_timedsend_time64
#define SEND SYS_mq_timedsend_time64
#define RECEIVE SYS_mq_timedreceive_time64
typedef long long seconds_t;
#else
#define SEND SYS_mq_timedsend
#define RECEIVE SYS_mq_timedreceive
typedef long seconds_t;
#endif

struct deadline { seconds_t seconds, nanoseconds; };

static long send(int fd, const char *text, long size, long priority) { return call(SEND, fd, (long)text, size, priority, 0); }

static void receive(const char *label, int fd, long size, struct deadline *due) {
  char buffer[64];
  unsigned priority = 99;
  long got = call(RECEIVE, fd, (long)buffer, size, (long)&priority, (long)due);
  if (got < 0) { say(label, 1, got, 0, 0); return; }
  say(label, 2, got, priority, 0);
  sayText(label, buffer, got);
}

static void attributesOf(const char *label, int fd) {
  struct attributes now;
  call(SYS_mq_getsetattr, fd, 0, (long)&now, 0, 0);
  say(label, 3, now.capacity, now.size, now.held);
  say(label, 1, (now.flags & O_NONBLOCK) != 0, 0, 0);
}

static volatile int heardSignal, heardCode, heardValue;

static void hear(int signal, siginfo_t *info, void *context) {
  heardSignal = signal;
  heardCode = info->si_code;
  heardValue = info->si_value.sival_int;
  (void)context;
}

int main(void) {
  call(SYS_mq_unlink, (long)"bap-queue", 0, 0, 0, 0);
  struct attributes wanted = {0, 3, 16, 0, {0}};
  int fd = (int)call(SYS_mq_open, (long)"bap-queue", O_RDWR | O_CREAT | O_EXCL, 0600, (long)&wanted, 0);
  say("open", 1, fd >= 0, 0, 0);
  attributesOf("attributes", fd);
  say("again", 2, call(SYS_mq_open, (long)"bap-queue", O_RDWR | O_CREAT | O_EXCL, 0600, 0, 0),
      call(SYS_mq_open, (long)"bap-none", O_RDWR, 0, 0, 0), 0);
  int other = (int)call(SYS_mq_open, (long)"bap-queue", O_WRONLY, 0, 0, 0);
  say("opened", 1, other >= 0, 0, 0);
  say("bad name", 1, call(SYS_mq_open, (long)"a/b", O_RDWR | O_CREAT, 0600, 0, 0), 0, 0);
  struct attributes tooBig = {0, 0, 16, 0, {0}};
  say("bad attributes", 1, call(SYS_mq_open, (long)"bap-bad", O_RDWR | O_CREAT, 0600, (long)&tooBig, 0), 0, 0);

  // By priority, and what is too much.
  say("send", 3, send(other, "low", 3, 1), send(other, "high", 4, 5), send(other, "mid", 3, 3));
  attributesOf("full", fd);
  struct attributes nonblocking = {O_NONBLOCK, 0, 0, 0, {0}};
  call(SYS_mq_getsetattr, fd, (long)&nonblocking, 0, 0, 0);
  attributesOf("nonblocking", fd);
  say("no room", 1, send(fd, "more", 4, 1), 0, 0);
  say("too big", 2, send(fd, "seventeen bytes!!", 17, 1), send(fd, "x", 1, 40000), 0);
  say("not to read", 1, call(RECEIVE, other, 0, 64, 0, 0), 0, 0);
  receive("first", fd, 64, 0);
  receive("second", fd, 64, 0);
  receive("small", fd, 8, 0);
  receive("third", fd, 64, 0);
  receive("empty", fd, 64, 0);
  struct attributes blocking = {0, 0, 0, 0, {0}};
  call(SYS_mq_getsetattr, fd, (long)&blocking, 0, 0, 0);
  struct deadline past = {0, 0}, wrong = {0, 2000000000};
  receive("past", fd, 64, &past);
  receive("wrong deadline", fd, 64, &wrong);

  // A signal when a message comes to it empty, once.
  struct sigaction action = {0};
  action.sa_sigaction = hear;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGUSR1, &action, 0);
  struct sigevent event = {0};
  event.sigev_notify = SIGEV_SIGNAL;
  event.sigev_signo = SIGUSR1;
  event.sigev_value.sival_int = 42;
  say("notify", 2, call(SYS_mq_notify, fd, (long)&event, 0, 0, 0), call(SYS_mq_notify, fd, (long)&event, 0, 0, 0), 0);
  send(fd, "ping", 4, 0);
  say("heard", 3, heardSignal == SIGUSR1, heardCode, heardValue);
  say("once", 1, call(SYS_mq_notify, fd, (long)&event, 0, 0, 0), 0, 0);
  receive("ping", fd, 64, 0);
  say("not any more", 1, call(SYS_mq_notify, fd, 0, 0, 0, 0), 0, 0);

  // A receive that waits for a child.
  int child = fork();
  if (child == 0) {
    struct timespec pause = {0, 20000000};
    nanosleep(&pause, 0);
    say("child sends", 0, 0, 0, 0);
    send(other, "late", 4, 2);
    _exit(0);
  }
  receive("waited", fd, 64, 0);
  waitpid(child, 0, 0);

  say("unlink", 2, call(SYS_mq_unlink, (long)"bap-queue", 0, 0, 0, 0), call(SYS_mq_unlink, (long)"bap-queue", 0, 0, 0, 0), 0);
  say("still open", 1, send(fd, "kept", 4, 0), 0, 0);
  receive("kept", fd, 64, 0);
  say("gone", 1, call(SYS_mq_open, (long)"bap-queue", O_RDWR, 0, 0, 0), 0, 0);
  return 0;
}
