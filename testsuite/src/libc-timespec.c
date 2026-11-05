// Times that Linux doesn't take: a timespec with a negative second or nanoseconds that aren't less than a second, and a timeval
// with microseconds that aren't less than a second, which each call that is given one fails with EINVAL, and, after each, a time of
// nothing, which it takes. Nothing waits. It says what it found, the same on each target. The calls are made by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <unistd.h>

long syscall(long, ...);

#define FUTEX_WAIT_PRIVATE 128

#ifndef SYS_epoll_pwait2
#define SYS_epoll_pwait2 441
#endif

static void say(const char *label, long value) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int digit = 0;
  do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (digit) line[n++] = digits[--digit];
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

struct span { long seconds, fraction; };
struct pair { struct span interval, value; };

static struct span zero = {0, 0};
static struct span tooMany = {0, 1000000000};
static struct span negative = {-1, 0};
static struct span below = {0, -1};

struct sqe { unsigned char opcode, flags; unsigned short priority; int fd; unsigned long long offset, address; unsigned length, opFlags;
             unsigned long long data; unsigned short index, personality; int spliceIn; unsigned long long pad[2]; };
struct cqe { unsigned long long data; int result; unsigned flags; };
struct params { unsigned sqEntries, cqEntries, flags, cpu, idle, features, wq, reserved[3];
                unsigned sqOff[10]; unsigned cqOff[10]; };

int main(void) {
  say("nanosleep a second of nanoseconds", call(SYS_nanosleep, (long)&tooMany, 0, 0, 0, 0, 0));
  say("nanosleep negative", call(SYS_nanosleep, (long)&negative, 0, 0, 0, 0, 0));
  say("nanosleep negative nanoseconds", call(SYS_nanosleep, (long)&below, 0, 0, 0, 0, 0));
  say("nanosleep nothing", call(SYS_nanosleep, (long)&zero, 0, 0, 0, 0, 0));

  say("clock_nanosleep a second of nanoseconds", call(SYS_clock_nanosleep, CLOCK_MONOTONIC, 0, (long)&tooMany, 0, 0, 0));
  say("clock_nanosleep negative", call(SYS_clock_nanosleep, CLOCK_MONOTONIC, 0, (long)&negative, 0, 0, 0));
  say("clock_nanosleep until negative", call(SYS_clock_nanosleep, CLOCK_MONOTONIC, TIMER_ABSTIME, (long)&negative, 0, 0, 0));
  say("clock_nanosleep until a second of nanoseconds",
      call(SYS_clock_nanosleep, CLOCK_REALTIME, TIMER_ABSTIME, (long)&tooMany, 0, 0, 0));
  say("clock_nanosleep nothing", call(SYS_clock_nanosleep, CLOCK_MONOTONIC, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep until the start", call(SYS_clock_nanosleep, CLOCK_MONOTONIC, TIMER_ABSTIME, (long)&zero, 0, 0, 0));
  say("clock_nanosleep no clock", call(SYS_clock_nanosleep, 100, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep no clock negative", call(SYS_clock_nanosleep, 100, 0, (long)&negative, 0, 0, 0));
  say("clock_nanosleep thread clock", call(SYS_clock_nanosleep, CLOCK_THREAD_CPUTIME_ID, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep coarse clock", call(SYS_clock_nanosleep, CLOCK_MONOTONIC_COARSE, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep clock 10", call(SYS_clock_nanosleep, 10, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep thread clock negative", call(SYS_clock_nanosleep, CLOCK_THREAD_CPUTIME_ID, 0, (long)&negative, 0, 0, 0));
  say("clock_nanosleep process clock", call(SYS_clock_nanosleep, CLOCK_PROCESS_CPUTIME_ID, 0, (long)&zero, 0, 0, 0));
  say("clock_nanosleep raw clock", call(SYS_clock_nanosleep, CLOCK_MONOTONIC_RAW, 0, (long)&zero, 0, 0, 0));

  unsigned long usr1 = 1UL << (SIGUSR1 - 1);
  call(SYS_rt_sigprocmask, SIG_BLOCK, (long)&usr1, 0, 8, 0, 0);
  say("sigtimedwait a second of nanoseconds", call(SYS_rt_sigtimedwait, (long)&usr1, 0, (long)&tooMany, 8, 0, 0));
  say("sigtimedwait nothing", call(SYS_rt_sigtimedwait, (long)&usr1, 0, (long)&zero, 8, 0, 0));
  call(SYS_kill, call(SYS_getpid, 0, 0, 0, 0, 0, 0), SIGUSR1, 0, 0, 0, 0);
  say("sigtimedwait pending negative", call(SYS_rt_sigtimedwait, (long)&usr1, 0, (long)&negative, 8, 0, 0));
  say("sigtimedwait pending nothing", call(SYS_rt_sigtimedwait, (long)&usr1, 0, (long)&zero, 8, 0, 0) == SIGUSR1);

  struct { long value; int signal, notify; int thread; char pad[64]; } event = {0, 0, SIGEV_NONE};
  int timer = -1;
  say("timer_create", call(SYS_timer_create, CLOCK_MONOTONIC, (long)&event, (long)&timer, 0, 0, 0));
  struct pair value = {zero, tooMany}, interval = {negative, zero}, nothing = {zero, zero};
  say("timer_settime a second of nanoseconds", call(SYS_timer_settime, timer, 0, (long)&value, 0, 0, 0));
  say("timer_settime negative interval", call(SYS_timer_settime, timer, 0, (long)&interval, 0, 0, 0));
  say("timer_settime no timer", call(SYS_timer_settime, timer + 100, 0, (long)&value, 0, 0, 0));
  say("timer_settime nothing", call(SYS_timer_settime, timer, 0, (long)&nothing, 0, 0, 0));

  int timerfd = (int)call(SYS_timerfd_create, CLOCK_MONOTONIC, 0, 0, 0, 0, 0);
  say("timerfd_settime a second of nanoseconds", call(SYS_timerfd_settime, timerfd, 0, (long)&value, 0, 0, 0));
  say("timerfd_settime negative interval", call(SYS_timerfd_settime, timerfd, 0, (long)&interval, 0, 0, 0));
  say("timerfd_settime no descriptor", call(SYS_timerfd_settime, 999, 0, (long)&value, 0, 0, 0));
  say("timerfd_settime nothing", call(SYS_timerfd_settime, timerfd, 0, (long)&nothing, 0, 0, 0));

  struct pair microseconds = {zero, {0, 1000000}};
  say("setitimer a second of microseconds", call(SYS_setitimer, ITIMER_REAL, (long)&microseconds, 0, 0, 0, 0));
  say("setitimer negative interval", call(SYS_setitimer, ITIMER_REAL, (long)&interval, 0, 0, 0, 0));
  say("setitimer nothing", call(SYS_setitimer, ITIMER_REAL, (long)&nothing, 0, 0, 0, 0));

  say("ppoll a second of nanoseconds", call(SYS_ppoll, 0, 0, (long)&tooMany, 0, 8, 0));
  say("ppoll negative", call(SYS_ppoll, 0, 0, (long)&negative, 0, 8, 0));
  say("ppoll nothing", call(SYS_ppoll, 0, 0, (long)&zero, 0, 8, 0));
  say("pselect6 a second of nanoseconds", call(SYS_pselect6, 0, 0, 0, 0, (long)&tooMany, 0));
  say("pselect6 negative", call(SYS_pselect6, 0, 0, 0, 0, (long)&negative, 0));
  say("pselect6 nothing", call(SYS_pselect6, 0, 0, 0, 0, (long)&zero, 0));
  int epoll = (int)call(SYS_epoll_create1, 0, 0, 0, 0, 0, 0);
  struct { unsigned events; unsigned long long data; } __attribute__((packed)) events[1];
  say("epoll_pwait2 a second of nanoseconds", call(SYS_epoll_pwait2, epoll, (long)events, 1, (long)&tooMany, 0, 8));
  say("epoll_pwait2 nothing", call(SYS_epoll_pwait2, epoll, (long)events, 1, (long)&zero, 0, 8));

  int word = 0;
  say("futex a second of nanoseconds", call(SYS_futex, (long)&word, FUTEX_WAIT_PRIVATE, 0, (long)&tooMany, 0, 0));
  say("futex other negative", call(SYS_futex, (long)&word, FUTEX_WAIT_PRIVATE, 1, (long)&negative, 0, 0));
  say("futex nothing", call(SYS_futex, (long)&word, FUTEX_WAIT_PRIVATE, 0, (long)&zero, 0, 0));

  int set = (int)call(SYS_semget, IPC_PRIVATE, 1, 0600, 0, 0, 0);
  struct { unsigned short number; short change, flags; } zeroWait = {0, 0, 0}, take = {0, -1, 0};
  say("semtimedop a second of nanoseconds", call(SYS_semtimedop, set, (long)&zeroWait, 1, (long)&tooMany, 0, 0));
  say("semtimedop nothing", call(SYS_semtimedop, set, (long)&zeroWait, 1, (long)&zero, 0, 0));
  say("semtimedop waits for nothing", call(SYS_semtimedop, set, (long)&take, 1, (long)&zero, 0, 0));
  call(SYS_semctl, set, 0, IPC_RMID, 0, 0, 0);

  struct { long flags, capacity, size, count, pad[4]; } wanted = {0, 1, 8, 0};
  call(SYS_mq_unlink, (long)"bap-timespec", 0, 0, 0, 0, 0);
  int queue = (int)call(SYS_mq_open, (long)"bap-timespec", O_RDWR | O_CREAT | O_EXCL, 0600, (long)&wanted, 0, 0);
  char message[8] = "message";
  say("mq_timedreceive empty negative", call(SYS_mq_timedreceive, queue, (long)message, 8, 0, (long)&negative, 0));
  say("mq_timedreceive empty nothing", call(SYS_mq_timedreceive, queue, (long)message, 8, 0, (long)&zero, 0));
  say("mq_timedsend room negative", call(SYS_mq_timedsend, queue, (long)message, 8, 0, (long)&negative, 0));
  say("mq_timedsend room nothing", call(SYS_mq_timedsend, queue, (long)message, 8, 0, (long)&zero, 0));
  say("mq_timedsend full a second of nanoseconds", call(SYS_mq_timedsend, queue, (long)message, 8, 0, (long)&tooMany, 0));
  say("mq_timedsend full nothing", call(SYS_mq_timedsend, queue, (long)message, 8, 0, (long)&zero, 0));
  say("mq_timedreceive one negative", call(SYS_mq_timedreceive, queue, (long)message, 8, 0, (long)&negative, 0));
  call(SYS_mq_unlink, (long)"bap-timespec", 0, 0, 0, 0, 0);

  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp", 0777, 0, 0, 0);
  int file = (int)call(SYS_openat, AT_FDCWD, (long)"/tmp/timespec-file", O_RDWR | O_CREAT | O_TRUNC, 0644, 0, 0);
  struct span times[2] = {{0, 1000000000}, {0, UTIME_OMIT}};
  say("utimensat a second of nanoseconds", call(SYS_utimensat, file, 0, (long)times, 0, 0, 0));
  times[0].fraction = -1;
  say("utimensat negative nanoseconds", call(SYS_utimensat, file, 0, (long)times, 0, 0, 0));
  times[0].fraction = UTIME_NOW;
  say("utimensat now", call(SYS_utimensat, file, 0, (long)times, 0, 0, 0));
  times[0] = zero;
  say("utimensat nothing", call(SYS_utimensat, file, 0, (long)times, 0, 0, 0));
  call(SYS_unlinkat, AT_FDCWD, (long)"/tmp/timespec-file", 0, 0, 0, 0);

  struct params given = {0};
  int ring = (int)call(SYS_io_uring_setup, 4, (long)&given, 0, 0, 0, 0);
  char *sq = mmap(0, given.sqOff[6] + given.sqEntries * 4, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, 0);
  char *cq = mmap(0, given.cqOff[5] + given.cqEntries * sizeof(struct cqe), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring,
                  0x8000000);
  struct sqe *entries = mmap(0, given.sqEntries * sizeof(struct sqe), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring,
                             0x10000000);
  unsigned *sqTail = (unsigned *)(sq + given.sqOff[1]), *sqArray = (unsigned *)(sq + given.sqOff[6]);
  unsigned *cqHead = (unsigned *)(cq + given.cqOff[0]), *cqTail = (unsigned *)(cq + given.cqOff[1]);
  struct cqe *completions = (struct cqe *)(cq + given.cqOff[5]);
  unsigned cqMask = *(unsigned *)(cq + given.cqOff[2]);
  struct { long long seconds, fraction; } spans[3] = {{-1, 0}, {0, -1}, {0, 0}};
  const char *labels[3] = {"io_uring timeout negative", "io_uring timeout negative nanoseconds", "io_uring timeout nothing"};
  for (unsigned index = 0; index < 3; index++) {
    struct sqe *entry = &entries[index];
    char *bytes = (char *)entry;
    for (unsigned at = 0; at < sizeof *entry; at++) bytes[at] = 0;
    entry->opcode = 11;
    entry->fd = -1;
    entry->address = (unsigned long long)(unsigned long)&spans[index];
    entry->length = 1;
    sqArray[index] = index;
    __atomic_store_n(sqTail, index + 1, __ATOMIC_RELEASE);
    call(SYS_io_uring_enter, ring, 1, 1, 1, 0, 0);
    unsigned head = *cqHead;
    say(labels[index], head == __atomic_load_n(cqTail, __ATOMIC_ACQUIRE) ? 1 : completions[head & cqMask].result);
    __atomic_store_n(cqHead, head + 1, __ATOMIC_RELEASE);
  }
  return 0;
}
