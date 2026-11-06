// Asynchronous I/O: AIO's reads and writes at offsets, with events that io_getevents takes and waits for, and an io_uring whose rings
// the program drives itself: reads and writes, a nop, a chain that a failure cancels, a read of a pipe that waits for what is written,
// which completes when it is written without another io_uring_enter, as the ring's descriptor and an eventfd that was registered say,
// reads and writes at an offset of what has none, a pipe and a socket, a write to a pipe that nothing reads, which raises SIGPIPE,
// a timeout, a cancel, and a probe. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/syscall.h>
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

static long call(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

struct iocb_ { unsigned long long data; unsigned key, flags; unsigned short opcode; short priority; unsigned fd;
               unsigned long long buffer, size; long long offset; unsigned long long reserved; unsigned more, resfd; };
struct event_ { unsigned long long data, object; long long result, result2; };

struct sqe { unsigned char opcode, flags; unsigned short priority; int fd; unsigned long long offset, address; unsigned length, opFlags;
             unsigned long long data; unsigned short index, personality; int spliceIn; unsigned long long pad[2]; };
struct cqe { unsigned long long data; int result; unsigned flags; };
struct params { unsigned sqEntries, cqEntries, flags, cpu, idle, features, wq, reserved[3];
                unsigned sqOff[10]; unsigned cqOff[10]; };

static unsigned *sqHead, *sqTail, *sqMask, *sqArray, *cqHead, *cqTail, *cqMask;
static struct sqe *entries;
static struct cqe *completions;
static int ring;

static void submit(unsigned char opcode, int fd, unsigned long long offset, void *address, unsigned length, unsigned flags,
                   unsigned long long data, unsigned char entryFlags) {
  unsigned tail = *sqTail;
  unsigned slot = tail & *sqMask;
  struct sqe *entry = &entries[slot];
  char *bytes = (char *)entry;
  for (unsigned index = 0; index < sizeof *entry; index++) bytes[index] = 0;
  entry->opcode = opcode;
  entry->flags = entryFlags;
  entry->fd = fd;
  entry->offset = offset;
  entry->address = (unsigned long long)(unsigned long)address;
  entry->length = length;
  entry->opFlags = flags;
  entry->data = data;
  sqArray[slot] = slot;
  __atomic_store_n(sqTail, tail + 1, __ATOMIC_RELEASE);
}

static long enter(unsigned count, unsigned wait) {
  return call(SYS_io_uring_enter, ring, count, wait, wait ? 1 : 0, 0, 0);
}

// How many completions there are to take.
static long ready(void) { return (long)(__atomic_load_n(cqTail, __ATOMIC_ACQUIRE) - *cqHead); }

// What poll says of the ring's descriptor, at once: whether it is ready to read, and what it has.
static void polled(const char *label) {
  struct { int fd; short events, revents; } watched = {ring, 1, 0};
  struct timespec now = {0, 0};
  long found = call(SYS_ppoll, (long)&watched, 1, (long)&now, 0, 8, 0);
  say(label, 2, found, watched.revents, 0);
}

static volatile int pipeSignals;
static void onPipe(int number) { pipeSignals += number == SIGPIPE; }

// What completed, in order.
static void reap(const char *label) {
  unsigned head = *cqHead;
  while (head != __atomic_load_n(cqTail, __ATOMIC_ACQUIRE)) {
    struct cqe *done = &completions[head & *cqMask];
    say(label, 2, (long)done->data, done->result, 0);
    head++;
  }
  __atomic_store_n(cqHead, head, __ATOMIC_RELEASE);
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "ring.d", 0700, 0, 0, 0);
  int file = open("ring.d/file", O_RDWR | O_CREAT | O_TRUNC, 0600);
  write(file, "0123456789", 10);

  // AIO.
  unsigned long context = 0;
  say("io_setup", 2, call(SYS_io_setup, 4, (long)&context, 0, 0, 0, 0), context != 0, 0);
  unsigned long other = 1;
  say("io_setup again", 1, call(SYS_io_setup, 4, (long)&other, 0, 0, 0, 0), 0, 0);
  char got[8] = {0};
  struct iocb_ reading = {77, 0, 0, 0, 0, (unsigned)file, (unsigned long)got, 4, 3, 0, 0, 0};
  struct iocb_ writing = {78, 0, 0, 1, 0, (unsigned)file, (unsigned long)"AB", 2, 0, 0, 0, 0};
  struct iocb_ *list[2] = {&reading, &writing};
  say("io_submit", 1, call(SYS_io_submit, context, 2, (long)list, 0, 0, 0), 0, 0);
  struct event_ events[4];
  long count = call(SYS_io_getevents, context, 2, 4, (long)events, 0, 0);
  say("io_getevents", 1, count, 0, 0);
  for (long index = 0; index < count; index++) say("event", 3, (long)events[index].data, (long)events[index].result,
                                                    events[index].object == (unsigned long)list[index]);
  sayText("read", got, 4);
  struct timespec soon = {0, 10000000};
  say("nothing", 1, call(SYS_io_getevents, context, 1, 4, (long)events, (long)&soon, 0), 0, 0);
  say("io_destroy", 2, call(SYS_io_destroy, context, 0, 0, 0, 0, 0), call(SYS_io_submit, context, 1, (long)list, 0, 0, 0), 0);

  // io_uring.
  struct params given = {0};
  ring = (int)call(SYS_io_uring_setup, 4, (long)&given, 0, 0, 0, 0);
  say("io_uring_setup", 3, ring >= 0, given.sqEntries, given.cqEntries);
  char *sq = mmap(0, given.sqOff[6] + given.sqEntries * 4, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, 0);
  char *cq = mmap(0, given.cqOff[5] + given.cqEntries * sizeof(struct cqe), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring,
                  0x8000000);
  entries = mmap(0, given.sqEntries * sizeof(struct sqe), PROT_READ | PROT_WRITE, MAP_SHARED | MAP_POPULATE, ring, 0x10000000);
  say("mapped", 3, sq != MAP_FAILED, cq != MAP_FAILED, entries != MAP_FAILED);
  sqHead = (unsigned *)(sq + given.sqOff[0]);
  sqTail = (unsigned *)(sq + given.sqOff[1]);
  sqMask = (unsigned *)(sq + given.sqOff[2]);
  sqArray = (unsigned *)(sq + given.sqOff[6]);
  cqHead = (unsigned *)(cq + given.cqOff[0]);
  cqTail = (unsigned *)(cq + given.cqOff[1]);
  cqMask = (unsigned *)(cq + given.cqOff[2]);
  completions = (struct cqe *)(cq + given.cqOff[5]);
  say("rings", 3, *sqMask, *(unsigned *)(sq + given.sqOff[3]), *cqMask);

  char buffer[16] = {0};
  submit(0, -1, 0, 0, 0, 0, 1, 0);
  submit(22, file, 0, buffer, 6, 0, 2, 0);
  submit(23, file, 8, "yz", 2, 0, 3, 0);
  say("enter", 1, enter(3, 3), 0, 0);
  reap("done");
  sayText("uring read", buffer, 6);
  char whole[16] = {0};
  pread(file, whole, 10, 0);
  sayText("file", whole, 10);

  // A chain that a failure ends.
  submit(22, 99, 0, buffer, 1, 0, 4, 4);
  submit(0, -1, 0, 0, 0, 0, 5, 4);
  submit(0, -1, 0, 0, 0, 0, 6, 0);
  say("chain", 1, enter(3, 3), 0, 0);
  reap("chain");

  // A read of a pipe that waits, a timeout, and what cancels.
  int pipes[2];
  pipe(pipes);
  char piped[8] = {0};
  submit(22, pipes[0], (unsigned long long)-1, piped, 8, 0, 7, 0);
  say("pending", 1, enter(1, 0), 0, 0);
  reap("not yet");
  write(pipes[1], "pipe", 4);
  say("written", 1, enter(0, 1), 0, 0);
  reap("piped");
  sayText("piped", piped, 4);

  // What completes as it can, without io_uring_enter: the ring's descriptor is ready to read while its ring of completions has
  // some, and an eventfd that was registered counts them.
  int counter = (int)call(SYS_eventfd2, 0, O_NONBLOCK, 0, 0, 0, 0);
  say("register eventfd", 1, call(SYS_io_uring_register, ring, 4, (long)&counter, 1, 0, 0), 0, 0);
  unsigned long long counted = 0;
  polled("ring empty");
  submit(22, pipes[0], (unsigned long long)-1, piped, 8, 0, 11, 0);
  say("submitted", 2, enter(1, 0), ready(), 0);
  polled("ring still empty");
  say("count before", 1, call(SYS_read, counter, (long)&counted, 8, 0, 0, 0), 0, 0);
  write(pipes[1], "late", 4);
  say("completed", 1, ready(), 0, 0);
  polled("ring ready");
  say("count", 2, call(SYS_read, counter, (long)&counted, 8, 0, 0, 0), (long)counted, 0);
  reap("late");
  sayText("late", piped, 4);
  polled("ring taken");
  say("unregister eventfd", 1, call(SYS_io_uring_register, ring, 5, 0, 0, 0, 0), 0, 0);
  close(counter);

  // At an offset of what has none: of 0, as at none.
  char some[8] = {0};
  submit(23, pipes[1], 0, "zero", 4, 0, 12, 4);
  submit(22, pipes[0], 0, some, 8, 0, 13, 0);
  say("pipe at 0", 1, enter(2, 2), 0, 0);
  reap("pipe at 0");
  sayText("pipe at 0", some, 4);
  struct { void *base; unsigned long size; } piece = {some, 8};
  write(pipes[1], "vect", 4);
  submit(1, pipes[0], 0, &piece, 1, 0, 14, 0);
  say("readv at 0", 1, enter(1, 1), 0, 0);
  reap("readv at 0");
  sayText("readv at 0", some, 4);
  int pair[2];
  say("socketpair", 1, call(SYS_socketpair, 1, 1, 0, (long)pair, 0, 0), 0, 0);
  write(pair[1], "sock", 4);
  submit(22, pair[0], 0, some, 8, 0, 15, 0);
  say("socket at 0", 1, enter(1, 1), 0, 0);
  reap("socket at 0");
  sayText("socket at 0", some, 4);
  // Of another offset, a pipe the same, and a socket ESPIPE.
  submit(23, pipes[1], 5, "five", 4, 0, 16, 4);
  submit(22, pipes[0], 5, some, 8, 0, 17, 0);
  say("pipe at 5", 1, enter(2, 2), 0, 0);
  reap("pipe at 5");
  sayText("pipe at 5", some, 4);
  submit(23, pair[1], 5, "five", 4, 0, 18, 0);
  say("socket at 5", 1, enter(1, 1), 0, 0);
  submit(22, pair[0], 5, some, 8, 0, 19, 0);
  say("socket at 5", 1, enter(1, 1), 0, 0);
  reap("socket at 5");
  close(pair[0]);
  close(pair[1]);

  // A write to a pipe that nothing reads: EPIPE, and SIGPIPE, as of write.
  signal(SIGPIPE, onPipe);
  int broken[2];
  pipe(broken);
  close(broken[0]);
  submit(23, broken[1], (unsigned long long)-1, "x", 1, 0, 20, 0);
  submit(23, broken[1], 0, "x", 1, 0, 21, 0);
  say("broken", 1, enter(2, 2), 0, 0);
  reap("broken");
  say("sigpipe", 1, pipeSignals, 0, 0);
  signal(SIGPIPE, SIG_DFL);
  close(broken[1]);
  struct { long long seconds, nanoseconds; } span = {0, 10000000};
  submit(11, -1, 0, &span, 1, 0, 8, 0);
  say("timeout", 1, enter(1, 1), 0, 0);
  reap("timed");
  submit(22, pipes[0], (unsigned long long)-1, piped, 8, 0, 9, 0);
  enter(1, 0);
  submit(14, -1, 0, (void *)9, 0, 0, 10, 0);
  say("cancel", 1, enter(1, 2), 0, 0);
  reap("cancelled");

  // What there is.
  struct { unsigned char last, length; unsigned short reserved; unsigned more[3];
           struct { unsigned char op, reserved; unsigned short flags; unsigned more; } ops[24]; } probe = {0};
  say("probe", 1, call(SYS_io_uring_register, ring, 8, (long)&probe, 24, 0, 0), 0, 0);
  say("supported", 3, probe.ops[22].flags & 1, probe.ops[23].flags & 1, probe.ops[11].flags & 1);
  say("bad register", 1, call(SYS_io_uring_register, ring, 999, 0, 0, 0, 0), 0, 0);
  struct params wrong = {0};
  say("no entries", 1, call(SYS_io_uring_setup, 0, (long)&wrong, 0, 0, 0, 0), 0, 0);
  unlink("ring.d/file");
  syscall(SYS_unlinkat, AT_FDCWD, "ring.d", AT_REMOVEDIR, 0, 0, 0);
  return 0;
}
