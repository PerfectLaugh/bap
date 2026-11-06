// How much a pipe holds: 64 KiB at first, which F_GETPIPE_SZ says and F_SETPIPE_SZ changes, a write that doesn't wait taking what
// there is room for, or nothing and EAGAIN, a write of at most PIPE_BUF bytes all of it or nothing, poll saying a pipe is ready to write
// only once a page of it is free, and a writer that waits for the reader to make room, all of what it writes coming through. It says
// what it found, the same on each target. The libc of the tests has no poll, sendfile, splice nor tee, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

#ifndef F_SETPIPE_SZ
#define F_SETPIPE_SZ 1031
#define F_GETPIPE_SZ 1032
#endif
#define SPLICE_F_NONBLOCK 2

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long result(long value) { return value < 0 ? -errno : value; }

static char big[1 << 20];
static char small[8192];

// The bits of POLLOUT that poll gives the end of a pipe that writes, without waiting.
static long writable(int fd) {
  struct pollfd entry = {fd, POLLOUT, 0};
  struct timespec none = {0, 0};
  long count = result(syscall(SYS_ppoll, &entry, 1, &none, 0, 8));
  return count <= 0 ? count : entry.revents & POLLOUT ? 1 : 0;
}

static unsigned char pattern(long at) { return (unsigned char)(at * 7 + at / 251); }

static volatile int pipes, alarms;
static void handler(int number) { pipes += number == SIGPIPE; alarms += number == SIGALRM; }

int main(void) {
  int ends[2];
  pipe(ends);
  say("F_GETPIPE_SZ", 1, result(fcntl(ends[1], F_GETPIPE_SZ)), 0, 0);
  fcntl(ends[1], F_SETFL, O_NONBLOCK);
  say("write of 1 MiB", 1, result(write(ends[1], big, sizeof big)), 0, 0);
  say("write to a full pipe", 1, result(write(ends[1], big, 1)), 0, 0);
  say("POLLOUT of a full pipe", 1, writable(ends[1]), 0, 0);
  say("F_SETPIPE_SZ smaller than what it holds", 1, result(fcntl(ends[1], F_SETPIPE_SZ, 8192)), 0, 0);
  say("read", 1, result(read(ends[0], small, 4000)), 0, 0);
  say("POLLOUT with 4000 bytes free", 1, writable(ends[1]), 0, 0);
  say("write of PIPE_BUF with 4000 bytes free", 1, result(write(ends[1], big, 4096)), 0, 0);
  say("read", 1, result(read(ends[0], small, 96)), 0, 0);
  say("POLLOUT with a page free", 1, writable(ends[1]), 0, 0);
  say("write of 5000 with a page free", 1, result(write(ends[1], big, 5000)), 0, 0);
  say("read", 1, result(read(ends[0], small, 4096)), 0, 0);
  say("write of PIPE_BUF with a page free", 1, result(write(ends[1], big, 4096)), 0, 0);

  // tee to a pipe of one page takes that much.
  int other[2];
  pipe(other);
  say("F_SETPIPE_SZ of 1", 1, result(fcntl(other[1], F_SETPIPE_SZ, 1)), 0, 0);
  say("F_GETPIPE_SZ", 1, result(fcntl(other[0], F_GETPIPE_SZ)), 0, 0);
  say("tee to it", 1, result(syscall(SYS_tee, ends[0], other[1], 100000, SPLICE_F_NONBLOCK)), 0, 0);
  say("tee to it full", 1, result(syscall(SYS_tee, ends[0], other[1], 100000, SPLICE_F_NONBLOCK)), 0, 0);
  close(other[0]);
  close(other[1]);
  close(ends[0]);
  close(ends[1]);

  // A new pipe, made bigger and smaller, and writev to it.
  pipe(ends);
  say("F_SETPIPE_SZ of 8192", 1, result(fcntl(ends[1], F_SETPIPE_SZ, 8192)), 0, 0);
  say("F_SETPIPE_SZ of 5000", 1, result(fcntl(ends[1], F_SETPIPE_SZ, 5000)), 0, 0);
  say("F_SETPIPE_SZ of 65536", 1, result(fcntl(ends[1], F_SETPIPE_SZ, 65536)), 0, 0);
  int devnull = open("/dev/null", O_RDONLY);
  say("F_GETPIPE_SZ of what isn't a pipe", 1, result(fcntl(devnull, F_GETPIPE_SZ)), 0, 0);
  close(devnull);
  fcntl(ends[1], F_SETFL, O_NONBLOCK);
  struct iovec pieces[2] = {{big, 40000}, {big, 40000}};
  say("writev of 80000", 1, result(writev(ends[1], pieces, 2)), 0, 0);
  close(ends[0]);
  close(ends[1]);

  // sendfile and splice from a file take what there is room for.
  syscall(SYS_mkdirat, AT_FDCWD, "pipesize.d", 0700);
  int file = open("pipesize.d/data", O_RDWR | O_CREAT | O_TRUNC, 0600);
  write(file, big, 100000);
  pipe(ends);
  long from = 0;
  say("sendfile of 100000", 1, result(syscall(SYS_sendfile, ends[1], file, &from, 100000)), 0, 0);
  fcntl(ends[1], F_SETFL, O_NONBLOCK);
  say("sendfile to a full pipe", 1, result(syscall(SYS_sendfile, ends[1], file, &from, 100000)), 0, 0);
  read(ends[0], small, 4096);
  long at = 0;
  say("splice with a page free", 1, result(syscall(SYS_splice, file, &at, ends[1], 0, 10000, 0)), 0, 0);
  say("splice to a full pipe", 1, result(syscall(SYS_splice, file, &at, ends[1], 0, 10000, SPLICE_F_NONBLOCK)), 0, 0);
  close(ends[0]);
  close(ends[1]);
  close(file);
  unlink("pipesize.d/data");
  syscall(SYS_unlinkat, AT_FDCWD, "pipesize.d", AT_REMOVEDIR);

  // A writer that waits for room, all of what it writes coming through in order.
  for (long index = 0; index < 200000; index++) big[index] = (char)pattern(index);
  pipe(ends);
  pid_t child = fork();
  if (child == 0) {
    close(ends[0]);
    say("child wrote", 1, result(write(ends[1], big, 200000)), 0, 0);
    _exit(0);
  }
  close(ends[1]);
  long total = 0, same = 1, count;
  while ((count = read(ends[0], small, 4096)) > 0) {
    for (long index = 0; index < count; index++) same &= (unsigned char)small[index] == pattern(total + index);
    total += count;
  }
  int status = 0;
  waitpid(child, &status, 0);
  say("parent read", 2, total, same, 0);
  close(ends[0]);

  // A writer that waits, which a signal ends: what it wrote, whether the handler has the call run again or not.
  pipe(ends);
  struct sigaction action = {0};
  action.sa_handler = handler;
  sigaction(SIGALRM, &action, 0);
  alarm(1);
  say("write that a signal ends", 2, result(write(ends[1], big, 200000)), alarms, 0);
  action.sa_flags = SA_RESTART;
  sigaction(SIGALRM, &action, 0);
  read(ends[0], small, 4096);
  alarm(1);
  say("write that a signal of SA_RESTART ends", 2, result(write(ends[1], big, 200000)), alarms, 0);
  close(ends[0]);
  close(ends[1]);

  // A writer that waits while the reader goes: what it wrote, and SIGPIPE.
  pipe(ends);
  child = fork();
  if (child == 0) {
    close(ends[0]);
    signal(SIGPIPE, handler);
    long wrote = result(write(ends[1], big, 200000));
    say("broken writer", 3, wrote >= 65536, wrote < 200000, pipes);
    _exit(0);
  }
  close(ends[1]);
  read(ends[0], small, 4096);
  close(ends[0]);
  waitpid(child, &status, 0);
  say("broken writer ended", 1, WIFEXITED(status), 0, 0);
  return 0;
}
