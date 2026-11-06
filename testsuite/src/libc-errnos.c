// Small things that Linux refuses or does in its own way: dup3 of flags it doesn't know, mmap of a directory, clocks that there
// aren't, getsockopt with less room than the option has, and a private mapping of a file that is written while it has pages it
// hasn't written itself. It says what it found, the same on each target, and uses only a directory of its own.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

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

#define DIR "errnos-dir"
#define PAGE 4096

// A clock of the CPU time of a process or a thread, as Linux numbers them, and what is none of them.
static long cpuClock(long pid, int thread, int which) { return (~pid << 3) | (thread ? 4 : 0) | which; }

static long gettime(long clock) {
  struct timespec now;
  return result(syscall(SYS_clock_gettime, clock, &now));
}

static long getres(long clock) {
  struct timespec now;
  return result(syscall(SYS_clock_getres, clock, &now));
}

static void dups(void) {
  int fd = open(DIR "/a", O_RDWR | O_CREAT, 0600);
  int spare = syscall(SYS_dup, fd);
  say("dup3 O_NONBLOCK", 1, result(syscall(SYS_dup3, fd, spare, O_NONBLOCK)), 0, 0);
  say("dup3 unknown flag", 1, result(syscall(SYS_dup3, fd, spare, 1)), 0, 0);
  say("dup3 same", 1, result(syscall(SYS_dup3, fd, fd, O_CLOEXEC)), 0, 0);
  say("dup3 same no flags", 1, result(syscall(SYS_dup3, fd, fd, 0)), 0, 0);
  say("dup3 O_CLOEXEC", 1, result(syscall(SYS_dup3, fd, spare, O_CLOEXEC)) == spare, 0, 0);
  say("dup3 cloexec set", 1, fcntl(spare, F_GETFD), 0, 0);
  close(spare);
  close(fd);
}

static void directoryMap(void) {
  int fd = open(DIR, O_RDONLY | O_DIRECTORY);
  void *private = mmap(0, PAGE, PROT_READ, MAP_PRIVATE, fd, 0);
  say("mmap directory private", 1, private == MAP_FAILED ? -errno : 0, 0, 0);
  void *shared = mmap(0, PAGE, PROT_READ, MAP_SHARED, fd, 0);
  say("mmap directory shared", 1, shared == MAP_FAILED ? -errno : 0, 0, 0);
  close(fd);
}

static void clocks(void) {
  static const long known[] = {0, 1, 2, 3, 4, 5, 6, 7, 11};
  int fine = 1;
  for (size_t index = 0; index < sizeof known / sizeof known[0]; index++)
    fine = fine && gettime(known[index]) == 0 && getres(known[index]) == 0;
  say("clocks known", 1, fine, 0, 0);
  say("clock 10", 2, gettime(10), getres(10), 0);
  say("clock 12", 2, gettime(12), getres(12), 0);
  say("clock big", 2, gettime(0x7fffffff), getres(0x7fffffff), 0);
  say("clock -1", 2, gettime(-1), getres(-1), 0);
  say("clock self process", 2, gettime(cpuClock(0, 0, 2)), getres(cpuClock(0, 0, 0)), 0);
  say("clock self thread", 2, gettime(cpuClock(0, 1, 2)), getres(cpuClock(0, 1, 1)), 0);
  say("clock own pid", 2, gettime(cpuClock(getpid(), 0, 2)), getres(cpuClock(getpid(), 0, 2)), 0);
  say("clock own tid", 2, gettime(cpuClock(syscall(SYS_gettid), 1, 2)), getres(cpuClock(syscall(SYS_gettid), 1, 2)), 0);
  say("clock which 3", 2, gettime(cpuClock(getpid(), 1, 3)), getres(cpuClock(0, 1, 3)), 0);
  // What is no CPU clock is of a descriptor, which a file isn't.
  int fd = open(DIR "/a", O_RDONLY);
  say("clock of a file", 2, gettime(cpuClock(fd, 0, 3)), getres(cpuClock(fd, 0, 3)), 0);
  close(fd);
  int ready[2];
  pipe(ready);
  pid_t child = fork();
  if (child == 0) {
    char byte;
    read(ready[0], &byte, 1);
    _exit(0);
  }
  say("clock child process", 2, gettime(cpuClock(child, 0, 2)), getres(cpuClock(child, 0, 2)), 0);
  say("clock child thread", 2, gettime(cpuClock(child, 1, 2)), getres(cpuClock(child, 1, 2)), 0);
  write(ready[1], "x", 1);
  int status;
  waitpid(child, &status, 0);
  close(ready[0]);
  close(ready[1]);
  say("clock gone process", 2, gettime(cpuClock(child, 0, 2)), getres(cpuClock(child, 0, 2)), 0);
}

static void options(void) {
  int pair[2];
  syscall(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, pair);
  unsigned char buffer[64];
  socklen_t length = 2;
  memset(buffer, 0x55, sizeof buffer);
  long got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_TYPE, buffer, &length));
  say("SO_TYPE in 2", 3, got, length, buffer[0] + buffer[1] + buffer[2] + buffer[3]);
  length = 0;
  memset(buffer, 0x55, sizeof buffer);
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_TYPE, buffer, &length));
  say("SO_TYPE in 0", 3, got, length, buffer[0]);
  length = 64;
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_TYPE, buffer, &length));
  say("SO_TYPE in 64", 3, got, length, buffer[0] + buffer[1] + buffer[2] + buffer[3]);
  length = (socklen_t)-1;
  say("SO_TYPE in -1", 2, result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_TYPE, buffer, &length)), (int)length, 0);
  length = (socklen_t)-1;
  say("unknown in -1", 2, result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, 9999, buffer, &length)), (int)length, 0);
  length = 64;
  memset(buffer, 0x55, sizeof buffer);
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_LINGER, buffer, &length));
  say("SO_LINGER in 64", 3, got, length, buffer[8]);
  length = 6;
  memset(buffer, 0x55, sizeof buffer);
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_LINGER, buffer, &length));
  say("SO_LINGER in 6", 3, got, length, buffer[6]);
  length = 64;
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_RCVTIMEO, buffer, &length));
  say("SO_RCVTIMEO in 64", 2, got, length == 2 * sizeof(long), 0);
  length = 64;
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_SNDTIMEO, buffer, &length));
  say("SO_SNDTIMEO in 64", 2, got, length == 2 * sizeof(long), 0);
  length = 3;
  memset(buffer, 0x55, sizeof buffer);
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_RCVTIMEO, buffer, &length));
  say("SO_RCVTIMEO in 3", 3, got, length, buffer[3]);
  length = 64;
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_PEERCRED, buffer, &length));
  say("SO_PEERCRED in 64", 2, got, length, 0);
  length = 4;
  memset(buffer, 0x55, sizeof buffer);
  got = result(syscall(SYS_getsockopt, pair[0], SOL_SOCKET, SO_PEERCRED, buffer, &length));
  say("SO_PEERCRED in 4", 3, got, length, buffer[4]);
  close(pair[0]);
  close(pair[1]);
}

static void privateMap(void) {
  int fd = open(DIR "/map", O_RDWR | O_CREAT | O_TRUNC, 0600);
  char page[PAGE];
  memset(page, 'a', PAGE);
  write(fd, page, PAGE);
  memset(page, 'b', PAGE);
  write(fd, page, PAGE);
  memset(page, 'c', PAGE);
  write(fd, page, PAGE);
  volatile char *map = mmap(0, 3 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
  // The first page is written, the second only read, and the third neither.
  map[0] = 'x';
  say("read second", 1, map[PAGE], 0, 0);
  pwrite(fd, "AAAA", 4, 100);
  pwrite(fd, "BBBB", 4, PAGE + 100);
  pwrite(fd, "CCCC", 4, 2 * PAGE + 100);
  say("written page", 2, map[0], map[100], 0);
  say("read page", 2, map[PAGE], map[PAGE + 100], 0);
  say("untouched page", 2, map[2 * PAGE], map[2 * PAGE + 100], 0);
  // A shared mapping of the same file writes it too.
  volatile char *shared = mmap(0, 3 * PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  shared[PAGE + 200] = 'S';
  shared[200] = 'T';
  getppid();
  say("shared to read page", 1, map[PAGE + 200], 0, 0);
  say("shared to written page", 1, map[200], 0, 0);
  // Once written, a page is the process's own.
  map[PAGE + 1] = 'y';
  pwrite(fd, "DDDD", 4, PAGE + 300);
  say("page written later", 2, map[PAGE + 300], map[PAGE + 1], 0);
  munmap((void *)shared, 3 * PAGE);
  munmap((void *)map, 3 * PAGE);
  close(fd);
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, DIR, 0700);
  dups();
  directoryMap();
  clocks();
  options();
  privateMap();
  unlink(DIR "/a");
  unlink(DIR "/map");
  syscall(SYS_unlinkat, AT_FDCWD, DIR, AT_REMOVEDIR);
  say("done", 0, 0, 0, 0);
  return 0;
}
