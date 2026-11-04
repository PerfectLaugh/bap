// Locks of files: fcntl's of a process, which a child sees and is kept from, which merge, split, and go with a close or an end, those of
// an open file, which those of the same process are kept from, flock's, which are apart from them, and locks that wait for another to
// let go. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <time.h>
#include <sys/file.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

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

static long lockOf(int fd, int command, int type, int whence, long start, long length) {
  struct flock lock = {0};
  lock.l_type = type;
  lock.l_whence = whence;
  lock.l_start = start;
  lock.l_len = length;
  return fcntl(fd, command, &lock) < 0 ? -errno : 0;
}

// What F_GETLK says is in the way of a lock: its type, where it starts, how long it is, and whether it is the parent's or no process's.
static void inTheWay(const char *label, int fd, int command, int type, long start, long length) {
  struct flock lock = {0};
  lock.l_type = type;
  lock.l_start = start;
  lock.l_len = length;
  if (fcntl(fd, command, &lock) < 0) { say(label, 1, -errno, 0, 0); return; }
  if (lock.l_type == F_UNLCK) { say(label, 1, F_UNLCK, 0, 0); return; }
  say(label, 3, lock.l_type, (long)lock.l_start, (long)lock.l_len);
  say(label, 2, lock.l_pid == getppid(), lock.l_pid == -1, 0);
}

static long flockOf(int fd, int operation) {
  long result = syscall(SYS_flock, fd, operation, 0, 0, 0, 0);
  return result < 0 ? -errno : result;
}

static void pause_(void) {
  struct timespec pause = {0, 20000000};
  nanosleep(&pause, 0);
}

// A child that runs `body` with the file, which the parent waits for.
static void inChild(void (*body)(int), int fd) {
  int child = fork();
  if (child == 0) { body(fd); _exit(0); }
  waitpid(child, 0, 0);
}

static void sees(int fd) {
  inTheWay("child sees", fd, F_GETLK, F_WRLCK, 5, 10);
  say("child kept", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 5, 10), 0, 0);
  say("child beside", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 10, 10), 0, 0);
  say("child reads", 1, lockOf(fd, F_SETLK, F_RDLCK, SEEK_SET, 50, 5), 0, 0);
}

static void seesMerged(int fd) { inTheWay("merged", fd, F_GETLK, F_WRLCK, 0, 0); }
static void seesSplit(int fd) { inTheWay("split", fd, F_GETLK, F_WRLCK, 0, 10); }
static void seesNone(int fd) { inTheWay("after close", fd, F_GETLK, F_WRLCK, 0, 0); }

static void waits(int fd) {
  say("child waits", 1, lockOf(fd, F_SETLKW, F_WRLCK, SEEK_SET, 0, 1), 0, 0);
  say("child got it", 0, 0, 0, 0);
}

static void waitsFlock(int fd) {
  int own = open("/tmp/lock-file", O_RDWR);
  say("child flock", 1, flockOf(own, LOCK_EX), 0, 0);
  say("child flocked", 0, 0, 0, 0);
  (void)fd;
}

static void holdsAndEnds(int fd) { say("child holds", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 0, 0), 0, 0); }

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777);
  int fd = open("/tmp/lock-file", O_RDWR | O_CREAT | O_TRUNC, 0644);
  write(fd, "0123456789", 10);

  // fcntl's locks of a process.
  say("lock", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 0, 10), 0, 0);
  inTheWay("own", fd, F_GETLK, F_WRLCK, 0, 10);
  inChild(sees, fd);
  say("read locks", 2, lockOf(fd, F_SETLK, F_RDLCK, SEEK_SET, 20, 10), lockOf(fd, F_SETLK, F_RDLCK, SEEK_SET, 30, 10), 0);
  say("unlock", 1, lockOf(fd, F_SETLK, F_UNLCK, SEEK_SET, 0, 10), 0, 0);
  inChild(seesMerged, fd);
  say("relock", 2, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 0, 10), lockOf(fd, F_SETLK, F_UNLCK, SEEK_SET, 0, 5), 0);
  inChild(seesSplit, fd);
  say("from the end", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_END, -2, 0), 0, 0);
  lseek(fd, 3, SEEK_SET);
  say("before here", 1, lockOf(fd, F_SETLK, F_RDLCK, SEEK_CUR, 0, -2), 0, 0);
  int other = open("/tmp/lock-file", O_RDONLY);
  close(other);
  inChild(seesNone, fd);

  // Wrong ones.
  int reading = open("/tmp/lock-file", O_RDONLY);
  say("bad type", 1, lockOf(fd, F_SETLK, 7, SEEK_SET, 0, 1), 0, 0);
  say("bad whence", 1, lockOf(fd, F_SETLK, F_WRLCK, 7, 0, 1), 0, 0);
  say("before start", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, -1, 1), 0, 0);
  say("write unwritable", 1, lockOf(reading, F_SETLK, F_WRLCK, SEEK_SET, 0, 1), 0, 0);
  say("getlk unlock", 1, lockOf(fd, F_GETLK, F_UNLCK, SEEK_SET, 0, 1), 0, 0);
  say("bad descriptor", 1, lockOf(99, F_SETLK, F_WRLCK, SEEK_SET, 0, 1), 0, 0);

  // Locks of an open file, which another of the same process is kept from, as is a lock of the process.
  int second = open("/tmp/lock-file", O_RDWR);
  say("ofd", 1, lockOf(fd, F_OFD_SETLK, F_WRLCK, SEEK_SET, 0, 10), 0, 0);
  say("ofd other", 1, lockOf(second, F_OFD_SETLK, F_WRLCK, SEEK_SET, 5, 1), 0, 0);
  say("ofd same", 1, lockOf(fd, F_OFD_SETLK, F_RDLCK, SEEK_SET, 0, 5), 0, 0);
  say("process kept", 1, lockOf(second, F_SETLK, F_WRLCK, SEEK_SET, 8, 1), 0, 0);
  inTheWay("ofd sees", second, F_OFD_GETLK, F_WRLCK, 0, 0);
  struct flock withPid = {0};
  withPid.l_type = F_WRLCK;
  withPid.l_pid = 1;
  say("ofd pid", 1, fcntl(second, F_OFD_SETLK, &withPid) < 0 ? -errno : 0, 0, 0);
  say("ofd unlock", 2, lockOf(fd, F_OFD_SETLK, F_UNLCK, SEEK_SET, 0, 0), lockOf(second, F_OFD_SETLK, F_WRLCK, SEEK_SET, 0, 1), 0);
  lockOf(second, F_OFD_SETLK, F_UNLCK, SEEK_SET, 0, 0);

  // flock, of all of a file, apart from the others.
  say("flock", 1, flockOf(fd, LOCK_EX), 0, 0);
  say("flock other", 2, flockOf(second, LOCK_EX | LOCK_NB), flockOf(second, LOCK_SH | LOCK_NB), 0);
  say("fcntl beside", 1, lockOf(second, F_SETLK, F_WRLCK, SEEK_SET, 0, 1), 0, 0);
  say("flock shared", 3, flockOf(fd, LOCK_SH), flockOf(second, LOCK_SH | LOCK_NB), flockOf(fd, LOCK_EX | LOCK_NB));
  say("flock unlock", 2, flockOf(fd, LOCK_UN), flockOf(second, LOCK_UN), 0);
  say("flock bad", 1, flockOf(fd, 3), 0, 0);
  lockOf(second, F_SETLK, F_UNLCK, SEEK_SET, 0, 0);

  // Locks that wait for the parent to let go, and one that goes with its process.
  lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 0, 1);
  int child = fork();
  if (child == 0) { waits(fd); _exit(0); }
  pause_();
  say("parent lets go", 0, 0, 0, 0);
  lockOf(fd, F_SETLK, F_UNLCK, SEEK_SET, 0, 1);
  waitpid(child, 0, 0);
  flockOf(fd, LOCK_EX);
  child = fork();
  if (child == 0) { waitsFlock(fd); _exit(0); }
  pause_();
  say("parent unflocks", 0, 0, 0, 0);
  flockOf(fd, LOCK_UN);
  waitpid(child, 0, 0);
  inChild(holdsAndEnds, fd);
  say("after end", 1, lockOf(fd, F_SETLK, F_WRLCK, SEEK_SET, 0, 0), 0, 0);
  unlink("/tmp/lock-file");
  return 0;
}
