// What a file has of itself: times that utimensat sets and a write moves, hard links, renameat2, extended attributes, an owner, the
// devices of /dev, and what /proc says of the process. It says what it found, the same on each target. The libc of the tests has none
// of these calls, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <string.h>
#include <time.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

#ifdef SYS_utimensat_time64
#define UTIMENSAT SYS_utimensat_time64
#else
#define UTIMENSAT SYS_utimensat
#endif

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

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

// statx, whose layout every target has: of a path, or of a descriptor with an empty one.
struct timestamp { long long sec; unsigned nsec; int pad; };
struct statx_ { unsigned mask, blksize; unsigned long long attributes; unsigned nlink, uid, gid; unsigned short mode, pad;
                unsigned long long ino, size, blocks, attributesMask; struct timestamp atime, btime, ctime, mtime; char rest[128]; };

static void statOf(int directory, const char *path, struct statx_ *out) {
  syscall(SYS_statx, directory, path, *path ? 0 : 0x1000, 0x7ff, out);
}

#define AT_FDCWD_ (-100)

#ifdef SYS_getgid32
#define GETGID SYS_getgid32
#else
#define GETGID SYS_getgid
#endif

// Whether `text` has `part` in it.
static int contains(const char *text, const char *part) {
  for (; *text; text++) {
    int index = 0;
    while (part[index] && text[index] == part[index]) index++;
    if (!part[index]) return 1;
  }
  return 0;
}

static long readAll(const char *path, char *buffer, long size) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) return -errno;
  long got = read(fd, buffer, size - 1);
  close(fd);
  if (got >= 0) buffer[got] = 0;
  return got;
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD_, "/tmp", 0777);
  syscall(SYS_mkdirat, AT_FDCWD_, "/tmp/bap-meta", 0777);
  syscall(SYS_chdir, "/tmp/bap-meta");
  int fd = open("a", O_CREAT | O_RDWR | O_TRUNC, 0644);
  write(fd, "one", 3);

  // Times that it is given, and that a write moves.
  struct timespec times[2] = { {1000000000, 5}, {1000000001, 7} };
  say("utimensat", 1, call(UTIMENSAT, AT_FDCWD_, (long)"a", (long)times, 0, 0), 0, 0);
  struct statx_ st;
  statOf(AT_FDCWD_, "a", &st);
  say("its times", 3, st.atime.sec == 1000000000 && st.atime.nsec == 5, st.mtime.sec == 1000000001, st.mtime.nsec == 7);
  write(fd, "two", 3);
  statOf(fd, "", &st);
  say("a write moves it", 1, st.mtime.sec > 1000000001, 0, 0);
  struct timespec omit[2] = { {0, 0x3ffffffeL}, {5, 0} };
  call(UTIMENSAT, fd, 0, (long)omit, 0, 0);
  statOf(fd, "", &st);
  say("UTIME_OMIT", 2, st.atime.sec == 1000000000, st.mtime.sec == 5, 0);

  // A hard link is the same file, which is there after the other path goes.
  say("link", 1, call(SYS_linkat, AT_FDCWD_, (long)"a", AT_FDCWD_, (long)"b", 0), 0, 0);
  struct statx_ other;
  statOf(AT_FDCWD_, "b", &other);
  statOf(AT_FDCWD_, "a", &st);
  say("the same file", 1, st.ino == other.ino, 0, 0);
  syscall(SYS_unlinkat, AT_FDCWD_, "a", 0);
  char buffer[256];
  say("after the other goes", 1, readAll("b", buffer, sizeof buffer), 0, 0);

  // renameat2: not over what is there, and an exchange.
  int c = open("c", O_CREAT | O_WRONLY, 0644);
  write(c, "x", 1);
  close(c);
  say("RENAME_NOREPLACE", 1, call(SYS_renameat2, AT_FDCWD_, (long)"b", AT_FDCWD_, (long)"c", 1), 0, 0);
  say("RENAME_EXCHANGE", 1, call(SYS_renameat2, AT_FDCWD_, (long)"b", AT_FDCWD_, (long)"c", 2), 0, 0);
  say("each has the other", 2, readAll("b", buffer, sizeof buffer), readAll("c", buffer, sizeof buffer), 0);

  // Extended attributes.
  say("setxattr", 1, call(SYS_setxattr, (long)"c", (long)"user.color", (long)"blue", 4, 0), 0, 0);
  say("XATTR_CREATE of one that is there", 1, call(SYS_setxattr, (long)"c", (long)"user.color", (long)"red", 3, 1) == -EEXIST, 0, 0);
  char value[16];
  long size = call(SYS_getxattr, (long)"c", (long)"user.color", (long)value, sizeof value, 0);
  say("getxattr", 3, size, size == 4 && memcmp(value, "blue", 4) == 0, call(SYS_getxattr, (long)"c", (long)"user.color", 0, 0, 0));
  say("too small", 1, call(SYS_getxattr, (long)"c", (long)"user.color", (long)value, 2, 0) == -ERANGE, 0, 0);
  // What a list has besides, as `security.selinux` of a system that has it, isn't said.
  char names[256];
  size = call(SYS_listxattr, (long)"c", (long)names, sizeof names, 0, 0);
  int listed = 0;
  for (long at = 0; at < size; at += strlen(names + at) + 1) if (strcmp(names + at, "user.color") == 0) listed = 1;
  say("listxattr", 1, listed, 0, 0);
  say("removexattr", 2, call(SYS_removexattr, (long)"c", (long)"user.color", 0, 0, 0),
      call(SYS_getxattr, (long)"c", (long)"user.color", 0, 0, 0) == -ENODATA, 0);
  say("of no namespace", 1, call(SYS_setxattr, (long)"c", (long)"color", (long)"x", 1, 0) == -EOPNOTSUPP, 0, 0);

  // An owner that it already is.
  say("fchown", 1, call(SYS_fchown, fd, getuid(), syscall(GETGID), 0, 0), 0, 0);
  close(fd);
  syscall(SYS_unlinkat, AT_FDCWD_, "b", 0);
  syscall(SYS_unlinkat, AT_FDCWD_, "c", 0);
  syscall(SYS_chdir, "/");
  syscall(SYS_unlinkat, AT_FDCWD_, "/tmp/bap-meta", 0x200);

  // Devices.
  int null = open("/dev/null", O_RDWR);
  say("/dev/null", 2, write(null, "abc", 3), read(null, buffer, 8), 0);
  int zero = open("/dev/zero", O_RDONLY);
  memset(buffer, 7, 8);
  say("/dev/zero", 2, read(zero, buffer, 8), buffer[0] == 0 && buffer[7] == 0, 0);
  int full = open("/dev/full", O_WRONLY);
  say("/dev/full", 1, write(full, "a", 1) == -1 && errno == ENOSPC, 0, 0);
  int random = open("/dev/urandom", O_RDONLY);
  say("/dev/urandom", 1, read(random, buffer, 16), 0, 0);

  // What /proc says of it.
  readAll("/proc/self/status", buffer, sizeof buffer);
  char uid[32] = "Uid:\t";
  int n = 5;
  unsigned id = getuid();
  char digits[12];
  int d = 0;
  do { digits[d++] = (char)('0' + id % 10); id /= 10; } while (id);
  while (d) uid[n++] = digits[--d];
  uid[n++] = '\t';
  uid[n] = 0;
  say("/proc/self/status has its uid", 1, contains(buffer, uid), 0, 0);
  int info = open("/proc/self/fdinfo/0", O_RDONLY);
  say("/proc/self/fdinfo", 1, info >= 0, 0, 0);
  return 0;
}
