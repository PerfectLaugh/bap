// Offsets and sizes of files that are negative, or that a count takes past 2^63, which are EINVAL: pread, pwrite, truncate,
// ftruncate, lseek, and the offsets that sendfile, splice and copy_file_range are given, of which copy_file_range has EOVERFLOW for one
// that the count takes past the end of 64 bits; and a file that grows by a write past its end or by ftruncate, with zeros in what it
// skips. It says what it found, the same on each target. The libc of the tests has none of these calls, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

#ifdef SYS_sendfile64
#define SENDFILE SYS_sendfile64
#else
#define SENDFILE SYS_sendfile
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

// What a call gives, or the error it has, negative.
static long result(long value) { return value < 0 ? -errno : value; }

static long sizeOf(int fd) {
  struct stat st;
  return syscall(SYS_fstat, fd, &st) < 0 ? -errno : (long)st.st_size;
}

int main(void) {
  char buffer[8] = {0};
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777);
  int fd = open("/tmp/offsets-file", O_RDWR | O_CREAT | O_TRUNC, 0644);
  int other = open("/tmp/offsets-other", O_RDWR | O_CREAT | O_TRUNC, 0644);
  say("write", 1, result(write(fd, "abcd", 4)), 0, 0);

  say("pwrite negative", 1, result(syscall(SYS_pwrite64, fd, "z", 1, -1L)), 0, 0);
  say("pwrite most negative", 1, result(syscall(SYS_pwrite64, fd, "z", 1, (long)(1UL << 63))), 0, 0);
  say("pwrite past the end of 63 bits", 1, result(syscall(SYS_pwrite64, fd, "z", 1, 0x7fffffffffffffffL)), 0, 0);
  say("pread negative", 1, result(syscall(SYS_pread64, fd, buffer, 4, -1L)), 0, 0);
  say("pread past the end of 63 bits", 1, result(syscall(SYS_pread64, fd, buffer, 4, 0x7ffffffffffffffeL)), 0, 0);
  say("ftruncate negative", 1, result(syscall(SYS_ftruncate, fd, -1L)), 0, 0);
  say("truncate negative", 1, result(syscall(SYS_truncate, "/tmp/offsets-file", -1L)), 0, 0);
  say("size", 1, sizeOf(fd), 0, 0);

  say("lseek negative", 1, result(syscall(SYS_lseek, fd, -1L, SEEK_SET)), 0, 0);
  say("lseek to 2", 1, result(syscall(SYS_lseek, fd, 2L, SEEK_SET)), 0, 0);
  say("lseek before start", 1, result(syscall(SYS_lseek, fd, -3L, SEEK_CUR)), 0, 0);
  say("lseek before end", 1, result(syscall(SYS_lseek, fd, -5L, SEEK_END)), 0, 0);
  say("lseek stays", 1, result(syscall(SYS_lseek, fd, 0L, SEEK_CUR)), 0, 0);

  long offset = -1;
  say("sendfile negative", 1, result(syscall(SENDFILE, other, fd, &offset, 1L)), 0, 0);
  say("sendfile offset", 1, offset, 0, 0);
  int pipes[2];
  syscall(SYS_pipe2, pipes, 0);
  say("splice negative", 1, result(syscall(SYS_splice, fd, &offset, pipes[1], 0L, 1L, 0)), 0, 0);
  long start = 0;
  say("copy_file_range negative in", 1, result(syscall(SYS_copy_file_range, fd, &offset, other, &start, 1L, 0)), 0, 0);
  say("copy_file_range negative out", 1, result(syscall(SYS_copy_file_range, fd, &start, other, &offset, 1L, 0)), 0, 0);
  offset = -100;
  say("copy_file_range farther in", 1, result(syscall(SYS_copy_file_range, fd, &offset, other, &start, 1L, 0)), 0, 0);
  say("copy_file_range farther out", 1, result(syscall(SYS_copy_file_range, fd, &start, other, &offset, 1L, 0)), 0, 0);
  say("other size", 1, sizeOf(other), 0, 0);

  say("pwrite past end", 1, result(syscall(SYS_pwrite64, fd, "z", 1, 4096L)), 0, 0);
  say("size", 1, sizeOf(fd), 0, 0);
  long read = result(syscall(SYS_pread64, fd, buffer, 8, 4090L));
  say("pread hole", 3, read, buffer[0], buffer[6]);
  say("ftruncate longer", 1, result(syscall(SYS_ftruncate, fd, 10000L)), 0, 0);
  say("size", 1, sizeOf(fd), 0, 0);
  buffer[0] = 1;
  say("pread zeros", 2, result(syscall(SYS_pread64, fd, buffer, 4, 9000L)), buffer[0], 0);
  say("truncate shorter", 1, result(syscall(SYS_truncate, "/tmp/offsets-file", 3L)), 0, 0);
  say("size", 1, sizeOf(fd), 0, 0);

  unlink("/tmp/offsets-file");
  unlink("/tmp/offsets-other");
  return 0;
}
