// fallocate, which grows a file, or keeps its size, or punches a hole of zeros in it, and what it refuses; posix_fadvise, which has
// nothing to do but check what it is given; sync; and preadv and pwritev, at an offset, of a file opened to append, and preadv2 and
// pwritev2 at the offset of the file. It says what it found, the same on each target. The libc of the tests has none of fallocate,
// fadvise, sync, preadv2 and pwritev2, so they are called by number, with what is of 64 bits in two arguments on 32 bits.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <unistd.h>

long syscall(long, ...);

#if __SIZEOF_LONG__ == 8
#define LL(x) (long)(x)
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define LL(x) (long)((long long)(x) >> 32), (long)(x)
#else
#define LL(x) (long)(x), (long)((long long)(x) >> 32)
#endif

static void say(const char *label, long value) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  // An error by its name, as the numbers of some differ between targets.
  const char *name = value == -EBADF ? "EBADF" : value == -EINVAL ? "EINVAL" : value == -ESPIPE ? "ESPIPE"
    : value == -ENODEV ? "ENODEV" : value == -EOPNOTSUPP ? "EOPNOTSUPP" : value == -ENOSYS ? "ENOSYS" : value == -EPERM ? "EPERM"
    : value == -EFBIG ? "EFBIG" : 0;
  if (name) {
    while (*name) line[n++] = *name++;
  } else {
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int digit = 0;
    do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (digit) line[n++] = digits[--digit];
  }
  line[n++] = '\n';
  write(1, line, n);
}

// Bytes of a file, with a dot for each zero.
static void show(const char *label, int fd, long offset, int count) {
  char line[64];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  char bytes[32];
  long got = pread(fd, bytes, count, offset);
  for (long index = 0; index < got; index++) line[n++] = bytes[index] ? bytes[index] : '.';
  line[n++] = '\n';
  write(1, line, n);
}

// What a call gives, or the error it has, negative.
static long result(long value) { return value < 0 ? -errno : value; }

// The size of a file, from where its end is, which leaves its offset.
static long sizeOf(int fd) {
  off_t at = lseek(fd, 0, SEEK_CUR);
  off_t size = lseek(fd, 0, SEEK_END);
  lseek(fd, at, SEEK_SET);
  return size < 0 ? -errno : (long)size;
}

// A descriptor that isn't open, until something is opened next.
static int noDescriptor(void) {
  int fd = open("filealloc-dir", O_RDONLY);
  close(fd);
  return fd;
}

static long allocate(int fd, int mode, long long offset, long long length) {
  return result(syscall(SYS_fallocate, fd, mode, LL(offset), LL(length)));
}

// posix_fadvise as musl calls it: ARM has the advice second, so that the pairs are in registers that line up.
static long advise(int fd, long long offset, long long length, int advice) {
#if defined(__arm__)
  return result(syscall(SYS_arm_fadvise64_64, fd, advice, LL(offset), LL(length)));
#elif __SIZEOF_LONG__ == 4
  return result(syscall(SYS_fadvise64_64, fd, LL(offset), LL(length), advice));
#else
  return result(syscall(SYS_fadvise64, fd, offset, length, advice));
#endif
}

// The offset of preadv2 and pwritev2 is in two words on every target, the low one first, of which 64 bits take the first.
static long readv2(int fd, struct iovec *vectors, int count, long long offset, int flags) {
  return result(syscall(SYS_preadv2, fd, vectors, count, (long)offset, (long)(offset >> 32), flags));
}

static long writev2(int fd, struct iovec *vectors, int count, long long offset, int flags) {
  return result(syscall(SYS_pwritev2, fd, vectors, count, (long)offset, (long)(offset >> 32), flags));
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "filealloc-dir", 0755);
  int fd = open("filealloc-dir/file", O_RDWR | O_CREAT | O_TRUNC, 0644);

  say("fallocate", allocate(fd, 0, 0, 8192));
  say("size", sizeOf(fd));
  say("fallocate keeping the size", allocate(fd, FALLOC_FL_KEEP_SIZE, 0, 20000));
  say("size", sizeOf(fd));
  say("fallocate within", allocate(fd, 0, 100, 10));
  say("size", sizeOf(fd));
  say("fallocate past the end", allocate(fd, 0, 9000, 100));
  say("size", sizeOf(fd));
  pwrite(fd, "abcdefgh", 8, 0);
  say("punch a hole", allocate(fd, FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE, 2, 3));
  show("bytes", fd, 0, 8);
  say("punch a hole past the end", allocate(fd, FALLOC_FL_PUNCH_HOLE | FALLOC_FL_KEEP_SIZE, 9050, 1000));
  say("size", sizeOf(fd));
  say("punch a hole without keeping the size", allocate(fd, FALLOC_FL_PUNCH_HOLE, 0, 1));
  say("unknown mode", allocate(fd, 0x100, 0, 1));
  say("negative offset", allocate(fd, 0, -1, 1));
  say("no length", allocate(fd, 0, 0, 0));
  say("negative length", allocate(fd, 0, 0, -1));
  say("offset", result(lseek(fd, 0, SEEK_CUR)));

  int reader = open("filealloc-dir/file", O_RDONLY);
  say("fallocate of what is open to read", allocate(reader, 0, 0, 1));
  int pipes[2];
  syscall(SYS_pipe2, pipes, 0);
  say("fallocate of a pipe", allocate(pipes[1], 0, 0, 1));
  say("fallocate of what reads a pipe", allocate(pipes[0], 0, 0, 1));
  int pair[2];
  syscall(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, pair);
  say("fallocate of a socket", allocate(pair[0], 0, 0, 1));
  say("fallocate of no descriptor", allocate(noDescriptor(), 0, 0, 1));

  say("fadvise", advise(fd, 0, 100, POSIX_FADV_SEQUENTIAL));
  say("fadvise of all", advise(reader, 0, 0, POSIX_FADV_DONTNEED));
  say("fadvise of a socket", advise(pair[0], 0, 0, POSIX_FADV_NORMAL));
  say("fadvise of no advice", advise(fd, 0, 100, 99));
  say("fadvise of a negative length", advise(fd, 0, -1, POSIX_FADV_NORMAL));
  say("fadvise of a pipe", advise(pipes[0], 0, 0, POSIX_FADV_NORMAL));
  say("fadvise of no descriptor", advise(noDescriptor(), 0, 0, POSIX_FADV_NORMAL));

  say("sync", result(syscall(SYS_sync)));

  int vectors = open("filealloc-dir/vectors", O_RDWR | O_CREAT | O_TRUNC, 0644);
  struct iovec out[2] = {{"hello", 5}, {" world", 6}};
  say("pwritev", result(pwritev(vectors, out, 2, 3)));
  say("size", sizeOf(vectors));
  show("bytes", vectors, 0, 14);
  char first[4], second[4];
  struct iovec in[2] = {{first, 4}, {second, 4}};
  say("preadv", result(preadv(vectors, in, 2, 5)));
  write(1, first, 4);
  write(1, second, 4);
  write(1, "\n", 1);
  say("preadv past the end", result(preadv(vectors, in, 2, 12)));
  say("preadv at the end", result(preadv(vectors, in, 2, 14)));
  say("offset", result(lseek(vectors, 0, SEEK_CUR)));
  say("preadv negative", result(preadv(vectors, in, 2, -1)));
  say("pwritev negative", result(pwritev(vectors, out, 2, -2)));
  say("preadv of a pipe", result(preadv(pipes[0], in, 2, 0)));
  say("pwritev of what is open to read", result(pwritev(reader, out, 2, 0)));
  say("preadv of no descriptor", result(preadv(noDescriptor(), in, 2, 0)));

  lseek(vectors, 3, SEEK_SET);
  struct iovec five[1] = {{first, 4}};
  say("preadv2 at the offset", readv2(vectors, five, 1, -1, 0));
  write(1, first, 4);
  write(1, "\n", 1);
  say("offset", result(lseek(vectors, 0, SEEK_CUR)));
  struct iovec bang[1] = {{"!", 1}};
  say("pwritev2 at the offset", writev2(vectors, bang, 1, -1, 0));
  say("offset", result(lseek(vectors, 0, SEEK_CUR)));
  show("bytes", vectors, 0, 14);
  say("preadv2 at 9", readv2(vectors, five, 1, 9, 0));
  write(1, first, 4);
  write(1, "\n", 1);
  say("offset", result(lseek(vectors, 0, SEEK_CUR)));
  say("pwritev2 at 0", writev2(vectors, bang, 1, 0, 0));
  show("bytes", vectors, 0, 14);
  say("preadv2 negative", readv2(vectors, five, 1, -2, 0));
  say("preadv2 of an unknown flag", readv2(vectors, five, 1, 0, 0x40000000));
  say("pwritev2 of an unknown flag", writev2(vectors, bang, 1, 0, 0x40000000));
  say("pwritev2 of a pipe", writev2(pipes[1], bang, 1, 0, 0));
  say("pwritev2 of a pipe at its offset", writev2(pipes[1], bang, 1, -1, 0));
  say("preadv2 of a pipe at its offset", readv2(pipes[0], five, 1, -1, 0));

  int appending = open("filealloc-dir/appended", O_WRONLY | O_CREAT | O_TRUNC | O_APPEND, 0644);
  write(appending, "abc", 3);
  struct iovec more[2] = {{"de", 2}, {"f", 1}};
  say("pwritev of what appends", result(pwritev(appending, more, 2, 0)));
  say("size", sizeOf(appending));
  int appended = open("filealloc-dir/appended", O_RDONLY);
  show("bytes", appended, 0, 6);

  close(fd);
  close(reader);
  close(vectors);
  close(appending);
  close(appended);
  say("unlink", result(syscall(SYS_unlinkat, AT_FDCWD, "filealloc-dir/file", 0)));
  say("unlink", result(syscall(SYS_unlinkat, AT_FDCWD, "filealloc-dir/vectors", 0)));
  say("unlink", result(syscall(SYS_unlinkat, AT_FDCWD, "filealloc-dir/appended", 0)));
  say("rmdir", result(syscall(SYS_unlinkat, AT_FDCWD, "filealloc-dir", AT_REMOVEDIR)));
  return 0;
}
