// Details of the calls on files, as Linux has them: O_CREAT|O_EXCL makes nothing through a link at the end of the path, O_TRUNC
// empties a file opened only to read, pwrite to what was opened O_APPEND goes to its end, SEEK_DATA and SEEK_HOLE of a file without
// holes, renameat2 of flags that there aren't, symlink of nothing, linkat of AT_EMPTY_PATH of a file that has no name, readlink into
// no room, and the numbers of the devices of /dev, which it only looks at. All the rest is in a directory that it makes, and takes
// away again.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a) {
  char line[96];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long value = a;
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int digit = 0;
  do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (digit) line[n++] = digits[--digit];
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

#define P(path) (long)(path)

static long openat_(const char *path, long flags) { return call(SYS_openat, AT_FDCWD, P(path), flags, 0644, 0); }
static long gone(const char *path, long flags) { return call(SYS_unlinkat, AT_FDCWD, P(path), flags, 0, 0); }

// What stat says of a path: its size, or the error.
static long size(const char *path) {
  struct stat st;
  long result = call(SYS_newfstatat, AT_FDCWD, P(path), (long)&st, 0, 0);
  return result < 0 ? result : (long)st.st_size;
}

// What stat says of a device: the number of it, or the error.
static long device(const char *path) {
  struct stat st;
  long result = call(SYS_newfstatat, AT_FDCWD, P(path), (long)&st, 0, 0);
  return result < 0 ? result : (long)st.st_rdev;
}

// A file of these bytes, made anew.
static void put(const char *path, const char *text) {
  long fd = openat_(path, O_WRONLY | O_CREAT | O_TRUNC);
  unsigned long n = 0;
  while (text[n]) n++;
  write((int)fd, text, n);
  close((int)fd);
}

// What a file holds, as a number of its bytes, each of them a letter: a for 1, b for 2 and so on, in base 32.
static long letters(const char *path) {
  long fd = openat_(path, O_RDONLY);
  char bytes[16];
  long count = read((int)fd, bytes, sizeof bytes);
  close((int)fd);
  long value = 0;
  for (long index = 0; index < count; index++) value = value * 32 + (bytes[index] - 'a' + 1);
  return value;
}

// The path of a descriptor in /proc/self/fd.
static void fdPath(char *out, long fd) {
  const char *start = "/proc/self/fd/";
  int n = 0;
  while (start[n]) { out[n] = start[n]; n++; }
  if (fd >= 10) out[n++] = (char)('0' + fd / 10);
  out[n++] = (char)('0' + fd % 10);
  out[n] = 0;
}

int main(void) {
  call(SYS_mkdirat, AT_FDCWD, P("calls"), 0755, 0, 0);

  // O_CREAT|O_EXCL of a link that points at nothing: EEXIST, and nothing is made.
  call(SYS_symlinkat, P("target"), AT_FDCWD, P("calls/dangle"), 0, 0);
  say("excl dangling link", openat_("calls/dangle", O_WRONLY | O_CREAT | O_EXCL));
  say("excl made target", size("calls/target"));
  long fd = openat_("calls/dangle", O_WRONLY | O_CREAT);
  say("creat dangling link", fd >= 0);
  close((int)fd);
  say("creat made target", size("calls/target"));

  // O_TRUNC of a file opened to read.
  put("calls/f", "hello");
  fd = openat_("calls/f", O_RDONLY | O_TRUNC);
  say("rdonly trunc", fd >= 0);
  close((int)fd);
  say("rdonly trunc size", size("calls/f"));

  // pwrite of O_APPEND goes to the end, and leaves the offset.
  put("calls/f", "abcdef");
  fd = openat_("calls/f", O_WRONLY | O_APPEND);
  say("append pwrite", call(SYS_pwrite64, fd, P("xy"), 2, 0, 0));
  say("append pwrite offset", call(SYS_lseek, fd, 0, SEEK_CUR, 0, 0));
  close((int)fd);
  say("append pwrite content", letters("calls/f"));

  // SEEK_DATA and SEEK_HOLE of a file of 5 bytes, all of them data, and of an empty one and a directory.
  put("calls/f", "hello");
  fd = openat_("calls/f", O_RDONLY);
  say("data 0", call(SYS_lseek, fd, 0, SEEK_DATA, 0, 0));
  say("data 2", call(SYS_lseek, fd, 2, SEEK_DATA, 0, 0));
  say("data offset", call(SYS_lseek, fd, 0, SEEK_CUR, 0, 0));
  say("data 5", call(SYS_lseek, fd, 5, SEEK_DATA, 0, 0));
  say("data 9", call(SYS_lseek, fd, 9, SEEK_DATA, 0, 0));
  say("data -1", call(SYS_lseek, fd, -1, SEEK_DATA, 0, 0));
  say("hole 0", call(SYS_lseek, fd, 0, SEEK_HOLE, 0, 0));
  say("hole 2", call(SYS_lseek, fd, 2, SEEK_HOLE, 0, 0));
  say("hole offset", call(SYS_lseek, fd, 0, SEEK_CUR, 0, 0));
  say("hole 5", call(SYS_lseek, fd, 5, SEEK_HOLE, 0, 0));
  say("hole 9", call(SYS_lseek, fd, 9, SEEK_HOLE, 0, 0));
  say("hole -1", call(SYS_lseek, fd, -1, SEEK_HOLE, 0, 0));
  close((int)fd);
  put("calls/empty", "");
  fd = openat_("calls/empty", O_RDONLY);
  say("empty data 0", call(SYS_lseek, fd, 0, SEEK_DATA, 0, 0));
  say("empty hole 0", call(SYS_lseek, fd, 0, SEEK_HOLE, 0, 0));
  close((int)fd);
  gone("calls/empty", 0);
  fd = openat_("calls", O_RDONLY | O_DIRECTORY);
  say("directory data 0", call(SYS_lseek, fd, 0, SEEK_DATA, 0, 0));
  close((int)fd);

  // renameat2 of a flag that there isn't, and of RENAME_NOREPLACE with RENAME_EXCHANGE.
  say("renameat2 flag 8", call(SYS_renameat2, AT_FDCWD, P("calls/f"), AT_FDCWD, P("calls/g"), 8));
  say("renameat2 noreplace exchange", call(SYS_renameat2, AT_FDCWD, P("calls/f"), AT_FDCWD, P("calls/target"), 3));
  say("renameat2 left it", size("calls/f"));

  // symlink of an empty target.
  say("symlink of nothing", call(SYS_symlinkat, P(""), AT_FDCWD, P("calls/empty"), 0, 0));
  say("symlink made", size("calls/empty"));

  // linkat of a file that has no name, by AT_EMPTY_PATH and by /proc/self/fd, and of one of O_TMPFILE, which may have one, unless
  // it was O_EXCL or had one already.
  char path[32];
  fd = openat_("calls/u", O_RDWR | O_CREAT);
  gone("calls/u", 0);
  say("link unlinked empty path", call(SYS_linkat, fd, P(""), AT_FDCWD, P("calls/back"), AT_EMPTY_PATH));
  fdPath(path, fd);
  say("link unlinked proc", call(SYS_linkat, AT_FDCWD, P(path), AT_FDCWD, P("calls/back"), AT_SYMLINK_FOLLOW));
  close((int)fd);
  fd = openat_("calls", O_RDWR | O_TMPFILE);
  say("link tmpfile", call(SYS_linkat, fd, P(""), AT_FDCWD, P("calls/kept"), AT_EMPTY_PATH));
  say("tmpfile kept", size("calls/kept"));
  say("link tmpfile again", call(SYS_linkat, fd, P(""), AT_FDCWD, P("calls/also"), AT_EMPTY_PATH));
  gone("calls/kept", 0);
  gone("calls/also", 0);
  say("link tmpfile once unlinked", call(SYS_linkat, fd, P(""), AT_FDCWD, P("calls/kept"), AT_EMPTY_PATH));
  close((int)fd);
  fd = openat_("calls", O_RDWR | O_TMPFILE | O_EXCL);
  say("link excl tmpfile", call(SYS_linkat, fd, P(""), AT_FDCWD, P("calls/never"), AT_EMPTY_PATH));
  close((int)fd);

  // readlink into no room, of a link, of a file and of nothing.
  char room[8];
  say("readlink 0", call(SYS_readlinkat, AT_FDCWD, P("calls/dangle"), P(room), 0, 0));
  say("readlink 0 of file", call(SYS_readlinkat, AT_FDCWD, P("calls/f"), P(room), 0, 0));
  say("readlink 0 of missing", call(SYS_readlinkat, AT_FDCWD, P("calls/missing"), P(room), 0, 0));
  say("readlink -1", call(SYS_readlinkat, AT_FDCWD, P("calls/dangle"), P(room), -1, 0));
  say("readlink 3", call(SYS_readlinkat, AT_FDCWD, P("calls/dangle"), P(room), 3, 0));
#ifdef SYS_readlink
  say("readlink 0 of old call", call(SYS_readlink, P("calls/dangle"), P(room), 0, 0, 0));
#else
  say("readlink 0 of old call", -EINVAL);
#endif

  // The numbers of the devices.
  say("rdev null", device("/dev/null"));
  say("rdev zero", device("/dev/zero"));
  say("rdev full", device("/dev/full"));
  say("rdev random", device("/dev/random"));
  say("rdev urandom", device("/dev/urandom"));
  say("rdev tty", device("/dev/tty"));
  say("rdev ptmx", device("/dev/ptmx"));
  say("rdev file", device("calls/f"));

  gone("calls/f", 0);
  gone("calls/target", 0);
  gone("calls/dangle", 0);
  say("all gone", gone("calls", AT_REMOVEDIR));
  return 0;
}
