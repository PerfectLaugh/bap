// The links of /proc/self/fd, and /dev/stdin, /dev/stdout, /dev/stderr and /dev/fd that lead to them: opening one opens what the
// descriptor is open on, whether it has a path or not, with an offset of its own, and reading one says what that is. It says what it
// found, the same on each target. The libc of the tests has no sockets, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/syscall.h>
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

// The path of a descriptor in a directory of links, as `/proc/self/fd/` and a number.
static const char *linkOf(char *path, const char *directory, int fd) {
  size_t n = 0;
  while (directory[n]) { path[n] = directory[n]; n++; }
  if (fd >= 10) path[n++] = (char)('0' + fd / 10);
  path[n++] = (char)('0' + fd % 10);
  path[n] = 0;
  return path;
}

static int startsWith(const char *text, long length, const char *prefix) {
  long n = 0;
  while (prefix[n]) { if (n >= length || text[n] != prefix[n]) return 0; n++; }
  return 1;
}

static int endsWith(const char *text, long length, const char *suffix) {
  long n = 0;
  while (suffix[n]) n++;
  if (length < n) return 0;
  for (long index = 0; index < n; index++) if (text[length - n + index] != suffix[index]) return 0;
  return 1;
}

static int same(const char *a, const char *b, long count) {
  for (long index = 0; index < count; index++) if (a[index] != b[index]) return 0;
  return 1;
}

int main(void) {
  char path[64], text[256];
  // What goes out by the paths of the standard descriptors, which are the console.
  int out = open("/dev/stdout", O_WRONLY);
  say("open /dev/stdout", 1, out < 0 ? -errno : 0, 0, 0);
  if (out >= 0) { write(out, "by /dev/stdout\n", 15); close(out); }
  int err = open("/dev/stderr", O_WRONLY);
  say("open /dev/stderr", 1, err < 0 ? -errno : 0, 0, 0);
  if (err >= 0) { write(err, "by /dev/stderr\n", 15); close(err); }

  // /dev/stdin, when it is a pipe.
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "piped\n", 6);
  dup2(pipes[0], 0);
  int in = open("/dev/stdin", O_RDONLY);
  say("open /dev/stdin of a pipe", 1, in < 0 ? -errno : 0, 0, 0);
  long n = in >= 0 ? result(read(in, text, sizeof text)) : 0;
  say("read it", 2, n, n == 6 && same(text, "piped\n", 6), 0);

  // A file that was removed, through its descriptor.
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777);
  int gone = open("/tmp/fdlinks-gone", O_RDWR | O_CREAT | O_TRUNC, 0644);
  write(gone, "kept", 4);
  unlink("/tmp/fdlinks-gone");
  int again = open(linkOf(path, "/proc/self/fd/", gone), O_RDONLY);
  say("open a removed file", 1, again < 0 ? -errno : 0, 0, 0);
  n = again >= 0 ? result(read(again, text, sizeof text)) : 0;
  say("read it from its start", 2, n, n == 4 && same(text, "kept", 4), 0);
  n = result(readlink(path, text, sizeof text));
  say("its link ends with (deleted)", 1, n > 0 && endsWith(text, n, " (deleted)"), 0, 0);
  n = result(readlink("/proc/self/fd/0", text, sizeof text));
  say("a pipe's link starts with pipe:[", 1, n > 0 && startsWith(text, n, "pipe:["), 0, 0);

  // The end of a pipe that writes, through /dev/fd, of the one that reads.
  int writer = open(linkOf(path, "/dev/fd/", pipes[0]), O_WRONLY);
  say("open a pipe to write through /dev/fd", 1, writer < 0 ? -errno : 0, 0, 0);
  n = writer >= 0 ? result(write(writer, "through", 7)) : 0;
  say("write to it", 1, n, 0, 0);
  n = result(read(pipes[0], text, sizeof text));
  say("read what it wrote", 2, n, n == 7 && same(text, "through", 7), 0);

  // A socket can't be opened.
  int sockets[2];
  syscall(SYS_socketpair, 1, 1, 0, sockets);
  n = result(open(linkOf(path, "/proc/self/fd/", sockets[0]), O_RDWR));
  say("open a socket", 1, n < 0 ? n : 0, 0, 0);
  n = result(readlink(path, text, sizeof text));
  say("its link starts with socket:[", 1, n > 0 && startsWith(text, n, "socket:["), 0, 0);

  // A file that has a path: another open file of it, with an offset of its own.
  int file = open("/tmp/fdlinks-file", O_RDWR | O_CREAT | O_TRUNC, 0644);
  write(file, "abcdef", 6);
  lseek(file, 1, SEEK_SET);
  int other = open(linkOf(path, "/proc/self/fd/", file), O_RDONLY);
  n = other >= 0 ? result(read(other, text, 2)) : -1;
  say("read two through its link", 2, n, n == 2 && same(text, "ab", 2), 0);
  say("where each is", 2, lseek(file, 0, SEEK_CUR), lseek(other, 0, SEEK_CUR), 0);
  n = result(readlink(path, text, sizeof text));
  say("its link is its path", 1, n == 17 && same(text, "/tmp/fdlinks-file", 17), 0, 0);
  // A directory, which a path goes on through.
  int directory = open("/tmp", O_RDONLY | O_DIRECTORY);
  linkOf(path, "/dev/fd/", directory);
  size_t end = 0;
  while (path[end]) end++;
  const char *name = "/fdlinks-file";
  for (size_t index = 0; name[index]; index++) path[end++] = name[index];
  path[end] = 0;
  int inside = open(path, O_RDONLY);
  n = inside >= 0 ? result(read(inside, text, 6)) : -errno;
  say("read a file in a directory through its link", 2, n, n == 6 && same(text, "abcdef", 6), 0);
  say("write to a directory through its link", 1, result(open(linkOf(path, "/proc/self/fd/", directory), O_RDWR)), 0, 0);
  unlink("/tmp/fdlinks-file");
  // A descriptor that isn't open has no link.
  say("a descriptor that isn't open", 1, result(open("/proc/self/fd/60", O_RDONLY)), 0, 0);
  return 0;
}
