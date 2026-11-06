// How many links stat says that a thing has, as Linux has it on tmpfs: a file has one for each of its names, and none once they are all
// gone but it is open, as a file of O_TMPFILE has none; a directory has two, and one more for each directory in it, which mkdir, rmdir
// and rename of a directory into it or out of it change, and none once it is removed but open; a pipe, a socket, an eventfd and
// /dev/null have one, and a file of memfd_create none. It works in a directory that it makes where it runs, and takes it away at the
// end. It says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

static long result(long value) { return value < 0 ? -errno : value; }

// The links of a path, or with an empty path of what a descriptor has open, as statx says them, or why there are none.
static long linksAt(int dir, const char *path) {
  unsigned int buffer[64];
  if (syscall(SYS_statx, dir, path, (path[0] ? 0 : AT_EMPTY_PATH) | AT_SYMLINK_NOFOLLOW, 0x4, buffer) < 0) return -errno;
  return buffer[0x10 / 4];
}

static long links(const char *path) { return linksAt(AT_FDCWD, path); }
static long linksOf(int fd) { return linksAt(fd, ""); }

int main(void) {
  say("mkdir", result(syscall(SYS_mkdirat, AT_FDCWD, "nlink-dir", 0755)));
  say("directory", links("nlink-dir"));

  int fd = open("nlink-dir/file", O_RDWR | O_CREAT | O_EXCL, 0644);
  say("open", fd >= 0);
  say("file", linksOf(fd));
  say("directory with a file", links("nlink-dir"));
  say("link", result(syscall(SYS_linkat, AT_FDCWD, "nlink-dir/file", AT_FDCWD, "nlink-dir/other", 0)));
  say("file", linksOf(fd));
  say("other name", links("nlink-dir/other"));
  say("rename over nothing", result(syscall(SYS_renameat, AT_FDCWD, "nlink-dir/other", AT_FDCWD, "nlink-dir/moved")));
  say("file", linksOf(fd));
  say("unlink one", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/file", 0)));
  say("file", linksOf(fd));
  say("moved name", links("nlink-dir/moved"));
  say("unlink the other", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/moved", 0)));
  say("open file without a name", linksOf(fd));
  close(fd);

  say("symlink", result(syscall(SYS_symlinkat, "file", AT_FDCWD, "nlink-dir/link")));
  say("symlink", links("nlink-dir/link"));
  say("unlink symlink", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/link", 0)));

  say("mkdir sub", result(syscall(SYS_mkdirat, AT_FDCWD, "nlink-dir/sub", 0755)));
  say("directory with a directory", links("nlink-dir"));
  say("sub", links("nlink-dir/sub"));
  say("mkdir sub/deeper", result(syscall(SYS_mkdirat, AT_FDCWD, "nlink-dir/sub/deeper", 0755)));
  say("sub with a directory", links("nlink-dir/sub"));
  say("directory", links("nlink-dir"));
  say("mkdir other", result(syscall(SYS_mkdirat, AT_FDCWD, "nlink-dir/other", 0755)));
  say("directory with two", links("nlink-dir"));
  // Out of one directory into another: the first has one less, the other one more, and what moved is as it was.
  say("rename sub/deeper to other", result(syscall(SYS_renameat, AT_FDCWD, "nlink-dir/sub/deeper", AT_FDCWD, "nlink-dir/other/deeper")));
  say("sub", links("nlink-dir/sub"));
  say("other", links("nlink-dir/other"));
  say("deeper", links("nlink-dir/other/deeper"));
  say("directory", links("nlink-dir"));
  // Over an empty directory in a third: that has one directory in place of another.
  say("mkdir sub/empty", result(syscall(SYS_mkdirat, AT_FDCWD, "nlink-dir/sub/empty", 0755)));
  say("sub", links("nlink-dir/sub"));
  say("rename other/deeper over sub/empty",
      result(syscall(SYS_renameat, AT_FDCWD, "nlink-dir/other/deeper", AT_FDCWD, "nlink-dir/sub/empty")));
  say("sub", links("nlink-dir/sub"));
  say("other", links("nlink-dir/other"));
  // A directory and a file trade places.
  fd = open("nlink-dir/other/file", O_RDWR | O_CREAT | O_EXCL, 0644);
  say("open", fd >= 0);
  close(fd);
  say("exchange sub/empty and other/file",
      result(syscall(SYS_renameat2, AT_FDCWD, "nlink-dir/sub/empty", AT_FDCWD, "nlink-dir/other/file", 2)));
  say("sub", links("nlink-dir/sub"));
  say("other", links("nlink-dir/other"));
  say("file", links("nlink-dir/sub/empty"));
  say("unlink file", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/sub/empty", 0)));
  say("rmdir other/file", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/other/file", AT_REMOVEDIR)));
  say("other", links("nlink-dir/other"));
  // A directory that is open once it is removed.
  int dir = open("nlink-dir/other", O_RDONLY | O_DIRECTORY);
  say("open other", dir >= 0);
  say("rmdir other", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/other", AT_REMOVEDIR)));
  say("removed directory", linksOf(dir));
  close(dir);
  say("directory", links("nlink-dir"));
  say("rmdir sub", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir/sub", AT_REMOVEDIR)));
  say("directory", links("nlink-dir"));

  fd = open("nlink-dir", O_RDWR | O_TMPFILE, 0600);
  say("O_TMPFILE", fd >= 0);
  say("file of O_TMPFILE", linksOf(fd));
  close(fd);

  int pipes[2];
  say("pipe", result(syscall(SYS_pipe2, pipes, 0)));
  say("pipe", linksOf(pipes[0]));
  close(pipes[0]);
  close(pipes[1]);
  int pair[2];
  say("socketpair", result(syscall(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, pair)));
  say("socket", linksOf(pair[0]));
  close(pair[0]);
  close(pair[1]);
  int event = (int)syscall(SYS_eventfd2, 0, 0);
  say("eventfd", linksOf(event));
  close(event);
  int memory = (int)syscall(SYS_memfd_create, "nlink", 0);
  say("memfd", linksOf(memory));
  close(memory);
  say("/dev/null", links("/dev/null"));

  say("rmdir", result(syscall(SYS_unlinkat, AT_FDCWD, "nlink-dir", AT_REMOVEDIR)));
  return 0;
}
