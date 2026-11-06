// fchmod and the calls that write a file to its disk, as Linux has them: fchmod sets the permissions of what a descriptor has open,
// which fstat then shows, of a file, a directory and a pipe, and fchmodat of a path does the same; fsync, fdatasync and syncfs succeed
// for a file and a directory, and for memfd, while fsync and fdatasync give EINVAL for a pipe, a socket and an eventfd, and each gives
// EBADF for a descriptor that isn't open. It works in a directory that it makes where it runs, and takes it away at the end. It says
// what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long value, int base) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  if (base == 8) line[n++] = '0';
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % base); value /= base; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

static long result(long value) { return value < 0 ? -errno : value; }

// The type and permissions of a path from a descriptor, or of what the descriptor has open with an empty path, as statx says them,
// or why there are none.
static long statxMode(int dir, const char *path) {
  unsigned short buffer[128];
  if (syscall(SYS_statx, dir, path, path[0] ? 0 : AT_EMPTY_PATH, 0x2, buffer) < 0) return -errno;
  return buffer[0x1c / 2];
}

// The permissions of what a descriptor has open.
static long modeOf(int fd) {
  long mode = statxMode(fd, "");
  return mode < 0 ? mode : (mode & 07777);
}

static void syncs(const char *what, int fd) {
  char label[64];
  const char *calls[] = {"fsync", "fdatasync", "syncfs"};
  long numbers[] = {SYS_fsync, SYS_fdatasync, SYS_syncfs};
  for (int i = 0; i < 3; i++) {
    size_t n = 0;
    for (const char *c = calls[i]; *c; c++) label[n++] = *c;
    label[n++] = ' ';
    for (const char *c = what; *c; c++) label[n++] = *c;
    label[n] = 0;
    say(label, result(syscall(numbers[i], fd)), 10);
  }
}

int main(void) {
  syscall(SYS_umask, 022);
  say("mkdir", result(syscall(SYS_mkdirat, AT_FDCWD, "fchmod-dir", 0755)), 10);
  int fd = open("fchmod-dir/file", O_RDWR | O_CREAT | O_EXCL, 0644);
  say("open", fd >= 0, 10);
  say("file mode", modeOf(fd), 8);
  say("fchmod 0600", result(syscall(SYS_fchmod, fd, 0600)), 10);
  say("file mode", modeOf(fd), 8);
  // What is above the permissions is left as it is.
  say("fchmod 0104751", result(syscall(SYS_fchmod, fd, 0104751)), 10);
  say("file mode", modeOf(fd), 8);
  long mode = statxMode(AT_FDCWD, "fchmod-dir/file");
  say("path is a file", S_ISREG(mode), 10);
  say("path mode", mode & 07777, 8);
  // A descriptor that it has closed, and so isn't open: EBADF.
  close(fd);
  int closed = fd;
  say("fchmod closed", result(syscall(SYS_fchmod, closed, 0600)), 10);

  // A descriptor that is only read from changes the permissions all the same.
  fd = open("fchmod-dir/file", O_RDONLY);
  say("fchmod read-only 0640", result(syscall(SYS_fchmod, fd, 0640)), 10);
  say("file mode", modeOf(fd), 8);
  say("fchmodat 0604", result(syscall(SYS_fchmodat, AT_FDCWD, "fchmod-dir/file", 0604)), 10);
  say("file mode", modeOf(fd), 8);
  say("fchmodat missing", result(syscall(SYS_fchmodat, AT_FDCWD, "fchmod-dir/missing", 0604)), 10);
  syncs("file", fd);
  close(fd);

  int dir = open("fchmod-dir", O_RDONLY | O_DIRECTORY);
  say("fchmod directory 0700", result(syscall(SYS_fchmod, dir, 0700)), 10);
  say("directory mode", modeOf(dir), 8);
  say("fchmod directory 0755", result(syscall(SYS_fchmod, dir, 0755)), 10);
  syncs("directory", dir);
  close(dir);

  int pipes[2];
  say("pipe", result(syscall(SYS_pipe2, pipes, 0)), 10);
  say("fchmod pipe 0640", result(syscall(SYS_fchmod, pipes[0], 0640)), 10);
  say("pipe mode", modeOf(pipes[0]), 8);
  say("other end mode", modeOf(pipes[1]), 8);
  syncs("pipe", pipes[1]);
  close(pipes[0]);
  close(pipes[1]);

  int pair[2];
  say("socketpair", result(syscall(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, pair)), 10);
  syncs("socket", pair[0]);
  close(pair[0]);
  close(pair[1]);

  int event = (int)syscall(SYS_eventfd2, 0, 0);
  say("eventfd", event >= 0, 10);
  syncs("eventfd", event);
  close(event);

  int memory = (int)syscall(SYS_memfd_create, "fchmod", 0);
  say("memfd", memory >= 0, 10);
  say("fchmod memfd 0600", result(syscall(SYS_fchmod, memory, 0600)), 10);
  say("memfd mode", modeOf(memory), 8);
  syncs("memfd", memory);
  close(memory);

  syncs("closed", closed);

  say("unlink", result(syscall(SYS_unlinkat, AT_FDCWD, "fchmod-dir/file", 0)), 10);
  say("rmdir", result(syscall(SYS_unlinkat, AT_FDCWD, "fchmod-dir", AT_REMOVEDIR)), 10);
  return 0;
}
