// What a name is to rename, unlink, rmdir and open: a mount point, which is busy; a file over a directory or the other way round; two
// names of the same file; O_CREAT of a directory; O_DIRECTORY of a device. It runs as root, natively in a namespace of its own.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/mount.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a, long b) {
  char line[96];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < 2; index++) {
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

static long move(const char *from, const char *to) { return call(SYS_renameat2, AT_FDCWD, (long)from, AT_FDCWD, (long)to, 0); }
static long gone(const char *path, long flags) { return call(SYS_unlinkat, AT_FDCWD, (long)path, flags, 0, 0); }
static long there(const char *path) { return call(SYS_faccessat, AT_FDCWD, (long)path, 0, 0, 0); }
static void make(const char *path) { close(open(path, O_WRONLY | O_CREAT, 0644)); }

int main(void) {
  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp", 0777, 0, 0);
  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp/paths-mount", 0755, 0, 0);
  say("tmpfs", call(SYS_mount, (long)"none", (long)"/tmp/paths-mount", (long)"tmpfs", 0, 0), 0);
  say("rmdir mount point", gone("/tmp/paths-mount", AT_REMOVEDIR), 0);
  say("rename mount point", move("/tmp/paths-mount", "/tmp/paths-moved"), 0);
  make("/tmp/paths-source");
  make("/tmp/paths-file");
  say("bind a file", call(SYS_mount, (long)"/tmp/paths-source", (long)"/tmp/paths-file", 0, MS_BIND, 0), 0);
  say("unlink mount point", gone("/tmp/paths-file", 0), there("/tmp/paths-source"));
  call(SYS_umount2, (long)"/tmp/paths-file", 0, 0, 0, 0);
  call(SYS_umount2, (long)"/tmp/paths-mount", 0, 0, 0, 0);

  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp/paths-dir", 0755, 0, 0);
  say("file over directory", move("/tmp/paths-file", "/tmp/paths-dir"), 0);
  say("directory over file", move("/tmp/paths-dir", "/tmp/paths-file"), 0);
  call(SYS_linkat, AT_FDCWD, (long)"/tmp/paths-file", AT_FDCWD, (long)"/tmp/paths-link", 0);
  say("rename to itself", move("/tmp/paths-file", "/tmp/paths-link"), there("/tmp/paths-file") == 0 && there("/tmp/paths-link") == 0);
  say("O_CREAT of a directory", open("/tmp/paths-dir", O_RDONLY | O_CREAT, 0644) < 0 ? -errno : 0, 0);
  say("O_DIRECTORY of a device", open("/dev/null", O_RDONLY | O_DIRECTORY) < 0 ? -errno : 0, 0);
  gone("/tmp/paths-link", 0);
  gone("/tmp/paths-file", 0);
  gone("/tmp/paths-source", 0);
  gone("/tmp/paths-dir", AT_REMOVEDIR);
  gone("/tmp/paths-mount", AT_REMOVEDIR);
  return 0;
}
