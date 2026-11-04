// Names that are wrong or odd: an empty path, which is no file rather than the working directory, a directory that isn't open, whose
// error is its own, and a name of bytes that aren't UTF-8, which is a name like any other.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
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

int main(void) {
  char status[256];
  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp", 0777, 0, 0);
  call(SYS_mkdirat, AT_FDCWD, (long)"/tmp/names", 0755, 0, 0);
  call(SYS_chdir, (long)"/tmp/names", 0, 0, 0, 0);
  say("stat empty", call(SYS_statx, AT_FDCWD, (long)"", 0, 0x7ff, (long)status), 0);
  say("chdir empty", call(SYS_chdir, (long)"", 0, 0, 0, 0), 0);
  say("mkdir empty", call(SYS_mkdirat, AT_FDCWD, (long)"", 0755, 0, 0), 0);
  say("rename empty", call(SYS_renameat2, AT_FDCWD, (long)"", AT_FDCWD, (long)"/tmp/names-moved", 0), call(SYS_faccessat, AT_FDCWD, (long)"/tmp/names", 0, 0, 0));
  say("chown empty", call(SYS_fchownat, AT_FDCWD, (long)"", 0, 0, 0), 0);
  int watcher = (int)call(SYS_inotify_init1, 0, 0, 0, 0, 0);
  say("watch empty", call(SYS_inotify_add_watch, watcher, (long)"", 2, 0, 0), 0);
  say("linkat closed directory", call(SYS_linkat, 99, (long)"a", AT_FDCWD, (long)"b", 0), 0);
  // A name of bytes that aren't UTF-8.
  const char odd[] = {'o', (char)0xff, 'd', 0};
  int fd = open(odd, O_WRONLY | O_CREAT, 0644);
  say("odd name", fd >= 0, call(SYS_faccessat, AT_FDCWD, (long)odd, 0, 0, 0));
  const char other[] = {'o', (char)0xfe, 'd', 0};
  say("another odd name", call(SYS_faccessat, AT_FDCWD, (long)other, 0, 0, 0), 0);
  say("unlink odd name", call(SYS_unlinkat, AT_FDCWD, (long)odd, 0, 0, 0), call(SYS_faccessat, AT_FDCWD, (long)odd, 0, 0, 0));
  call(SYS_chdir, (long)"/", 0, 0, 0, 0);
  call(SYS_unlinkat, AT_FDCWD, (long)"/tmp/names", AT_REMOVEDIR, 0, 0);
  return 0;
}
