// What a slash at the end of a path is, and a `.` or `..` there: the path must be of a directory then, after the link it may name,
// which is ENOTDIR of anything else. open of O_CREAT makes no directory, unlink and rmdir don't take what isn't one, and rename takes it
// only of a directory. All of it is in a directory that it makes, and takes away again.
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

// What open gives: 0 for a descriptor, which is closed again, or the error.
static long opened(const char *path, long flags) {
  long fd = call(SYS_openat, AT_FDCWD, P(path), flags, 0644, 0);
  if (fd >= 0) { close((int)fd); return 0; }
  return fd;
}

// What stat says of a path: 1 for a directory, 2 for a file, 3 for a link, or the error.
static long kind(const char *path, long flags) {
  struct stat st;
  long result = call(SYS_newfstatat, AT_FDCWD, P(path), (long)&st, flags, 0);
  if (result < 0) return result;
  return S_ISDIR(st.st_mode) ? 1 : S_ISREG(st.st_mode) ? 2 : S_ISLNK(st.st_mode) ? 3 : 4;
}

static long gone(const char *path, long flags) { return call(SYS_unlinkat, AT_FDCWD, P(path), flags, 0, 0); }
static long made(const char *path) { return call(SYS_mkdirat, AT_FDCWD, P(path), 0755, 0, 0); }
static long moved(const char *from, const char *to) { return call(SYS_renameat2, AT_FDCWD, P(from), AT_FDCWD, P(to), 0); }
static long linked(const char *target, const char *path) { return call(SYS_symlinkat, P(target), AT_FDCWD, P(path), 0, 0); }

int main(void) {
  made("slash");
  close((int)call(SYS_openat, AT_FDCWD, P("slash/f"), O_WRONLY | O_CREAT, 0644, 0));
  made("slash/d");
  made("slash/d/e");
  linked("f", "slash/lf");
  linked("d", "slash/ld");
  linked("nothing", "slash/dangle");

  say("open file/", opened("slash/f/", O_RDONLY));
  say("open file/.", opened("slash/f/.", O_RDONLY));
  say("open dir/", opened("slash/d/", O_RDONLY));
  say("open dir/.", opened("slash/d/.", O_RDONLY));
  say("open link to file/", opened("slash/lf/", O_RDONLY));
  say("open link to dir/ nofollow", opened("slash/ld/", O_RDONLY | O_NOFOLLOW));
  say("open missing/", opened("slash/missing/", O_RDONLY));
  say("create new/", opened("slash/new/", O_WRONLY | O_CREAT));
  say("stat new", kind("slash/new", 0));
  say("create new/.", opened("slash/new/.", O_WRONLY | O_CREAT));
  say("stat new", kind("slash/new", 0));
  say("create file/", opened("slash/f/", O_RDONLY | O_CREAT));
  say("create dir/", opened("slash/d/", O_RDONLY | O_CREAT));
  say("create dangling link/", opened("slash/dangle/", O_WRONLY | O_CREAT));

  say("stat file/", kind("slash/f/", 0));
  say("stat dir/", kind("slash/d/", 0));
  say("stat missing/", kind("slash/missing/", 0));
  say("lstat link to dir", kind("slash/ld", AT_SYMLINK_NOFOLLOW));
  say("lstat link to dir/", kind("slash/ld/", AT_SYMLINK_NOFOLLOW));
  say("lstat link to file/", kind("slash/lf/", AT_SYMLINK_NOFOLLOW));
  say("lstat dangling link/", kind("slash/dangle/", AT_SYMLINK_NOFOLLOW));
  say("access file/", call(SYS_faccessat, AT_FDCWD, P("slash/f/"), F_OK, 0, 0));
  say("truncate file/", call(SYS_truncate, P("slash/f/"), 0, 0, 0, 0));

  say("unlink file/", gone("slash/f/", 0));
  say("stat file", kind("slash/f", 0));
  say("unlink dir/", gone("slash/d/", 0));
  say("unlink dir/.", gone("slash/d/.", 0));
  say("unlink link to dir/", gone("slash/ld/", 0));
  say("unlink missing/", gone("slash/missing/", 0));
  say("rmdir file/", gone("slash/f/", AT_REMOVEDIR));
  say("rmdir link to dir/", gone("slash/ld/", AT_REMOVEDIR));
  say("rmdir dir/.", gone("slash/d/e/.", AT_REMOVEDIR));
  say("rmdir dir/..", gone("slash/d/e/..", AT_REMOVEDIR));
  say("rmdir file/.", gone("slash/f/.", AT_REMOVEDIR));
  say("rmdir missing/.", gone("slash/missing/.", AT_REMOVEDIR));
  say("rmdir dir/", gone("slash/d/e/", AT_REMOVEDIR));
  say("stat dir", kind("slash/d/e", 0));

  say("mkdir new/", made("slash/n/"));
  say("stat new", kind("slash/n", 0));
  say("mkdir file/", made("slash/f/"));
  say("mkdir dangling link/", made("slash/dangle/"));
  say("mkdir new/.", made("slash/m/."));
  say("mkdir dir/.", made("slash/d/."));

  say("rename file to new/", moved("slash/f", "slash/g/"));
  say("rename file/ to new", moved("slash/f/", "slash/g"));
  say("rename dir/ to new/", moved("slash/n/", "slash/m/"));
  say("stat moved", kind("slash/m", 0));
  say("rename dir/. to new", moved("slash/m/.", "slash/k"));
  say("rename dir to dir/.", moved("slash/m", "slash/d/."));
  say("rename link to dir/ to new", moved("slash/ld/", "slash/k"));

  say("symlink to new/", linked("f", "slash/sl/"));
  say("symlink to file/", linked("f", "slash/f/"));
  say("link to new/", call(SYS_linkat, AT_FDCWD, P("slash/f"), AT_FDCWD, P("slash/hl/"), 0));
  say("link of file/", call(SYS_linkat, AT_FDCWD, P("slash/f/"), AT_FDCWD, P("slash/hl"), 0));
  say("chdir file/", call(SYS_chdir, P("slash/f/"), 0, 0, 0, 0));

  gone("slash/f", 0);
  gone("slash/lf", 0);
  gone("slash/ld", 0);
  gone("slash/dangle", 0);
  gone("slash/m", AT_REMOVEDIR);
  gone("slash/d", AT_REMOVEDIR);
  say("all gone", gone("slash", AT_REMOVEDIR));
  return 0;
}
