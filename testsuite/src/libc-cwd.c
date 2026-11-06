// The working directory is a directory, not a name: renamed, the process is in it by its new name, and what it makes there is under
// that; removed, it has no name, getcwd says ENOENT and nothing can be made in it, while `..` is still its parent; fchdir goes into what
// a descriptor has open, and a child is where its parent is. It works in a directory of its own, which it makes and removes.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
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

static long result(long value) { return value < 0 ? -errno : value; }

// The libc of the tests has no mkdir, chdir, rmdir or stat, so they are called by number.
static long makeDirectory(const char *path, long mode) { return syscall(SYS_mkdirat, AT_FDCWD, path, mode); }
static long changeDirectory(const char *path) { return syscall(SYS_chdir, path); }
static long removeDirectory(const char *path) { return syscall(SYS_unlinkat, AT_FDCWD, path, AT_REMOVEDIR); }
static long statPath(const char *path, struct stat *st) { return syscall(SYS_newfstatat, AT_FDCWD, path, st, 0); }

static char top[4096];
static unsigned long topLength;

// Whether the working directory is `top` and then `name`, as getcwd says, or the error that it gives.
static long cwdIs(const char *name) {
  char buffer[4096];
  long got = syscall(SYS_getcwd, buffer, sizeof buffer);
  if (got < 0) return -errno;
  unsigned long n = 0;
  while (n < topLength && buffer[n] == top[n]) n++;
  if (n != topLength) return 0;
  unsigned long k = 0;
  while (name[k] && buffer[n + k] == name[k]) k++;
  return !name[k] && !buffer[n + k];
}

// Whether there is something at `top` and then `name`.
static long existsAt(const char *name) {
  char path[4096];
  unsigned long n = 0;
  while (n < topLength) { path[n] = top[n]; n++; }
  unsigned long k = 0;
  do path[n + k] = name[k]; while (name[k++]);
  struct stat st;
  return result(statPath(path, &st));
}

int main(void) {
  say("made", result(makeDirectory("cwd-work", 0755)), result(changeDirectory("cwd-work")));
  if (syscall(SYS_getcwd, top, sizeof top) < 0) return 1;
  while (top[topLength]) topLength++;

  // Renamed, by a name of its parent.
  say("in one", result(makeDirectory("one", 0755)), result(changeDirectory("one")));
  say("renamed", result(rename("../one", "../two")), cwdIs("/two"));
  long fd = result(open("made", O_CREAT | O_WRONLY, 0644));
  say("created", fd >= 0, existsAt("/two/made"));
  close(fd);
  say("not old", existsAt("/one/made"), 0);
  char link[4096];
  long length = result(readlink("/proc/self/cwd", link, sizeof link));
  say("proc cwd", length == (long)topLength + 4, length > 0 && link[length - 1] == 'o');

  // A child is where its parent is, after the rename and after another.
  say("renamed again", result(rename("../two", "../three")), cwdIs("/three"));
  int status = 0;
  pid_t child = fork();
  if (child == 0) _exit(cwdIs("/three") == 1 && existsAt("/three/made") == 0 ? 7 : 8);
  waitpid(child, &status, 0);
  say("child", WIFEXITED(status), WEXITSTATUS(status));

  // fchdir into what a descriptor has open, which was renamed while it was open.
  say("up", result(changeDirectory("..")), cwdIs(""));
  say("dir", result(makeDirectory("four", 0755)), 0);
  long directory = result(open("four", O_RDONLY | O_DIRECTORY));
  say("renamed open", result(rename("four", "five")), 0);
  say("fchdir", result(fchdir(directory)), cwdIs("/five"));
  close(directory);
  long bad = result(open(".", O_RDONLY));
  close(bad);
  say("fchdir bad", result(fchdir(bad)), 0);

  // Removed: no name, and nothing made in it, but it is still a directory and `..` is its parent.
  say("removed", result(removeDirectory("../five")), 0);
  say("getcwd gone", cwdIs("/five"), 0);
  say("create gone", result(open("file", O_CREAT | O_WRONLY, 0644)), result(makeDirectory("sub", 0755)));
  say("not made", existsAt("/five/file"), existsAt("/file"));
  struct stat st;
  say("stat here", result(statPath(".", &st)), S_ISDIR(st.st_mode));
  say("back up", result(changeDirectory("..")), cwdIs(""));
  say("same name", result(makeDirectory("five", 0755)), 0);
  say("not in it", existsAt("/five/file"), result(removeDirectory("five")));

  // A child that changes directory leaves its parent where it was.
  say("dir", result(makeDirectory("six", 0755)), 0);
  child = fork();
  if (child == 0) _exit(changeDirectory("six") == 0 && cwdIs("/six") == 1 ? 7 : 8);
  waitpid(child, &status, 0);
  say("child moved", WEXITSTATUS(status), cwdIs(""));

  say("cleaned", result(unlink("three/made")), result(removeDirectory("three")));
  say("cleaned", result(removeDirectory("six")), 0);
  say("out", result(changeDirectory("..")), result(removeDirectory("cwd-work")));
  return 0;
}
