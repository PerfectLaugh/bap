// Permissions, as execve and access have them: a program runs only if it is a file that its caller may run, by the bits of its class
// of owner, group or everyone, and so does what a script names to run it; a directory isn't one, EACCES. access and faccessat2 say
// whether a file may be read, written or run by those bits, EINVAL of what isn't a mode or a flag, of the link itself with
// AT_SYMLINK_NOFOLLOW, and EACCES of what is in a directory that may not be searched. It copies itself into a directory that it makes
// where it runs, and takes that away at the end. Root may do more than this asks: as root it gives what it made to nobody and is
// nobody, so that it says the same as anyone else. It says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/wait.h>
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

static long access2(const char *path, long mode, long flags) {
  return result(syscall(SYS_faccessat2, AT_FDCWD, path, mode, flags));
}

static long access1(const char *path, long mode) { return result(syscall(SYS_faccessat, AT_FDCWD, path, mode)); }

static long chmodPath(const char *path, long mode) { return result(syscall(SYS_fchmodat, AT_FDCWD, path, mode)); }

static char *noEnvironment[] = {NULL};

// What execve gives of a path that it doesn't run.
static long refused(const char *path) {
  char *arguments[] = {(char *)path, "child", NULL};
  return result(syscall(SYS_execve, path, arguments, noEnvironment));
}

// How a child that runs a path exits, or 100 and why it couldn't.
static long run(const char *path) {
  pid_t child = fork();
  if (child == 0) {
    char *arguments[] = {(char *)path, "child", NULL};
    syscall(SYS_execve, path, arguments, noEnvironment);
    _exit(100 + errno);
  }
  int status = 0;
  waitpid(child, &status, 0);
  return WEXITSTATUS(status);
}

static void make(const char *path, const char *text, long mode) {
  int fd = syscall(SYS_openat, AT_FDCWD, path, O_CREAT | O_WRONLY | O_TRUNC, mode);
  size_t n = 0;
  while (text[n]) n++;
  write(fd, text, n);
  close(fd);
}

int main(int argc, char **argv) {
  // The copy, run by its own path or by a script.
  if (argc > 1 && argv[argc - 1][0] == 'c' && argv[argc - 1][1] == 'h') return 42;

  say("mkdir", result(syscall(SYS_mkdirat, AT_FDCWD, "perms", 0755)));
  int from = syscall(SYS_openat, AT_FDCWD, "/proc/self/exe", O_RDONLY);
  int to = syscall(SYS_openat, AT_FDCWD, "perms/copy", O_CREAT | O_WRONLY | O_TRUNC, 0700);
  char buffer[4096];
  long count, total = 0;
  while ((count = read(from, buffer, sizeof buffer)) > 0) total += write(to, buffer, count);
  close(from);
  close(to);
  say("copied", total > 1000);
  make("perms/script", "#!perms/copy\n", 0755);
  make("perms/file", "text", 0600);
  say("symlink", result(syscall(SYS_symlinkat, "file", AT_FDCWD, "perms/link")));
  if (getuid() == 0) {
    const char *made[] = {"perms", "perms/copy", "perms/script", "perms/file", "perms/link"};
    for (int index = 0; index < 5; index++) syscall(SYS_fchownat, AT_FDCWD, made[index], 65534, 65534, AT_SYMLINK_NOFOLLOW);
    // And where it is, which it takes what it made away from at the end, as anyone may of their own.
    syscall(SYS_fchownat, AT_FDCWD, ".", 65534, 65534, 0);
    syscall(SYS_setgroups, 0, NULL);
    syscall(SYS_setresgid, 65534, 65534, 65534);
    syscall(SYS_setresuid, 65534, 65534, 65534);
  }

  // A program that no one may run.
  say("chmod 644", chmodPath("perms/copy", 0644));
  say("access X 644", access1("perms/copy", X_OK));
  say("execve 644", refused("perms/copy"));
  say("script of 644", run("perms/script"));
  // That others may run, but not its owner.
  say("chmod 007", chmodPath("perms/copy", 0007));
  say("access X 007", access1("perms/copy", X_OK));
  say("execve 007", refused("perms/copy"));
  // That anyone may run.
  say("chmod 755", chmodPath("perms/copy", 0755));
  say("access X 755", access1("perms/copy", X_OK));
  say("access RX 755", access1("perms/copy", R_OK | X_OK));
  say("run 755", run("perms/copy"));
  say("script of 755", run("perms/script"));
  say("chmod script 644", chmodPath("perms/script", 0644));
  say("script 644", run("perms/script"));

  // A directory, which may be searched and isn't a program.
  say("access X directory", access1("perms", X_OK));
  say("execve directory", refused("perms"));
  say("execve dot", refused("."));

  // A file that its owner may only read.
  say("chmod 400", chmodPath("perms/file", 0400));
  say("access F", access1("perms/file", F_OK));
  say("access R", access1("perms/file", R_OK));
  say("access W", access1("perms/file", W_OK));
  say("access RW", access1("perms/file", R_OK | W_OK));
  say("access X", access1("perms/file", X_OK));
  say("access R effective", access2("perms/file", R_OK, AT_EACCESS));
  say("access W effective", access2("perms/file", W_OK, AT_EACCESS));
  say("access W of link", access2("perms/link", W_OK, 0));
  say("access W of link itself", access2("perms/link", W_OK, AT_SYMLINK_NOFOLLOW));
  say("access mode 8", access1("perms/file", 8));
  say("access bad flag", access2("perms/file", R_OK, 1));
  say("access missing", access1("perms/missing", F_OK));
  say("access W missing", access1("perms/missing", W_OK));

  // What is in a directory that may not be searched.
  say("chmod directory 600", chmodPath("perms", 0600));
  say("access in unsearchable", access1("perms/file", R_OK));
  say("access missing in unsearchable", access1("perms/missing", F_OK));
  say("execve in unsearchable", refused("perms/copy"));
  say("chmod directory 755", chmodPath("perms", 0755));

  say("unlink", result(syscall(SYS_unlinkat, AT_FDCWD, "perms/copy", 0)) + result(syscall(SYS_unlinkat, AT_FDCWD, "perms/script", 0)) +
    result(syscall(SYS_unlinkat, AT_FDCWD, "perms/file", 0)) + result(syscall(SYS_unlinkat, AT_FDCWD, "perms/link", 0)));
  say("rmdir", result(syscall(SYS_unlinkat, AT_FDCWD, "perms", AT_REMOVEDIR)));
  return 0;
}
