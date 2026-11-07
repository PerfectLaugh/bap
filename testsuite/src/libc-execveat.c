// execveat, as Linux has it: a path is from the directory that a descriptor is open on, or from the working directory for AT_FDCWD,
// and with AT_EMPTY_PATH an empty one is the file that the descriptor itself is open on, of O_PATH or not, which has to be one that may
// run: a directory is EACCES. A program run from a descriptor so has /dev/fd/N, or /dev/fd/N/path, for AT_EXECFN, and of an empty
// path is named by its file, as Linux has it since 6.14; a script is run with that path, which a descriptor that closes on exec takes
// away, so that it is ENOENT. With AT_SYMLINK_NOFOLLOW a link at the end is ELOOP, and any other flag is EINVAL. It copies itself
// into a directory that it makes where it runs, and takes that away at the end; each case is a child that runs the copy, with an
// environment that says what it is to say, and that ends with 7. The libc of the tests has no execveat, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <string.h>
#include <sys/auxv.h>
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

static void make(const char *path, const char *content, long mode) {
  int fd = syscall(SYS_openat, AT_FDCWD, path, O_CREAT | O_WRONLY | O_TRUNC, mode);
  write(fd, content, strlen(content));
  close(fd);
}

static const char *variable(char **envp, const char *name) {
  size_t length = strlen(name);
  for (; *envp; envp++)
    if (strncmp(*envp, name, length) == 0 && (*envp)[length] == '=') return *envp + length + 1;
  return "";
}

static int ends(const char *string, const char *end) {
  size_t length = strlen(string), size = strlen(end);
  return length >= size && strcmp(string + length - size, end) == 0;
}

// What the new program says of the path that it was run by.
static int image(int argc, char **argv, const char *mode) {
  const char *execfn = (const char *)getauxval(AT_EXECFN);
  say(mode, 1);
  say("execfn of /dev/fd", strncmp(execfn, "/dev/fd/", 8) == 0);
  say("execfn ends in /copy", ends(execfn, "/copy"));
  say("execfn is execveat/copy", strcmp(execfn, "execveat/copy") == 0);
  // What the process is named.
  char name[32] = {0};
  int fd = syscall(SYS_openat, AT_FDCWD, "/proc/self/comm", O_RDONLY);
  read(fd, name, sizeof name - 1);
  close(fd);
  say("comm is copy", strcmp(name, "copy\n") == 0);
  // A script has its path after the name of what runs it.
  if (argc > 1) say("script of /dev/fd", strncmp(argv[1], "/dev/fd/", 8) == 0);
  return 7;
}

// A child that runs `path` from `directory` with `flags`, and says what came of it: an error, or how the program ended.
static void run(const char *label, int directory, const char *path, int flags, const char *mode) {
  char environment[64] = "execveat=";
  memcpy(environment + 9, mode, strlen(mode) + 1);
  pid_t child = fork();
  if (child == 0) {
    char *arguments[] = {"copy", NULL};
    char *environ_[] = {environment, NULL};
    long result = syscall(SYS_execveat, directory, path, arguments, environ_, flags);
    say(label, result < 0 ? -errno : result);
    _exit(100);
  }
  int status = 0;
  waitpid(child, &status, 0);
  say("exit", WEXITSTATUS(status));
}

int main(int argc, char **argv, char **envp) {
  const char *mode = variable(envp, "execveat");
  if (*mode) return image(argc, argv, mode);

  say("mkdir", syscall(SYS_mkdirat, AT_FDCWD, "execveat", 0755));
  int from = syscall(SYS_openat, AT_FDCWD, "/proc/self/exe", O_RDONLY);
  int to = syscall(SYS_openat, AT_FDCWD, "execveat/copy", O_CREAT | O_WRONLY | O_TRUNC, 0755);
  char buffer[4096];
  long count, total = 0;
  while ((count = read(from, buffer, sizeof buffer)) > 0) total += write(to, buffer, count);
  close(from);
  close(to);
  say("copied", total > 1000);
  make("execveat/script", "#!execveat/copy\n", 0755);
  say("symlink", syscall(SYS_symlinkat, "copy", AT_FDCWD, "execveat/link"));

  int file = syscall(SYS_openat, AT_FDCWD, "execveat/copy", O_RDONLY);
  int path = syscall(SYS_openat, AT_FDCWD, "execveat/copy", O_PATH);
  int directory = syscall(SYS_openat, AT_FDCWD, "execveat", O_RDONLY | O_DIRECTORY);
  int script = syscall(SYS_openat, AT_FDCWD, "execveat/script", O_RDONLY);
  int closing = syscall(SYS_openat, AT_FDCWD, "execveat/script", O_RDONLY | O_CLOEXEC);
  int bad = syscall(SYS_openat, AT_FDCWD, "execveat/copy", O_RDONLY);
  close(bad);

  run("empty path", file, "", AT_EMPTY_PATH, "empty");
  run("empty path of O_PATH", path, "", AT_EMPTY_PATH, "opath");
  run("from a directory", directory, "copy", 0, "directory");
  run("from the working directory", AT_FDCWD, "execveat/copy", 0, "cwd");
  run("absolute path", directory, "/proc/self/exe", 0, "absolute");
  run("link", directory, "link", 0, "link");
  run("script", script, "", AT_EMPTY_PATH, "script");

  run("link without following", directory, "link", AT_SYMLINK_NOFOLLOW, "none");
  run("unknown flag", directory, "copy", 0x2, "none");
  run("empty path of a directory", directory, "", AT_EMPTY_PATH, "none");
  run("empty path without AT_EMPTY_PATH", file, "", 0, "none");
  run("from a file", file, "copy", 0, "none");
  run("from a bad descriptor", bad, "copy", 0, "none");
  run("script that closes on exec", closing, "", AT_EMPTY_PATH, "none");

  close(file);
  close(path);
  close(directory);
  close(script);
  close(closing);
  say("unlink", syscall(SYS_unlinkat, AT_FDCWD, "execveat/copy", 0) + syscall(SYS_unlinkat, AT_FDCWD, "execveat/script", 0) +
    syscall(SYS_unlinkat, AT_FDCWD, "execveat/link", 0));
  say("rmdir", syscall(SYS_unlinkat, AT_FDCWD, "execveat", AT_REMOVEDIR));
  return 0;
}
