// What execve makes of a new program, as Linux has it: the auxiliary vector has the ids that the process has, AT_EXECFN the path that
// execve was given, not argv[0], in a copy of its own above the strings of the arguments, which the strings of the environment follow
// with nothing between them, and AT_PLATFORM and AT_RANDOM below those. A program run with no arguments has one, which is empty. A
// script is run by what its first line names, relative to the working directory, with the path of the script as it was given, and
// the process is named by that. A program run by /proc/self/exe has the file as its /proc/self/exe, which runs it again. It copies
// itself into a directory that it makes where it runs, and takes that away at the end; each case is a child that runs the copy or
// itself, with an environment that says which, and says what it found, the same on each target. As root, a child is nobody first,
// so that its ids aren't those of root. The libc of the tests has no execve, so it is called by number.
#define _GNU_SOURCE
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

static void text(const char *label, const char *value) {
  write(1, label, strlen(label));
  write(1, " \"", 2);
  write(1, value, strlen(value));
  write(1, "\"\n", 2);
}

static void make(const char *path, const char *content, long mode) {
  int fd = syscall(SYS_openat, AT_FDCWD, path, O_CREAT | O_WRONLY | O_TRUNC, mode);
  write(fd, content, strlen(content));
  close(fd);
}

// What /proc/self/comm says, without its newline.
static void comm(void) {
  char name[32] = {0};
  int fd = syscall(SYS_openat, AT_FDCWD, "/proc/self/comm", O_RDONLY);
  long size = read(fd, name, sizeof name - 1);
  close(fd);
  if (size > 0 && name[size - 1] == '\n') name[size - 1] = 0;
  text("comm", name);
}

static const char *variable(char **envp, const char *name) {
  size_t length = strlen(name);
  for (; *envp; envp++)
    if (strncmp(*envp, name, length) == 0 && (*envp)[length] == '=') return *envp + length + 1;
  return "";
}

// What the new program says of itself, by the case that its environment names.
static int image(int argc, char **argv, char **envp, const char *mode) {
  const char *execfn = (const char *)getauxval(AT_EXECFN);
  // Run by the path of the file, which isn't the same everywhere.
  int again = strcmp(mode, "again") == 0;
  if (again) say("again by the file", strcmp(execfn, variable(envp, "exe")) == 0);
  else text(mode, execfn);
  say("uid", getauxval(AT_UID) == syscall(SYS_getuid));
  say("euid", getauxval(AT_EUID) == syscall(SYS_geteuid));
  say("gid", getauxval(AT_GID) == syscall(SYS_getgid));
  say("egid", getauxval(AT_EGID) == syscall(SYS_getegid));
  say("secure", getauxval(AT_SECURE));
  say("argc", argc);
  for (int index = 0; index < argc; index++) text("argv", argv[index]);
  say("argv ends", argv[argc] == NULL);
  if (!again) comm();
  if (strcmp(mode, "layout") == 0) {
    // The strings, one after the other: those of the arguments and then those of the environment.
    int contiguous = 1;
    for (int index = 0; index + 1 < argc; index++) contiguous &= argv[index] + strlen(argv[index]) + 1 == argv[index + 1];
    say("arguments contiguous", contiguous);
    say("environment follows", argv[argc - 1] + strlen(argv[argc - 1]) + 1 == envp[0]);
    int count = 0;
    while (envp[count]) count++;
    for (int index = 0; index + 1 < count; index++) contiguous &= envp[index] + strlen(envp[index]) + 1 == envp[index + 1];
    say("environment contiguous", contiguous);
    say("execfn above", execfn > envp[count - 1] + strlen(envp[count - 1]));
    const char *random = (const char *)getauxval(AT_RANDOM);
    say("random below", random + 16 <= argv[0]);
#if defined(__x86_64__) || defined(__aarch64__)
    const char *platform = (const char *)getauxval(AT_PLATFORM);
    say("platform below", platform + strlen(platform) < argv[0] && random < platform);
#endif
  } else if (strcmp(mode, "proc") == 0) {
    // The file that runs is what its link says, which runs it again.
    char link[4096] = {0};
    long size = readlink("/proc/self/exe", link, sizeof link - 1);
    say("exe is the file", size > 0 && strcmp(link, variable(envp, "exe")) == 0);
    char *arguments[] = {"again", NULL};
    char *environment[] = {"execimage=again", (char *)variable(envp, "exe") - 4, NULL};
    syscall(SYS_execve, link, arguments, environment);
    say("execve of link", -1);
    return 1;
  }
  return 0;
}

// A child that runs `path` with `arguments` and `environment`, from `directory`, as nobody if it is root.
static void run(const char *directory, const char *path, char **arguments, char **environment) {
  pid_t child = fork();
  if (child == 0) {
    if (syscall(SYS_getuid) == 0) {
      syscall(SYS_setgroups, 0, NULL);
      syscall(SYS_setresgid, 65534, 65534, 65534);
      syscall(SYS_setresuid, 65534, 65534, 65534);
    }
    if (directory) syscall(SYS_chdir, directory);
    syscall(SYS_execve, path, arguments, environment);
    _exit(100);
  }
  int status = 0;
  waitpid(child, &status, 0);
  say("exit", WEXITSTATUS(status));
}

int main(int argc, char **argv, char **envp) {
  const char *mode = variable(envp, "execimage");
  if (*mode) return image(argc, argv, envp, mode);

  say("mkdir", syscall(SYS_mkdirat, AT_FDCWD, "execimage", 0755));
  int from = syscall(SYS_openat, AT_FDCWD, "/proc/self/exe", O_RDONLY);
  int to = syscall(SYS_openat, AT_FDCWD, "execimage/copy", O_CREAT | O_WRONLY | O_TRUNC, 0755);
  char buffer[4096];
  long count, total = 0;
  while ((count = read(from, buffer, sizeof buffer)) > 0) total += write(to, buffer, count);
  close(from);
  close(to);
  say("copied", total > 1000);
  make("execimage/script", "#!./copy\n", 0755);

  char *layoutArguments[] = {"renamed", "x", "yy", NULL};
  char *layoutEnvironment[] = {"execimage=layout", "B=2", NULL};
  run(NULL, "execimage/copy", layoutArguments, layoutEnvironment);

  char *noArguments[] = {NULL};
  char *emptyEnvironment[] = {"execimage=empty", NULL};
  run(NULL, "execimage/copy", noArguments, emptyEnvironment);

  char *scriptArguments[] = {"named", "arg", NULL};
  char *scriptEnvironment[] = {"execimage=script", NULL};
  run("execimage", "./script", scriptArguments, scriptEnvironment);

  // The file that this is, which the child runs by its link.
  char exe[4096] = "exe=";
  readlink("/proc/self/exe", exe + 4, sizeof exe - 5);
  char *procArguments[] = {"proc", NULL};
  char *procEnvironment[] = {"execimage=proc", exe, NULL};
  run(NULL, "/proc/self/exe", procArguments, procEnvironment);

  say("unlink", syscall(SYS_unlinkat, AT_FDCWD, "execimage/copy", 0) + syscall(SYS_unlinkat, AT_FDCWD, "execimage/script", 0));
  say("rmdir", syscall(SYS_unlinkat, AT_FDCWD, "execimage", AT_REMOVEDIR));
  return 0;
}
