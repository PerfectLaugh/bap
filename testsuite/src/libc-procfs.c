// What /proc says as Linux has it. A listing of /proc/self/fd that is read again from its start has what dup and close changed since,
// without the directory being opened again. The name of a process, in /proc/self/comm, the Name: of /proc/self/status, the second
// field of /proc/self/stat and PR_GET_NAME, is the last part of the path that it was run by, of 15 bytes at most, as is a name that
// PR_SET_NAME gives it; it is run by a long name, from a copy of itself in a directory that it
// makes where it runs, which it takes away at the end. /proc/self/maps has a line for each mapping, with its path at column 73 (49 on
// 32 bits): the program for its own code, [heap] for what brk has grown, s for what is shared, which is /dev/zero (deleted) if it is
// anonymous, and of a file the path and the offset that it was mapped at, and (deleted) after the path once the file is removed.
// execve of /proc/self/exe runs the program again, and so does execve of /proc/PID/exe of another process, before anything has looked
// in /proc; and a program that was run so runs itself again the same way. The libc of the tests has no execve, so it is called by
// number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stddef.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#define DIRECTORY "procfs-work"
#define COPY DIRECTORY "/a-long-program-name"
#define MAPPED DIRECTORY "/mapped"

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

static void text(const char *label, const char *value, size_t length) {
  write(1, label, strlen(label));
  write(1, " \"", 2);
  write(1, value, length);
  write(1, "\"\n", 2);
}

static long readAll(const char *path, char *buffer, long size) {
  int fd = syscall(SYS_openat, AT_FDCWD, path, O_RDONLY);
  long total = 0, got;
  while (total < size - 1 && (got = read(fd, buffer + total, size - 1 - total)) > 0) total += got;
  close(fd);
  buffer[total] = 0;
  return total;
}

// How many entries a directory has besides . and .., from its start.
static int entries(int fd) {
  char buffer[512];
  int count = 0;
  long got;
  syscall(SYS_lseek, fd, 0L, SEEK_SET);
  // A little at a time, as a listing that changes between reads has to be read.
  while ((got = syscall(SYS_getdents64, fd, buffer, sizeof buffer)) > 0)
    for (long at = 0; at < got;) {
      unsigned short length = *(unsigned short *)(buffer + at + 16);
      const char *name = buffer + at + 19;
      if (strcmp(name, ".") != 0 && strcmp(name, "..") != 0) count++;
      at += length;
    }
  return count;
}

// The first line of `content` that `label` begins, up to its end, without the label.
static const char *field(const char *content, const char *label, size_t *length) {
  size_t size = strlen(label);
  for (const char *line = content; *line; ) {
    if (strncmp(line, label, size) == 0) {
      const char *end = strchr(line, '\n');
      *length = end ? (size_t)(end - line) - size : strlen(line) - size;
      return line + size;
    }
    const char *end = strchr(line, '\n');
    if (!end) break;
    line = end + 1;
  }
  *length = 0;
  return "";
}

static void names(const char *when) {
  char content[4096];
  size_t length;
  write(1, when, strlen(when));
  write(1, "\n", 1);
  long size = readAll("/proc/self/comm", content, sizeof content);
  text("comm", content, size > 0 && content[size - 1] == '\n' ? size - 1 : size);
  readAll("/proc/self/status", content, sizeof content);
  const char *name = field(content, "Name:\t", &length);
  text("status", name, length);
  readAll("/proc/self/stat", content, sizeof content);
  const char *open = strchr(content, '(');
  const char *close_ = open;
  for (const char *at = content; *at; at++) if (*at == ')') close_ = at;
  text("stat", open + 1, close_ - open - 1);
  char asked[32] = {0};
  syscall(SYS_prctl, PR_GET_NAME, asked, 0L, 0L, 0L);
  text("prctl", asked, strlen(asked));
}

// A child that runs `path` with `mode` as its argument, and how it ended.
static void run(const char *path, const char *mode) {
  long child = syscall(SYS_clone, SIGCHLD, 0L, 0L, 0L, 0L);
  if (child == 0) {
    char *arguments[] = {(char *)path, (char *)mode, NULL};
    char *environment[] = {NULL};
    syscall(SYS_execve, path, arguments, environment);
    _exit(100 + errno);
  }
  int status = 0;
  syscall(SYS_wait4, child, &status, 0L, 0L);
  say(mode, WIFEXITED(status) ? WEXITSTATUS(status) : -1);
}

// The line of /proc/self/maps of an address, and where its fields are.
struct line { char text[512]; int perms, offset, path; };

static int lineOf(const char *maps, unsigned long address, struct line *found) {
  for (const char *line = maps; *line; ) {
    const char *end = strchr(line, '\n');
    if (!end) break;
    unsigned long start = 0, stop = 0;
    const char *at = line;
    for (; *at != '-'; at++) start = start * 16 + (*at <= '9' ? *at - '0' : *at - 'a' + 10);
    for (at++; *at != ' '; at++) stop = stop * 16 + (*at <= '9' ? *at - '0' : *at - 'a' + 10);
    if (start <= address && address < stop) {
      size_t length = end - line;
      memcpy(found->text, line, length);
      found->text[length] = 0;
      found->perms = at + 1 - line;
      found->offset = found->perms + 5;
      // After the device and the inode.
      int spaces = 0, index = found->offset;
      while (found->text[index] && spaces < 3) if (found->text[index++] == ' ') spaces++;
      while (found->text[index] == ' ') index++;
      found->path = index;
      return 1;
    }
    line = end + 1;
  }
  return 0;
}

static int endsWith(const char *value, const char *end) {
  size_t size = strlen(value), tail = strlen(end);
  return size >= tail && strcmp(value + size - tail, end) == 0;
}

static void maps(void) {
  static char content[65536];
  struct line line;
  int column = sizeof(void *) == 8 ? 73 : 49;
  // The program's own code, by the path of its file.
  char exe[4096] = {0};
  syscall(SYS_readlinkat, AT_FDCWD, "/proc/self/exe", exe, sizeof exe - 1);
  readAll("/proc/self/maps", content, sizeof content);
  lineOf(content, (unsigned long)&maps, &line);
  text("code perms", line.text + line.perms, 4);
  say("code is the program", strcmp(line.text + line.path, exe) == 0);
  say("code path column", line.path == column);
  // What brk grew.
  unsigned long top = syscall(SYS_brk, 0L);
  syscall(SYS_brk, top + 65536);
  readAll("/proc/self/maps", content, sizeof content);
  say("heap", lineOf(content, top + 4096, &line));
  text("heap perms", line.text + line.perms, 4);
  text("heap path", line.text + line.path, strlen(line.text + line.path));
  say("heap path column", line.path == column);
  syscall(SYS_brk, top);
  // What is shared and anonymous.
  long shared = syscall(SYS_mmap, 0L, 8192L, (long)(PROT_READ | PROT_WRITE), (long)(MAP_SHARED | MAP_ANONYMOUS), -1L, 0L);
  readAll("/proc/self/maps", content, sizeof content);
  lineOf(content, shared, &line);
  text("shared perms", line.text + line.perms, 4);
  text("shared offset", line.text + line.offset, 8);
  text("shared path", line.text + line.path, strlen(line.text + line.path));
  syscall(SYS_munmap, shared, 8192L);
  // A file, mapped from its second page.
  int fd = syscall(SYS_openat, AT_FDCWD, MAPPED, O_CREAT | O_RDWR | O_TRUNC, 0644);
  static char page[4096];
  for (int index = 0; index < 3; index++) write(fd, page, sizeof page);
  long mapped = syscall(SYS_mmap, 0L, 4096L, (long)PROT_READ, (long)MAP_PRIVATE, (long)fd, 4096L);
  close(fd);
  readAll("/proc/self/maps", content, sizeof content);
  lineOf(content, mapped, &line);
  text("file perms", line.text + line.perms, 4);
  text("file offset", line.text + line.offset, 8);
  say("file path", endsWith(line.text, "/" MAPPED));
  say("file path column", line.path == column);
  syscall(SYS_unlinkat, AT_FDCWD, MAPPED, 0L);
  readAll("/proc/self/maps", content, sizeof content);
  lineOf(content, mapped, &line);
  say("removed file path", endsWith(line.text, "/" MAPPED " (deleted)"));
  syscall(SYS_munmap, mapped, 4096L);
  // What is anonymous and private has no name, with a space after its inode.
  long private_ = syscall(SYS_mmap, 0L, 4096L, (long)(PROT_READ | PROT_WRITE), (long)(MAP_PRIVATE | MAP_ANONYMOUS), -1L, 0L);
  readAll("/proc/self/maps", content, sizeof content);
  lineOf(content, private_, &line);
  text("anonymous", line.text + line.offset, strlen(line.text + line.offset));
  syscall(SYS_munmap, private_, 4096L);
  readAll("/proc/self/maps", content, sizeof content);
  int stack = 0;
  for (const char *at = content; *at; at++) stack |= strncmp(at, " [stack]\n", 9) == 0;
  say("stack", stack);
}

int main(int argc, char **argv) {
  if (argc > 1 && (strcmp(argv[1], "exe") == 0 || strcmp(argv[1], "first") == 0 || strcmp(argv[1], "parent") == 0)) return 7;
  if (argc > 1 && strcmp(argv[1], "again") == 0) {
    char *arguments[] = {"/proc/self/exe", "exe", NULL};
    char *environment[] = {NULL};
    syscall(SYS_execve, "/proc/self/exe", arguments, environment);
    return 100 + errno;
  }
  if (argc > 1 && strcmp(argv[1], "named") == 0) {
    names("run by a long name");
    syscall(SYS_prctl, PR_SET_NAME, "another-long-name-here", 0L, 0L, 0L);
    names("after PR_SET_NAME");
    return 0;
  }
  // Before anything looks in /proc.
  run("/proc/self/exe", "first");
  run("/proc/self/exe", "again");
  char parent[32] = "/proc/";
  char digits[24];
  int d = 0;
  for (long pid = getpid(); pid; pid /= 10) digits[d++] = (char)('0' + pid % 10);
  size_t n = strlen(parent);
  while (d) parent[n++] = digits[--d];
  memcpy(parent + n, "/exe", 5);
  run(parent, "parent");
  int directory = syscall(SYS_openat, AT_FDCWD, "/proc/self/fd", O_RDONLY | O_DIRECTORY);
  int before = entries(directory);
  int status = syscall(SYS_openat, AT_FDCWD, "/proc/self/status", O_RDONLY);
  int stat = syscall(SYS_openat, AT_FDCWD, "/proc/self/stat", O_RDONLY);
  int first = syscall(SYS_dup, directory), second = syscall(SYS_dup, directory);
  say("fd after open and dup", entries(directory) - before);
  close(first);
  close(status);
  say("fd after close", entries(directory) - before);
  close(second);
  close(stat);
  say("fd after all closed", entries(directory) - before);
  close(directory);
  syscall(SYS_mkdirat, AT_FDCWD, DIRECTORY, 0755);
  maps();
  // A copy of itself, which runs by a long name.
  static char program[4 << 20];
  long size = readAll("/proc/self/exe", program, sizeof program);
  int copy = syscall(SYS_openat, AT_FDCWD, COPY, O_CREAT | O_WRONLY | O_TRUNC, 0755);
  for (long done = 0, wrote; done < size && (wrote = write(copy, program + done, size - done)) > 0; done += wrote) {}
  close(copy);
  run(COPY, "named");
  run("/proc/self/exe", "exe");
  syscall(SYS_unlinkat, AT_FDCWD, COPY, 0L);
  syscall(SYS_unlinkat, AT_FDCWD, DIRECTORY, AT_REMOVEDIR);
  return 0;
}
