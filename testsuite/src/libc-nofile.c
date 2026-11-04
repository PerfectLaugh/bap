// RLIMIT_NOFILE is kept to before a call does anything: an open that would make a file past it makes none, a pipe needs room for two,
// and dup2, dup3 and F_DUPFD to or from past it are wrong.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/resource.h>
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

static long call(long number, long a, long b, long c) {
  long result = syscall(number, a, b, c, 0L, 0L, 0L);
  return result < 0 ? -errno : result;
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777, 0, 0, 0);
  struct rlimit ten = {10, 4096};
  setrlimit(RLIMIT_NOFILE, &ten);
  // 0 to 2 are open; 3 to 8 are made, and 9 is left.
  for (int fd = 3; fd < 9; fd++) open("/dev/null", O_RDONLY);
  int pipes[2];
  say("pipe with one left", pipe(pipes) < 0 ? -errno : 0, 0);
  say("last", open("/dev/null", O_RDONLY), 0);
  say("open past", open("/tmp/nofile-made", O_WRONLY | O_CREAT, 0644) < 0 ? -errno : 0,
      call(SYS_faccessat, AT_FDCWD, (long)"/tmp/nofile-made", 0));
  say("dup2 past", call(SYS_dup3, 0, 10, 0), call(SYS_dup3, 0, 5, 0));
  say("F_DUPFD from past", call(SYS_fcntl, 0, F_DUPFD, 10), call(SYS_fcntl, 0, F_DUPFD, 5));
  close(5);
  say("F_DUPFD with room", call(SYS_fcntl, 0, F_DUPFD, 3), 0);
  return 0;
}
