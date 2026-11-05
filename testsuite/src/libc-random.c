// getrandom, whose bytes go on from call to call and from a process to the one it forks, as those of Linux do. It says what it found,
// the same on each target and never the bytes themselves. The libc of the tests has no getrandom, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <stddef.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#define GRND_NONBLOCK 1

static long random_bytes(void *buffer, long count, long flags) {
  long result = syscall(SYS_getrandom, buffer, count, flags);
  return result < 0 ? -errno : result;
}

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

int main(void) {
  unsigned char first[16], second[16], big[32];
  say("first", random_bytes(first, 16, 0));
  say("second", random_bytes(second, 16, 0));
  say("differ", memcmp(first, second, 16) != 0);
  say("none", random_bytes(first, 0, 0));
  say("big", random_bytes(big, 32, 0));
  say("nonblock", random_bytes(first, 16, GRND_NONBLOCK));
  say("fault", random_bytes((void *)8, 16, 0));

  int pipes[2];
  if (pipe(pipes) != 0) return 1;
  pid_t child = fork();
  if (child == 0) {
    unsigned char mine[16];
    long got = random_bytes(mine, 16, 0);
    write(pipes[1], mine, 16);
    _exit(got == 16 ? 0 : 1);
  }
  unsigned char theirs[16], mine[16];
  long read_count = read(pipes[0], theirs, 16);
  int status = 0;
  waitpid(child, &status, 0);
  say("child", read_count == 16 && WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  say("parent", random_bytes(mine, 16, 0));
  say("forked differ", memcmp(theirs, mine, 16) != 0);
  return 0;
}
