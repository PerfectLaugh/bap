// What F_GETFL says of how a file was opened, and dup2: of a descriptor to itself, which leaves it as it is, and over one that holds
// a lock, which goes with it as a close would take it.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
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

static long lockOf(int fd, int command, int type) {
  struct flock lock = {0};
  lock.l_type = type;
  lock.l_whence = SEEK_SET;
  lock.l_len = 1;
  if (fcntl(fd, command, &lock) < 0) return -errno;
  return command == F_GETLK ? lock.l_type : 0;
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777, 0, 0, 0);
  int fd = open("/tmp/dup-file", O_RDWR | O_CREAT | O_TRUNC | O_CLOEXEC | O_APPEND, 0644);
  // What stays of the flags: the access and O_APPEND, without what only opening had.
  say("flags", fcntl(fd, F_GETFL) & ~(O_LARGEFILE | 0100000), 0);
  say("dup2 itself", dup2(fd, fd), fcntl(fd, F_GETFD));
  int other = open("/tmp/dup-file", O_RDWR);
  lockOf(other, F_SETLK, F_WRLCK);
  int spare = open("/dev/null", O_RDONLY);
  dup2(spare, other);
  int child = fork();
  if (child == 0) {
    int mine = open("/tmp/dup-file", O_RDWR);
    say("lock after dup2", lockOf(mine, F_GETLK, F_WRLCK), 0);
    _exit(0);
  }
  waitpid(child, 0, 0);
  unlink("/tmp/dup-file");
  return 0;
}
