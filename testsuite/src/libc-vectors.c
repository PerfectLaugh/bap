// readv and writev of what isn't a file: a terminal, an eventfd and a timerfd, as stdio uses them.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/ioctl.h>
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

int main(void) {
  int master = open("/dev/ptmx", O_RDWR | O_NOCTTY);
  int unlock = 0;
  ioctl(master, 0x40045431, &unlock);
  int number = -1;
  ioctl(master, 0x80045430, &number);
  char name[32] = "/dev/pts/";
  int at = 9;
  if (number >= 10) name[at++] = (char)('0' + number / 10);
  name[at++] = (char)('0' + number % 10);
  name[at] = 0;
  int slave = open(name, O_RDWR | O_NOCTTY);
  struct iovec out[2] = {{"he", 2}, {"llo\n", 4}};
  say("writev master", writev(master, out, 2), 0);
  char first[3] = {0}, second[16] = {0};
  struct iovec in[2] = {{first, 0}, {second, sizeof second}};
  long got = readv(slave, in, 2);
  say("readv slave", got, second[0] == 'h' && second[5] == '\n');
  int counter = (int)syscall(SYS_eventfd2, 0, 0);
  unsigned long long add = 5, value = 0;
  struct iovec one = {&add, 8}, back = {&value, 8};
  say("writev eventfd", writev(counter, &one, 1), 0);
  say("readv eventfd", readv(counter, &back, 1), (long)value);
  int timer = (int)syscall(SYS_timerfd_create, 1, 0);
  long wrote = write(timer, &add, 8);
  say("write timerfd", wrote < 0 ? -errno : wrote, 0);
  wrote = writev(timer, &one, 1);
  say("writev timerfd", wrote < 0 ? -errno : wrote, 0);
  return 0;
}
