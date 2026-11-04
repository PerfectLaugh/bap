// What /proc/self/stat says of the heap, in the field of start_brk among 52, and what /proc/self/status says of the umask.
#define _GNU_SOURCE
#include <fcntl.h>
#include <sys/stat.h>
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

static long readAll(const char *path, char *buffer, long size) {
  int fd = open(path, O_RDONLY);
  long got = read(fd, buffer, size - 1);
  close(fd);
  buffer[got < 0 ? 0 : got] = 0;
  return got;
}

int main(void) {
  unsigned long start = (unsigned long)syscall(SYS_brk, 0L, 0L, 0L, 0L, 0L, 0L);
  char text[1024];
  readAll("/proc/self/stat", text, sizeof text);
  // Fields after the name, which ends at the last ')'.
  char *at = text;
  for (char *p = text; *p; p++) if (*p == ')') at = p + 1;
  int field = 2;
  unsigned long brk = 0;
  for (char *p = at; *p && *p != '\n'; p++) {
    if (*p == ' ') {
      field++;
      if (field == 47) { brk = 0; for (char *q = p + 1; *q >= '0' && *q <= '9'; q++) brk = brk * 10 + (unsigned long)(*q - '0'); }
    }
  }
  say("fields", field, brk == start);
  syscall(SYS_umask, 027L, 0L, 0L, 0L, 0L, 0L);
  readAll("/proc/self/status", text, sizeof text);
  int found = 0;
  for (char *p = text; *p; p++)
    if (p[0] == 'U' && p[1] == 'm' && p[2] == 'a' && p[3] == 's' && p[4] == 'k') found = p[7] == '0' && p[8] == '0' && p[9] == '2' && p[10] == '7';
  say("umask", found, 0);
  return 0;
}
