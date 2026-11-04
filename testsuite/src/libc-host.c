// What a program finds in a directory of the host that the machine sees at /host: its names, its files and a link in it, what a
// write changes, which the host doesn't see, and what an unlink takes away, which doesn't come back.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b, long c) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
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

static void sayText(const char *label, const char *text) {
  unsigned long n = 0;
  while (label[n]) n++;
  write(1, label, n);
  write(1, " ", 1);
  n = 0;
  while (text[n]) n++;
  write(1, text, n);
  write(1, "\n", 1);
}

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

static long removeFile(const char *path) { return call(SYS_unlinkat, AT_FDCWD, (long)path, 0, 0, 0); }

static void put(const char *path, const char *text) {
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  unsigned long n = 0;
  while (text[n]) n++;
  write(fd, text, n);
  close(fd);
}

// What a file holds, or the error of opening it.
static void show(const char *label, const char *path) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) { say(label, 1, -errno, 0, 0); return; }
  char buffer[64];
  long got = read(fd, buffer, sizeof buffer - 1);
  close(fd);
  buffer[got < 0 ? 0 : got] = 0;
  sayText(label, buffer);
}

// The names of a directory, in order.
static void names(const char *label, const char *path) {
  int fd = open(path, O_RDONLY | O_DIRECTORY);
  if (fd < 0) { say(label, 1, -errno, 0, 0); return; }
  char buffer[2048] __attribute__((aligned(8)));
  char *found[32];
  int count = 0;
  long got;
  while ((got = call(SYS_getdents64, fd, (long)buffer, sizeof buffer, 0, 0)) > 0) {
    for (long at = 0; at < got;) {
      unsigned short length = *(unsigned short *)(buffer + at + 16);
      char *name = buffer + at + 19;
      if (count < 32 && !(name[0] == '.' && (name[1] == 0 || (name[1] == '.' && name[2] == 0)))) {
        unsigned long size = 0;
        while (name[size]) size++;
        static char kept[32][64];
        for (unsigned long index = 0; index <= size && index < 63; index++) kept[count][index] = name[index];
        found[count] = kept[count];
        count++;
      }
      at += length;
    }
  }
  close(fd);
  for (int i = 0; i < count; i++)
    for (int j = i + 1; j < count; j++) {
      int k = 0;
      while (found[i][k] && found[i][k] == found[j][k]) k++;
      if ((unsigned char)found[i][k] > (unsigned char)found[j][k]) { char *t = found[i]; found[i] = found[j]; found[j] = t; }
    }
  char line[512];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  for (int i = 0; i < count; i++) {
    line[n++] = ' ';
    for (int k = 0; found[i][k]; k++) line[n++] = found[i][k];
  }
  line[n++] = '\n';
  write(1, line, n);
}

int main(void) {
  names("names", "/host");
  show("a", "/host/a.txt");
  show("b", "/host/sub/b.txt");
  char target[64];
  long size = call(SYS_readlinkat, AT_FDCWD, (long)"/host/link", (long)target, sizeof target - 1, 0);
  target[size < 0 ? 0 : size] = 0;
  sayText("link", target);
  show("through the link", "/host/link");
  put("/host/a.txt", "changed");
  show("written", "/host/a.txt");
  say("unlink", 1, removeFile("/host/sub/b.txt"), 0, 0);
  show("unlinked", "/host/sub/b.txt");
  names("sub", "/host/sub");
  show("missing", "/host/none");
  put("/host/new", "new");
  names("names after", "/host");
  return 0;
}
