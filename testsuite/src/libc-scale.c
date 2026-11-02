/* A workload of what shouldn't take longer each time for what it has already done, as many of it as the second argument says, of the
   kind that the first says. The third, of some, is how much it has before that. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

static char *at[100000];
static char big[65536];
static char list[256];

static int number(const char *s) {
  int v = 0;
  while (*s) v = v * 10 + *s++ - '0';
  return v;
}

__attribute__((noinline)) static int down(int n) {
  volatile int keep = n;
  if (n == 0) return 0;
  int r = down(n - 1);
  return r + keep;
}

static void name_of(char *name, int i) {
  int k = 0;
  name[k++] = 'f';
  do { name[k++] = '0' + i % 10; i /= 10; } while (i);
  name[k] = 0;
}

static void fill(int fd, int size) {
  while (size > 0) {
    int part = size < 65536 ? size : 65536;
    write(fd, big, part);
    size -= part;
  }
}

int main(int c, char **v) {
  char mode = v[1][0], b = 'x', name[16];
  int n = number(v[2]), size = c > 3 ? number(v[3]) : 0, ends[2];
  switch (mode) {
    case 'm': /* mappings, each touched, then all touched again, then gone */
      for (int i = 0; i < n; i++) {
        at[i] = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
        at[i][0] = 1;
      }
      for (int r = 0; r < 20; r++) for (int i = 0; i < n; i++) at[i][1]++;
      for (int i = 0; i < n; i++) munmap(at[i], 4096);
      break;
    case 'b': { /* the break, a page at a time */
      char *start = (char *)syscall(SYS_brk, 0);
      for (int i = 1; i <= n; i++) {
        syscall(SYS_brk, start + i * 4096);
        start[(i - 1) * 4096 + 1] = 1;
      }
      for (int r = 0; r < 20; r++) for (int i = 0; i < n; i++) start[i * 4096 + 1]++;
      break;
    }
    case 'f': /* files */
      for (int i = 0; i < n; i++) {
        name_of(name, i);
        close(open(name, O_CREAT | O_WRONLY, 0644));
      }
      break;
    case 'l': { /* files, and a small read at a time of the directory that has them */
      for (int i = 0; i < n; i++) {
        name_of(name, i);
        close(open(name, O_CREAT | O_WRONLY, 0644));
      }
      int d = open("/", O_RDONLY);
      while (syscall(SYS_getdents64, d, list, sizeof(list)) > 0) {}
      close(d);
      break;
    }
    case 'd': /* calls within calls */
      down(n);
      break;
    case 'g': { /* writes to the end of a file that has this much */
      int fd = open("g", O_CREAT | O_WRONLY | O_APPEND, 0644);
      fill(fd, size);
      for (int i = 0; i < n; i++) write(fd, &b, 1);
      break;
    }
    case 'q': /* reads from a pipe that has this much */
      pipe(ends);
      fill(ends[1], size);
      for (int i = 0; i < n; i++) read(ends[0], &b, 1);
      break;
    case 'c': { /* lines to the console, after this much */
      int fd = 1;
      fill(fd, size);
      for (int i = 0; i < n; i++) write(fd, &b, 1);
      break;
    }
  }
  return 0;
}
