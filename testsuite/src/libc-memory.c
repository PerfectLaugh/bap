/* What a program can tell of brk, madvise, mremap and shared mappings, as
   qemu runs it too. Each line is one thing that was looked at. */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <semaphore.h>
#include <stdarg.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

#define PAGE 4096

/* printf of %d and %c, which is all that this needs of it. */
static void say(const char *format, ...) {
  char out[128];
  int n = 0;
  va_list args;
  va_start(args, format);
  for (; *format; format++) {
    if (*format != '%') { out[n++] = *format; continue; }
    int value = va_arg(args, int);
    if (*++format == 'c') { out[n++] = value; continue; }
    if (value < 0) { out[n++] = '-'; value = -value; }
    char digits[12];
    int count = 0;
    do { digits[count++] = '0' + value % 10; value /= 10; } while (value);
    while (count) out[n++] = digits[--count];
  }
  va_end(args);
  write(1, out, n);
}
#define printf say

static void break_(void) {
  char *start = (char *)syscall(SYS_brk, 0);
  char *base = (char *)(((unsigned long)start + PAGE - 1) & ~(unsigned long)(PAGE - 1));
  char *grown = (char *)syscall(SYS_brk, base + 3 * PAGE);
  printf("brk grows %d\n", grown == base + 3 * PAGE);
  base[2 * PAGE] = 7;
  printf("brk shrinks %d\n", (char *)syscall(SYS_brk, base + PAGE) == base + PAGE);
  printf("brk regrows %d\n", (char *)syscall(SYS_brk, base + 3 * PAGE) == base + 3 * PAGE);
  printf("brk is zeros %d\n", base[2 * PAGE]);
  printf("brk below stays %d\n", (char *)syscall(SYS_brk, 1) == base + 3 * PAGE);
  syscall(SYS_brk, start);
}

static void fill(int fd, int pages, char byte) {
  char buf[PAGE];
  memset(buf, byte, PAGE);
  for (int i = 0; i < pages; i++) write(fd, buf, PAGE);
}

static void advice(int fd) {
  char *m = mmap(0, 2 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  m[0] = 1; m[PAGE] = 2;
  printf("advice anonymous %d", madvise(m, PAGE, MADV_DONTNEED));
  printf(" %d %d\n", m[0], m[PAGE]);
  m[0] = 3;
  madvise(m, PAGE, MADV_NORMAL);
  printf("advice normal %d\n", m[0]);
  printf("advice unaligned %d %d\n", madvise(m + 1, PAGE, MADV_DONTNEED), errno);
  munmap(m + PAGE, PAGE);
  printf("advice unmapped %d %d\n", madvise(m, 2 * PAGE, MADV_DONTNEED), errno);
  munmap(m, PAGE);

  char *p = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
  p[0] = 'z';
  printf("advice private %c", p[0]);
  madvise(p, PAGE, MADV_DONTNEED);
  printf(" %c\n", p[0]);
  munmap(p, PAGE);

  char *s = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  s[1] = 'q';
  madvise(s, PAGE, MADV_DONTNEED);
  printf("advice shared %c\n", s[1]);
  s[1] = 'a';
  munmap(s, PAGE);
}

static void remap(int fd) {
  char *m = mmap(0, 4 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  m[0] = 1; m[PAGE] = 2; m[3 * PAGE] = 4;
  printf("remap shrinks %d", mremap(m, 4 * PAGE, 2 * PAGE, 0) == m);
  printf(" %d %d\n", m[0], m[PAGE]);
  char *there = mmap(m + 2 * PAGE, PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
  printf("remap blocked %d %d\n", mremap(m, 2 * PAGE, 4 * PAGE, 0) == MAP_FAILED, errno);
  there[0] = 9;
  char *moved = mremap(m, 2 * PAGE, 4 * PAGE, MREMAP_MAYMOVE);
  printf("remap moves %d", moved != m && moved != MAP_FAILED);
  printf(" %d %d %d\n", moved[0], moved[PAGE], moved[3 * PAGE]);
  munmap(there, PAGE);
  munmap(moved + PAGE, 3 * PAGE);
  char *grown = mremap(moved, PAGE, 3 * PAGE, 0);
  printf("remap grows in place %d", grown == moved);
  grown[2 * PAGE] = 5;
  printf(" %d %d\n", grown[0], grown[2 * PAGE]);
  char *room = mmap(0, 4 * PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  char *at = mremap(grown, 3 * PAGE, 3 * PAGE, MREMAP_MAYMOVE | MREMAP_FIXED, room);
  printf("remap to %d %d %d\n", at == room, at[0], at[2 * PAGE]);
  printf("remap no such %d %d\n", mremap(grown, PAGE, 2 * PAGE, MREMAP_MAYMOVE) == MAP_FAILED, errno);
  printf("remap unaligned %d %d\n", mremap(at + 1, PAGE, 2 * PAGE, MREMAP_MAYMOVE) == MAP_FAILED, errno);
  munmap(room, 4 * PAGE);

  char *f = mmap(0, PAGE, PROT_READ, MAP_PRIVATE, fd, 0);
  char *more = mremap(f, PAGE, 2 * PAGE, MREMAP_MAYMOVE);
  printf("remap file %c %c\n", more[0], more[PAGE]);
  munmap(more, 2 * PAGE);
}

static void shared(int fd, const char *path) {
  char b[4] = {0};
  char *s = mmap(0, 2 * PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  s[5] = 'M';
  pread(fd, b, 1, 5);
  printf("shared write reaches the file %c\n", b[0]);
  pwrite(fd, "F", 1, 6);
  printf("shared file reaches memory %c\n", s[6]);
  char *alias = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  alias[7] = 'A';
  s[8] = 'B';
  getpid();
  pread(fd, b, 2, 7);
  printf("shared aliases %c%c %c %c\n", b[0], b[1], s[7], alias[8]);
  munmap(alias, PAGE);
  int in = open(path, O_RDONLY);
  pwrite(fd, "R", 1, 9);
  lseek(in, 9, SEEK_SET);
  read(in, s + 20, 1);
  printf("shared read into itself %c", s[20]);
  pread(fd, b, 1, 20);
  printf(" %c\n", b[0]);
  printf("shared read-only for write %d %d\n", mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, in, 0) == MAP_FAILED, errno);
  char *r = mmap(0, PAGE, PROT_READ, MAP_SHARED, in, 0);
  printf("shared read-only sees %c", r[5]);
  printf(" %d %d\n", mprotect(r, PAGE, PROT_READ | PROT_WRITE), errno);
  munmap(r, PAGE);
  char *priv = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_PRIVATE, in, 0);
  priv[5] = 'P';
  pread(fd, b, 1, 5);
  printf("private stays %c %c\n", priv[5], b[0]);
  munmap(priv, PAGE);
  close(in);
  printf("msync %d\n", msync(s, PAGE, MS_SYNC));
  pid_t child = fork();
  if (!child) {
    s[10] = 'C';
    _exit(s[5] == 'M' ? 0 : 1);
  }
  int status;
  waitpid(child, &status, 0);
  printf("shared child %d %c\n", WEXITSTATUS(status), s[10]);
  s[11] = 'E';
  munmap(s, 2 * PAGE);
  pread(fd, b, 1, 11);
  printf("shared stays in the file %c\n", b[0]);
  char *last = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  ftruncate(fd, 100);
  printf("shared truncated %c %d\n", last[5], last[200]);
  ftruncate(fd, 2 * PAGE);
  printf("shared regrown %d\n", last[200]);
  munmap(last, PAGE);
}

static void together(void) {
  struct { sem_t ping, pong; int value; } *t = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  sem_init(&t->ping, 1, 0);
  sem_init(&t->pong, 1, 0);
  pid_t child = fork();
  if (!child) {
    for (int i = 0; i < 5; i++) {
      sem_wait(&t->ping);
      t->value += 2;
      sem_post(&t->pong);
    }
    _exit(0);
  }
  for (int i = 0; i < 5; i++) {
    t->value += 1;
    sem_post(&t->ping);
    sem_wait(&t->pong);
  }
  int status;
  waitpid(child, &status, 0);
  printf("shared anonymous %d %d\n", t->value, WEXITSTATUS(status));
  munmap(t, PAGE);
  int *x = mmap(0, PAGE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  int *y = mremap(x, 0, PAGE, MREMAP_MAYMOVE);
  *x = 11;
  getpid();
  printf("shared second mapping %d %d\n", y != x, *y);
}

int main(void) {
  break_();
  const char *path = "libc-memory.dat";
  int fd = open(path, O_CREAT | O_RDWR | O_TRUNC, 0644);
  fill(fd, 1, 'a');
  fill(fd, 1, 'b');
  advice(fd);
  remap(fd);
  shared(fd, path);
  close(fd);
  unlink(path);
  together();
  return 0;
}
