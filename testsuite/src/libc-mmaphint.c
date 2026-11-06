// Where mmap puts a mapping that says where it wants it: MAP_FIXED_NOREPLACE there or not at all, and a hint there if it is free and
// elsewhere if not, for anonymous, shared and file mappings. It says what it found, the same on each target, as equalities rather than
// addresses.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/stat.h>
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

#define PAGE 4096
#define RW (PROT_READ | PROT_WRITE)
#define ANON (MAP_PRIVATE | MAP_ANONYMOUS)

// Whether a call failed with this errno.
static long failed(void *result, int errno_) { return result == MAP_FAILED && errno == errno_; }

int main(void) {
  // Pages that were mapped and aren't, which are free here as they are under Linux.
  char *region = mmap(0, 8 * PAGE, RW, ANON, -1, 0);
  munmap(region, 8 * PAGE);

  char *at = mmap(region, PAGE, RW, ANON | MAP_FIXED_NOREPLACE, -1, 0);
  say("noreplace anonymous at the address", 1, at == region, 0, 0);
  at[0] = 7;
  say("noreplace over a mapping is EEXIST", 1, failed(mmap(region, PAGE, RW, ANON | MAP_FIXED_NOREPLACE, -1, 0), EEXIST), 0, 0);
  say("noreplace over part of one is EEXIST", 1,
      failed(mmap(region - PAGE, 2 * PAGE, RW, ANON | MAP_FIXED_NOREPLACE, -1, 0), EEXIST), 0, 0);
  say("noreplace off a page is EINVAL", 1, failed(mmap(region + PAGE + 1, PAGE, RW, ANON | MAP_FIXED_NOREPLACE, -1, 0), EINVAL), 0, 0);
  say("noreplace shared at the address", 1,
      mmap(region + PAGE, PAGE, RW, MAP_SHARED | MAP_ANONYMOUS | MAP_FIXED_NOREPLACE, -1, 0) == region + PAGE, 0, 0);

  char *hint = mmap(region + 2 * PAGE, PAGE, RW, ANON, -1, 0);
  say("hint anonymous", 1, hint == region + 2 * PAGE, 0, 0);
  hint = mmap(region + 3 * PAGE, PAGE, RW, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  say("hint shared", 1, hint == region + 3 * PAGE, 0, 0);
  hint = mmap(region + 4 * PAGE + 100, PAGE, RW, ANON, -1, 0);
  say("hint off a page is its page", 1, hint == region + 4 * PAGE, 0, 0);

  syscall(SYS_mkdirat, AT_FDCWD, "mmaphint-dir", 0700);
  int fd = open("mmaphint-dir/file", O_RDWR | O_CREAT | O_TRUNC, 0600);
  char bytes[PAGE];
  for (int index = 0; index < PAGE; index++) bytes[index] = (char)(index % 251);
  write(fd, bytes, PAGE);
  char *file = mmap(region + 5 * PAGE, PAGE, PROT_READ, MAP_PRIVATE, fd, 0);
  say("hint file", 2, file == region + 5 * PAGE, file[1000] == bytes[1000], 0);
  file = mmap(region + 6 * PAGE, PAGE, PROT_READ, MAP_SHARED | MAP_FIXED_NOREPLACE, fd, 0);
  say("noreplace file at the address", 2, file == region + 6 * PAGE, file[2000] == bytes[2000], 0);
  say("noreplace file over a mapping is EEXIST", 1,
      failed(mmap(region + 6 * PAGE, PAGE, PROT_READ, MAP_SHARED | MAP_FIXED_NOREPLACE, fd, 0), EEXIST), 0, 0);
  char *busy = mmap(region + 6 * PAGE, PAGE, PROT_READ, MAP_PRIVATE, fd, 0);
  say("hint file over a mapping is not the hint", 1, busy != MAP_FAILED && busy != region + 6 * PAGE, 0, 0);
  close(fd);
  unlink("mmaphint-dir/file");
  syscall(SYS_unlinkat, AT_FDCWD, "mmaphint-dir", AT_REMOVEDIR);

  busy = mmap(region, PAGE, RW, ANON, -1, 0);
  say("hint over a mapping is not the hint", 1, busy != MAP_FAILED && busy != region, 0, 0);
  say("what noreplace mapped is kept", 1, at[0], 0, 0);
  char *fixed = mmap(region, PAGE, RW, ANON | MAP_FIXED, -1, 0);
  say("fixed over a mapping at the address", 2, fixed == region, fixed[0], 0);
  return 0;
}
