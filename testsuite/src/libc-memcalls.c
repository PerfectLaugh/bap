// What a program asks of its memory besides mapping it: msync, the locks of mlock and its kin, mincore, membarrier, and madvise of
// huge pages. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <sys/mman.h>
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

static long call(long number, long a, long b, long c) {
  long result = syscall(number, a, b, c, 0L, 0L, 0L);
  return result < 0 ? -errno : result;
}

int main(void) {
  char *memory = mmap(0, 4 * 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  for (int page = 0; page < 4; page++) memory[page * 4096] = 1;
  long at = (long)memory;
  munmap(memory + 3 * 4096, 4096);

  say("msync", 3, call(SYS_msync, at, 4096, MS_SYNC), call(SYS_msync, at + 1, 4096, MS_SYNC),
      call(SYS_msync, at, 4096, MS_SYNC | MS_ASYNC));
  say("msync unmapped", 2, call(SYS_msync, at, 4 * 4096, MS_ASYNC), call(SYS_msync, at, 4096, 8), 0);

  say("mlock", 3, call(SYS_mlock, at, 8192, 0), call(SYS_munlock, at, 8192, 0), call(SYS_mlock, at, 4 * 4096, 0));
  say("mlock2", 2, call(SYS_mlock2, at, 4096, MLOCK_ONFAULT), call(SYS_mlock2, at, 4096, 2), 0);
  say("munlock", 1, call(SYS_munlock, at, 4096, 0), 0, 0);
  say("mlockall", 3, call(SYS_mlockall, 0, 0, 0), call(SYS_mlockall, MCL_ONFAULT, 0, 0), call(SYS_munlockall, 0, 0, 0));

  unsigned char resident[4] = {9, 9, 9, 9};
  say("mincore", 1, call(SYS_mincore, at, 3 * 4096, (long)resident), 0, 0);
  say("resident", 3, resident[0], resident[1], resident[2]);
  say("mincore wrong", 2, call(SYS_mincore, at + 1, 4096, (long)resident), call(SYS_mincore, at, 4 * 4096, (long)resident), 0);

  long query = call(SYS_membarrier, 0, 0, 0);
  say("membarrier query", 2, query > 0, (query & 0x18) == 0x18, 0);
  say("private before", 1, call(SYS_membarrier, 8, 0, 0), 0, 0);
  say("register", 2, call(SYS_membarrier, 16, 0, 0), call(SYS_membarrier, 8, 0, 0), 0);
  say("wrong", 2, call(SYS_membarrier, 1 << 20, 0, 0), call(SYS_membarrier, 0, 1, 0), 0);

  say("madvise", 3, call(SYS_madvise, at, 4096, MADV_WILLNEED), call(SYS_madvise, at, 4096, MADV_NOHUGEPAGE),
      call(SYS_madvise, at, 4096, 999));
  say("madvise unmapped", 1, call(SYS_madvise, at, 4 * 4096, MADV_WILLNEED), 0, 0);
  return 0;
}
