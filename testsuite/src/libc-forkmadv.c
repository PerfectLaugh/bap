// madvise for a fork: MADV_WIPEONFORK makes a private anonymous range zeros in a child, which MADV_KEEPONFORK undoes, and of anything
// else is EINVAL; MADV_DONTFORK leaves a range out of a child, which MADV_DOFORK undoes. Both are of the mapping, so mprotect and mremap
// keep them and munmap drops them, a child keeps the wipe for its own children, a child of vfork has the memory as it is, and a program
// that runs has none. It says what it found, the same on each target. The libc of the tests has no execve, so it is called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
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

// What a child of fork finds, as its status: a byte of it, or 255 if the page isn't mapped there, as msync says of a page that isn't.
static int inChild(volatile char *page) {
  pid_t child = fork();
  if (child == 0) {
    if (msync((void *)page, PAGE, MS_ASYNC) != 0) _exit(errno == ENOMEM ? 255 : 254);
    _exit(page[0]);
  }
  int status = 0;
  waitpid(child, &status, 0);
  return WEXITSTATUS(status);
}

// Whether a call failed with this errno.
static long failed(int result, int errno_) { return result == -1 && errno == errno_; }

// The digits of a number, and the number of digits.
static void digits(unsigned long value, char *out) {
  char reversed[24];
  int count = 0;
  do { reversed[count++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (count) *out++ = reversed[--count];
  *out = 0;
}

int main(int argc, char **argv) {
  if (argc > 2) {
    // A program that runs has none of it: the same address, mapped again, is the child's as it is the parent's.
    unsigned long address = 0;
    for (char *digit = argv[2]; *digit; digit++) address = address * 10 + (unsigned long)(*digit - '0');
    volatile char *page = mmap((void *)address, PAGE, RW, ANON | MAP_FIXED_NOREPLACE, -1, 0);
    if (page != (void *)address) { say("the program can't map the address", 0, 0, 0); return 1; }
    page[0] = 9;
    say("a program that runs doesn't wipe", 1, inChild(page), 0);
    return 0;
  }

  volatile char *page = mmap(0, 4 * PAGE, RW, ANON, -1, 0);
  page[0] = 9;
  page[PAGE] = 9;
  say("wipeonfork", 1, madvise((void *)page, PAGE, MADV_WIPEONFORK), 0);
  say("the child reads", 1, inChild(page), 0);
  say("the parent still has", 1, page[0], 0);
  say("the next page isn't wiped", 1, inChild(page + PAGE), 0);

  // A child keeps it for its own children, and one of vfork has the memory itself.
  pid_t child = fork();
  if (child == 0) {
    page[0] = 5;
    _exit(inChild(page) * 10 + page[0]);
  }
  int status = 0;
  waitpid(child, &status, 0);
  say("a grandchild reads, and the child has", 2, WEXITSTATUS(status) / 10, WEXITSTATUS(status) % 10);
  child = vfork();
  if (child == 0) _exit(page[0]);
  waitpid(child, &status, 0);
  say("a child of vfork reads", 1, WEXITSTATUS(status), 0);

  // mprotect and mremap keep it.
  mprotect((void *)page, PAGE, PROT_READ);
  say("after mprotect the child reads", 1, inChild(page), 0);
  mprotect((void *)page, PAGE, RW);
  volatile char *moved = mmap(0, 2 * PAGE, RW, ANON, -1, 0);
  munmap((void *)moved, 2 * PAGE);
  moved = mremap((void *)page, PAGE, PAGE, MREMAP_MAYMOVE | MREMAP_FIXED, (void *)moved);
  say("moved, the parent has", 1, moved[0], 0);
  say("and the child reads", 1, inChild(moved), 0);
  mremap((void *)moved, PAGE, PAGE, MREMAP_MAYMOVE | MREMAP_FIXED, (void *)page);

  say("keeponfork", 1, madvise((void *)page, PAGE, MADV_KEEPONFORK), 0);
  say("the child reads", 1, inChild(page), 0);

  // munmap drops it: what is mapped there again is whole in a child.
  madvise((void *)page, PAGE, MADV_WIPEONFORK);
  munmap((void *)page, PAGE);
  mmap((void *)page, PAGE, RW, ANON | MAP_FIXED, -1, 0);
  page[0] = 9;
  say("mapped again, the child reads", 1, inChild(page), 0);

  // Only of what is private and anonymous.
  void *shared = mmap(0, PAGE, RW, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  say("wipeonfork of a shared mapping is EINVAL", 1, failed(madvise(shared, PAGE, MADV_WIPEONFORK), EINVAL), 0);
  syscall(SYS_mkdirat, AT_FDCWD, "forkmadv.dir", 0700);
  int fd = open("forkmadv.dir/file", O_RDWR | O_CREAT | O_TRUNC, 0600);
  ftruncate(fd, PAGE);
  void *file = mmap(0, PAGE, RW, MAP_PRIVATE, fd, 0);
  say("a file is mapped", 1, file != MAP_FAILED, 0);
  say("wipeonfork of a file mapping is EINVAL", 1, failed(madvise(file, PAGE, MADV_WIPEONFORK), EINVAL), 0);
  close(fd);
  unlink("forkmadv.dir/file");
  syscall(SYS_unlinkat, AT_FDCWD, "forkmadv.dir", AT_REMOVEDIR);

  // DONTFORK: the child hasn't got it, and the parent goes on with it.
  say("dontfork", 1, madvise((void *)(page + 2 * PAGE), PAGE, MADV_DONTFORK), 0);
  page[2 * PAGE] = 9;
  page[3 * PAGE] = 9;
  say("the child finds it unmapped", 1, inChild(page + 2 * PAGE) == 255, 0);
  say("the parent still has", 1, page[2 * PAGE], 0);
  say("the next page is in the child", 1, inChild(page + 3 * PAGE), 0);
  say("dofork", 1, madvise((void *)(page + 2 * PAGE), PAGE, MADV_DOFORK), 0);
  say("the child reads", 1, inChild(page + 2 * PAGE), 0);
  say("dontfork of a shared mapping", 1, madvise(shared, PAGE, MADV_DONTFORK), 0);
  *(volatile char *)shared = 9;
  say("the child finds it unmapped", 1, inChild(shared) == 255, 0);

  // A program that runs has none of it, at the address that had it.
  madvise((void *)page, PAGE, MADV_WIPEONFORK);
  char address[24];
  digits((unsigned long)page, address);
  child = fork();
  if (child == 0) {
    char *arguments[] = {argv[0], "program", address, 0};
    char *environment[] = {0};
    syscall(SYS_execve, argv[0], arguments, environment);
    _exit(1);
  }
  waitpid(child, &status, 0);
  say("and it ended with", 1, WEXITSTATUS(status), 0);
  return 0;
}
