// What goes from one file to another, and files of memory: memfd_create and its seals, O_TMPFILE, sendfile, splice, tee and
// copy_file_range, with a splice that waits for what a child writes. It says what it found, the same on each target. The libc of the
// tests has none of these calls, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <time.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

#ifdef SYS_sendfile64
#define SENDFILE SYS_sendfile64
#else
#define SENDFILE SYS_sendfile
#endif

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
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

// A label and what was read, as text.
static void sayText(const char *label, const char *text, long size) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  for (long index = 0; index < size; index++) line[n++] = text[index];
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

static long fcntlOf(int fd, int command, long value) { return call(SYS_fcntl, fd, command, value, 0, 0, 0); }

static long sizeOf(int fd) { return lseek(fd, 0, SEEK_END); }

static void readBack(const char *label, int fd, long offset) {
  char buffer[64];
  long got = pread(fd, buffer, sizeof buffer, offset);
  if (got < 0) say(label, 1, -errno, 0, 0);
  else sayText(label, buffer, got);
}

static void readPipe(const char *label, int fd) {
  char buffer[64];
  long got = read(fd, buffer, sizeof buffer);
  if (got < 0) say(label, 1, -errno, 0, 0);
  else sayText(label, buffer, got);
}

int main(void) {
  // A file of memory that can have seals.
  int memory = (int)call(SYS_memfd_create, (long)"copy", MFD_CLOEXEC | MFD_ALLOW_SEALING, 0, 0, 0, 0);
  say("memfd", 2, memory >= 0, fcntlOf(memory, F_GETFD, 0), 0);
  say("write", 1, write(memory, "hello world", 11), 0, 0);
  say("seals", 1, fcntlOf(memory, F_GET_SEALS, 0), 0, 0);
  say("ftruncate", 2, ftruncate(memory, 20), sizeOf(memory), 0);
  say("add shrink grow", 2, fcntlOf(memory, F_ADD_SEALS, F_SEAL_SHRINK | F_SEAL_GROW), fcntlOf(memory, F_GET_SEALS, 0), 0);
  say("shrink", 1, ftruncate(memory, 10) < 0 ? -errno : 0, 0, 0);
  say("grow", 1, ftruncate(memory, 30) < 0 ? -errno : 0, 0, 0);
  say("pwrite inside", 1, pwrite(memory, "HE", 2, 0), 0, 0);
  say("pwrite past", 1, pwrite(memory, "xyz", 3, 19) < 0 ? -errno : 0, 0, 0);
  lseek(memory, 20, SEEK_SET);
  say("write past", 1, write(memory, "!", 1) < 0 ? -errno : 0, 0, 0);
  readBack("memfd holds", memory, 0);
  say("add write", 2, fcntlOf(memory, F_ADD_SEALS, F_SEAL_WRITE), fcntlOf(memory, F_GET_SEALS, 0), 0);
  say("write sealed", 1, pwrite(memory, "h", 1, 0) < 0 ? -errno : 0, 0, 0);
  void *mapped = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, memory, 0);
  say("map sealed", 1, mapped == MAP_FAILED ? -errno : 0, 0, 0);
  mapped = mmap(0, 4096, PROT_READ, MAP_SHARED, memory, 0);
  say("map to read", 2, mapped != MAP_FAILED, mapped != MAP_FAILED && ((char *)mapped)[1] == 'E', 0);
  say("add seal", 2, fcntlOf(memory, F_ADD_SEALS, F_SEAL_SEAL), fcntlOf(memory, F_ADD_SEALS, F_SEAL_SHRINK), 0);
  say("bad seal", 1, fcntlOf(memory, F_ADD_SEALS, 0x100), 0, 0);

  // One that can't, one whose mapping writes it, and a file of the tree.
  int plain = (int)call(SYS_memfd_create, (long)"plain", 0, 0, 0, 0, 0);
  say("unsealable", 2, fcntlOf(plain, F_GET_SEALS, 0), fcntlOf(plain, F_ADD_SEALS, F_SEAL_GROW), 0);
  say("bad flags", 1, call(SYS_memfd_create, (long)"bad", 0x100, 0, 0, 0, 0), 0, 0);
  int busy = (int)call(SYS_memfd_create, (long)"busy", MFD_ALLOW_SEALING, 0, 0, 0, 0);
  ftruncate(busy, 4096);
  char *writable = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, busy, 0);
  writable[0] = 'w';
  say("busy", 1, fcntlOf(busy, F_ADD_SEALS, F_SEAL_WRITE), 0, 0);
  munmap(writable, 4096);
  say("unmapped", 1, fcntlOf(busy, F_ADD_SEALS, F_SEAL_WRITE), 0, 0);
  readBack("mapping wrote", busy, 0);

  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777);
  int source = open("/tmp/copy-source", O_RDWR | O_CREAT | O_TRUNC, 0644);
  write(source, "0123456789abcdef", 16);
  lseek(source, 0, SEEK_SET);

  // sendfile: from an offset that it moves, and from where the file is.
  int pipes[2];
  pipe(pipes);
  say("pipe seals", 1, fcntlOf(pipes[0], F_GET_SEALS, 0), 0, 0);
  long long offset = 4;
  say("sendfile", 2, call(SENDFILE, pipes[1], source, (long)&offset, 6, 0, 0), (long)offset, 0);
  say("offset kept", 1, lseek(source, 0, SEEK_CUR), 0, 0);
  readPipe("sendfile pipe", pipes[0]);
  int target = open("/tmp/copy-target", O_RDWR | O_CREAT | O_TRUNC, 0644);
  say("sendfile file", 2, call(SENDFILE, target, source, 0, 100, 0, 0), lseek(source, 0, SEEK_CUR), 0);
  readBack("target", target, 0);
  say("sendfile end", 1, call(SENDFILE, target, source, 0, 100, 0, 0), 0, 0);
  say("sendfile bad", 1, call(SENDFILE, 99, source, 0, 1, 0, 0), 0, 0);

  // splice, of which one end is a pipe.
  write(pipes[1], "splice!", 7);
  long long at = 2;
  say("splice to file", 2, call(SYS_splice, pipes[0], 0, target, (long)&at, 100, 0), (long)at, 0);
  readBack("spliced", target, 0);
  at = 10;
  say("splice from file", 2, call(SYS_splice, source, (long)&at, pipes[1], 0, 3, 0), (long)at, 0);
  readPipe("splice pipe", pipes[0]);
  say("splice files", 1, call(SYS_splice, source, 0, target, 0, 1, 0), 0, 0);
  say("splice offset", 1, call(SYS_splice, pipes[0], (long)&at, target, 0, 1, 0), 0, 0);
  say("splice empty", 1, call(SYS_splice, pipes[0], 0, target, 0, 1, SPLICE_F_NONBLOCK), 0, 0);

  // tee, which leaves what it copies.
  int others[2];
  pipe(others);
  write(pipes[1], "teedata", 7);
  say("tee", 1, call(SYS_tee, pipes[0], others[1], 100, 0, 0, 0), 0, 0);
  readPipe("tee copy", others[0]);
  readPipe("tee kept", pipes[0]);
  say("tee same", 1, call(SYS_tee, pipes[0], pipes[1], 1, 0, 0, 0), 0, 0);
  say("tee file", 1, call(SYS_tee, source, others[1], 1, 0, 0, 0), 0, 0);
  say("tee empty", 1, call(SYS_tee, pipes[0], others[1], 1, SPLICE_F_NONBLOCK, 0, 0), 0, 0);

  // copy_file_range, from offsets and from where the files are.
  long long from = 10, to = 0;
  say("copy", 3, call(SYS_copy_file_range, source, (long)&from, target, (long)&to, 4, 0), (long)from, (long)to);
  readBack("copied", target, 0);
  lseek(source, 0, SEEK_SET);
  lseek(target, 12, SEEK_SET);
  say("copy positions", 3, call(SYS_copy_file_range, source, 0, target, 0, 3, 0), lseek(source, 0, SEEK_CUR), lseek(target, 0, SEEK_CUR));
  readBack("copied again", target, 0);
  say("copy flags", 1, call(SYS_copy_file_range, source, 0, target, 0, 1, 1), 0, 0);
  from = 0; to = 2;
  say("copy overlap", 1, call(SYS_copy_file_range, source, (long)&from, source, (long)&to, 4, 0), 0, 0);
  int appending = open("/tmp/copy-target", O_WRONLY | O_APPEND);
  say("copy append", 1, call(SYS_copy_file_range, source, 0, appending, 0, 1, 0), 0, 0);
  int directory = open("/tmp", O_RDONLY | O_DIRECTORY);
  say("copy directory", 1, call(SYS_copy_file_range, directory, 0, target, 0, 1, 0), 0, 0);
  say("copy pipe", 1, call(SYS_copy_file_range, pipes[0], 0, target, 0, 1, 0), 0, 0);

  // O_TMPFILE: a file of no name in a directory.
  int unnamed = open("/tmp", O_TMPFILE | O_RDWR, 0600);
  say("tmpfile", 1, unnamed >= 0, 0, 0);
  write(unnamed, "nameless", 8);
  readBack("tmpfile holds", unnamed, 0);
  say("tmpfile read only", 1, open("/tmp", O_TMPFILE | O_RDONLY, 0600) < 0 ? -errno : 0, 0, 0);
  say("tmpfile missing", 1, open("/tmp/none", O_TMPFILE | O_RDWR, 0600) < 0 ? -errno : 0, 0, 0);
  say("tmpfile file", 1, open("/tmp/copy-source", O_TMPFILE | O_RDWR, 0600) < 0 ? -errno : 0, 0, 0);

  // A splice that waits for what a child writes, and one that has nothing to wait for.
  int waits[2];
  pipe(waits);
  int child = fork();
  if (child == 0) {
    close(waits[0]);
    struct timespec pause = {0, 20000000};
    nanosleep(&pause, 0);
    write(waits[1], "late", 4);
    _exit(0);
  }
  close(waits[1]);
  at = 0;
  say("splice waited", 1, call(SYS_splice, waits[0], 0, target, (long)&at, 100, 0), 0, 0);
  readBack("late", target, 0);
  waitpid(child, 0, 0);
  say("splice ended", 1, call(SYS_splice, waits[0], 0, target, 0, 100, 0), 0, 0);
  unlink("/tmp/copy-source");
  unlink("/tmp/copy-target");
  return 0;
}
