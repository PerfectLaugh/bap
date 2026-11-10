// What the taint of a machine says of memory that a call fills that isn't of the world (testLinuxTaintMoves): of `exec`, the program
// that execve runs, whose constants come from nothing; of `mremap`, bytes of a file that a mapping moves with, which still come from it;
// of `append`, bytes of a file that pwrite wrote to one opened to append, which go to its end, whatever pwrite says, and come back from
// there; of `rwfappend`, the same of pwritev2 with RWF_APPEND; and of `sendfile`, `splice`, `tee` and `copy`, bytes that the kernel
// copied from a file or a pipe to another, which come from what they were copied from.
// Each says where what it is about is, and then works, for the test to look there.
#define _GNU_SOURCE
#include <fcntl.h>
#include <sys/sendfile.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

static const char marker[16] = "a constant here";

static void hold(void) {
  for (;;) {
  }
}

int main(int argc, char **argv) {
  setvbuf(stdout, 0, _IONBF, 0);
  if (argc > 1 && strcmp(argv[1], "exec") == 0) {
    char *arguments[] = {argv[0], "marker", 0};
    execve(argv[0], arguments, 0);
    return 1;
  }
  if (argc > 1 && strcmp(argv[1], "marker") == 0) {
    printf("%lx\n", (unsigned long)marker);
    hold();
  }
  if (argc > 1 && strcmp(argv[1], "mremap") == 0) {
    char *block = mmap(0, 65536, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    // What is after it keeps it from growing where it is, so that it moves.
    mmap(block + 65536, 4096, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0);
    int fd = open("/data", O_RDONLY);
    pread(fd, block, 16, 0);
    char *moved = mremap(block, 65536, 131072, MREMAP_MAYMOVE);
    printf("%lx %d\n", (unsigned long)moved, moved != block);
    hold();
  }
  if (argc > 1 && strcmp(argv[1], "append") == 0) {
    static char from[16], back[16];
    int data = open("/data", O_RDONLY);
    pread(data, from, 16, 0);
    int log = open("/log", O_CREAT | O_WRONLY | O_APPEND, 0644);
    write(log, "abcd", 4);
    pwrite(log, from, 4, 0);
    int again = open("/log", O_RDONLY);
    pread(again, back, 4, 4);
    printf("%lx %d\n", (unsigned long)back, memcmp(back, from, 4) == 0);
    hold();
  }
  if (argc > 1 && strcmp(argv[1], "rwfappend") == 0) {
    static char from[16], back[16];
    int data = open("/data", O_RDONLY);
    pread(data, from, 16, 0);
    int log = open("/log", O_CREAT | O_RDWR, 0644);
    write(log, "abcd", 4);
    struct iovec piece = {from, 4};
    pwritev2(log, &piece, 1, 0, RWF_APPEND);
    pread(log, back, 4, 4);
    printf("%lx %d\n", (unsigned long)back, memcmp(back, from, 4) == 0);
    hold();
  }
  if (argc > 1 && (strcmp(argv[1], "sendfile") == 0 || strcmp(argv[1], "splice") == 0 || strcmp(argv[1], "tee") == 0 ||
                   strcmp(argv[1], "copy") == 0)) {
    static char from[16], back[16];
    int data = open("/data", O_RDONLY);
    pread(data, from, 16, 0);
    int log = open("/log", O_CREAT | O_RDWR | O_TRUNC, 0644);
    write(log, from, 16);
    int copy = open("/copy", O_CREAT | O_RDWR | O_TRUNC, 0644);
    if (strcmp(argv[1], "sendfile") == 0) {
      off_t at = 0;
      sendfile(copy, log, &at, 16);
      pread(copy, back, 16, 0);
    } else if (strcmp(argv[1], "copy") == 0) {
      loff_t in = 0, out = 0;
      syscall(SYS_copy_file_range, log, &in, copy, &out, 16, 0);
      pread(copy, back, 16, 0);
    } else {
      int first[2], second[2];
      pipe(first);
      pipe(second);
      write(first[1], from, 16);
      if (strcmp(argv[1], "splice") == 0) {
        splice(first[0], 0, copy, 0, 16, 0);
        pread(copy, back, 16, 0);
      } else {
        tee(first[0], second[1], 16, 0);
        read(second[0], back, 16);
      }
    }
    printf("%lx %d\n", (unsigned long)back, memcmp(back, from, 16) == 0);
    hold();
  }
  return 0;
}
