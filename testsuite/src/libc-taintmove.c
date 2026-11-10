// What the taint of a machine says of memory that a call fills that isn't of the world (testLinuxTaintMoves): of `exec`, the program
// that execve runs, whose constants come from nothing; of `mremap`, bytes of a file that a mapping moves with, which still come from it;
// of `append`, bytes of a file that pwrite wrote to one opened to append, which go to its end, whatever pwrite says, and come back from
// there.
// Each says where what it is about is, and then works, for the test to look there.
#define _GNU_SOURCE
#include <fcntl.h>
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
  return 0;
}
