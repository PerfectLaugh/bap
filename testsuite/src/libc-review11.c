// What a mapping takes of the host is what it has, not how large it is (testLinuxRaises): a shared mapping of 16 GiB of a file of a page,
// written where the file is and read back of the file, grown by mremap and moved; a shared anonymous mapping of 16 GiB, of which a write
// writes a little; and a writev of pieces that say more than there is, to a pipe.
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/uio.h>
#include <unistd.h>

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  int fd = open("review11.data", O_RDWR | O_CREAT | O_TRUNC, 0600);
  unlink("review11.data");
  char page[4096];
  memset(page, 'a', sizeof page);
  write(fd, page, sizeof page);
  size_t huge = (size_t)1 << 34;
  char *mapped = mmap(0, huge, PROT_READ | PROT_WRITE, MAP_SHARED, fd, 0);
  printf("mmap of 16 GiB of a page: %s\n", mapped == MAP_FAILED ? "failed" : "mapped");
  if (mapped == MAP_FAILED) return 0;
  mapped[1] = 'b';
  char back[2] = {0};
  pread(fd, back, 2, 0);
  printf("of the file: %c%c\n", back[0], back[1]);
  char *moved = mremap(mapped, huge, huge + 4096, MREMAP_MAYMOVE);
  printf("mremap: %s, keeps %c%c\n", moved == MAP_FAILED ? "failed" : "moved", moved[0], moved[1]);
  munmap(moved, huge + 4096);
  size_t large = (size_t)1 << 34;
  char *anonymous = mmap(0, large, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  printf("shared anonymous of 16 GiB: %s\n", anonymous == MAP_FAILED ? "failed" : "mapped");
  anonymous[large - 1] = 'z';
  int null = open("/dev/null", O_WRONLY);
  printf("a write of its last byte: %zd\n", write(null, anonymous + large - 1, 1));
  int pipes[2];
  pipe(pipes);
  struct iovec pieces[2] = {{page, 3}, {anonymous, large}};
  printf("writev of 3 and 16 GiB to a pipe that doesn't wait: %zd\n", (fcntl(pipes[1], F_SETFL, O_NONBLOCK), writev(pipes[1], pieces, 2)));
  return 0;
}
