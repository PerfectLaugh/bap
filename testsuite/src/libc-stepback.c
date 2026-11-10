// A file of a directory of the host that the machine mounts, opened at the start and then a while of work: what `stepBack` goes back over
// opens it again as the run did (testStepBackHost).
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdio.h>

int main(void) {
  int fd = open("/mnt/a", O_RDONLY);
  for (volatile long index = 0; index < 2000000; index++) {
  }
  printf("open %s\n", fd >= 0 ? "ok" : "failed");
  return 0;
}
