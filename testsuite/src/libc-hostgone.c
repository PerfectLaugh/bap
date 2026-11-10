// A file of a directory of the host that the machine mounts, which the program removes and then works: what it removed is gone, even
// as the machine is saved and put back as it was then (testHostDeleted).
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

int main(void) {
  close(open("/mnt/a", O_RDONLY));
  unlink("/mnt/a");
  for (volatile long index = 0; index < 2000000; index++) {
  }
  struct stat status;
  printf("what was removed is %s\n", stat("/mnt/a", &status) == 0 ? "there" : "gone");
  return 0;
}
