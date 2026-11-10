// The `struct stat` that 64-bit MIPS's fstat writes is the kernel's of n64, which is 104 bytes and ends at st_blocks: nothing past it is
// written, as a program that has only that much room for it, as Go's has, would be harmed (testLinuxRaises).
#define _GNU_SOURCE
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/syscall.h>
#include <unistd.h>

int main(void) {
  unsigned char buffer[200];
  memset(buffer, 0xaa, sizeof buffer);
  int fd = open("/dev/null", O_RDONLY);
  long result = syscall(SYS_fstat, fd, buffer);
  int past = 0;
  for (unsigned index = 104; index < sizeof buffer; index++)
    if (buffer[index] != 0xaa) past++;
  printf("fstat %ld, bytes written past 104: %d\n", result, past);
  return 0;
}
