/* /proc/self/auxv, against what the program was given. */
#include <fcntl.h>
#include <stdio.h>
#include <sys/auxv.h>
#include <unistd.h>
int main(void) {
  unsigned long words[128];
  int fd = open("/proc/self/auxv", O_RDONLY);
  long size = read(fd, words, sizeof words);
  unsigned long count = size / sizeof words[0], agree = 0, pairs = 0;
  for (unsigned long i = 0; i + 1 < count && words[i] != 0; i += 2) {
    pairs++;
    if (getauxval(words[i]) == words[i + 1]) agree++;
  }
  printf("%d %d %d\n", pairs > 5, agree == pairs, count >= 2 && words[count - 2] == 0 && words[count - 1] == 0);
  return 0;
}
