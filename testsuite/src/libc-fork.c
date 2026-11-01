#include <stdio.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
/* A process and its child, whose memory is its own, and which tell each other things by a file and a status. */
static int shared = 1;
int main(void) {
  int fd = open("/out", O_CREAT | O_RDWR, 0644);
  pid_t child = fork();
  if (child == 0) {
    shared = 2; for (int i = 0; i < 12; i++) dprintf(fd, "%d\n", i * shared);
    _exit(7);
  }
  int status = 0; waitpid(child, &status, 0);
  char text[32]; lseek(fd, -4, SEEK_END); int n = read(fd, text, 4); text[n] = 0;
  printf("status %d shared %d last %s", WEXITSTATUS(status), shared, text);
  return 3;
}
