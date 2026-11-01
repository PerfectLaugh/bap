/* execve: of a program in a child, of one that isn't there, of a script, and of a descriptor that doesn't stay open. */
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

int main(int argc, char **argv, char **envp) {
  if (argc > 1 && strcmp(argv[1], "child") == 0) {
    printf("child:");
    for (int i = 2; i < argc; i++) printf(" %s", argv[i]);
    printf(" env=%s", envp[0] ? envp[0] : "none");
    printf(" kept=%d", fcntl(3, F_GETFD) != -1);
    printf(" closed=%d\n", fcntl(4, F_GETFD) != -1);
    fflush(stdout);
    /* What it had before is gone, and its heap works. */
    char *block = malloc(100000);
    block[99999] = 1;
    return 7;
  }
  char *none[] = {"/nothing", NULL};
  execv("/nothing", none);
  printf("missing %d\n", errno);
  fflush(stdout);
  int kept = open("/test", O_RDONLY);
  int closed = open("/test", O_RDONLY | O_CLOEXEC);
  printf("descriptors %d %d\n", kept, closed);
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    char *arguments[] = {"/test", "child", "a", "bc", NULL};
    char *environment[] = {"NAME=value", NULL};
    execve("/test", arguments, environment);
    _exit(99);
  }
  int status = 0;
  waitpid(pid, &status, 0);
  printf("status %d\n", WEXITSTATUS(status));
  fflush(stdout);
  pid = fork();
  if (pid == 0) {
    char *arguments[] = {"/script", "x", NULL};
    char *environment[] = {NULL};
    execve("/script", arguments, environment);
    _exit(98);
  }
  waitpid(pid, &status, 0);
  printf("script %d\n", WEXITSTATUS(status));
  return 0;
}
