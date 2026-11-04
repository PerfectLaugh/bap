// A program that runs what a directory of the host has: a script there, which names a program there to run it.
#define _GNU_SOURCE
#include <errno.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void put(const char *text) {
  unsigned long n = 0;
  while (text[n]) n++;
  write(1, text, n);
}

int main(int argc, char **argv) {
  if (argc > 1 && argv[1][0] == 'c' && argv[1][1] == 0) {
    put("child");
    for (int index = 2; index < argc; index++) { put(" "); put(argv[index]); }
    put("\n");
    return 0;
  }
  char *arguments[] = {"/host/script", "x", 0};
  char *environment[] = {0};
  long failed = syscall(SYS_execve, (long)arguments[0], (long)arguments, (long)environment, 0L, 0L, 0L);
  put(failed < 0 && errno == ENOENT ? "exec ENOENT\n" : "exec failed\n");
  return 1;
}
