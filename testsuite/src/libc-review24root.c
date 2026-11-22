// What Linux says of a working directory that isn't under the root of its process, as root, in a process of its own: after chroot to a
// directory below it, getcwd gives its path with "(unreachable)" before it, which the getcwd of a libc makes ENOENT, until the process
// is somewhere under its root again.
// In a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static const char *error(long result) { return result < 0 ? strerror(errno) : "ok"; }

static void outside(void) {
  char path[512] = {0}, libc[512];
  const char *marker = "(unreachable)/", *last = "/r24root";
  printf("chroot: %s\n", error(chroot("jail")));
  long size = syscall(SYS_getcwd, path, sizeof path);
  /* where this runs is the host's: what is before and after it is said */
  printf("getcwd gives a path %s: starts as unreachable %d, ends where it is %d\n", size == (long)strlen(path) + 1 ? "and its size" : "only",
         strncmp(path, marker, strlen(marker)) == 0, size > 8 && strcmp(path + strlen(path) - strlen(last), last) == 0);
  printf("getcwd of the libc: %s\n", getcwd(libc, sizeof libc) ? libc : strerror(errno));
  printf("chdir to the root: %s\n", error(chdir("/")));
  size = syscall(SYS_getcwd, path, sizeof path);
  printf("getcwd gives %ld: %s\n", size, path);
  printf("chdir into it: %s\n", error(chdir("/in")));
  printf("getcwd of the libc: %s\n", getcwd(libc, sizeof libc) ? libc : strerror(errno));
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("r24root", 0755);
  chdir("r24root");
  mkdir("jail", 0755);
  mkdir("jail/in", 0755);
  pid_t child = fork();
  if (child == 0) {
    alarm(10);
    outside();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) printf("ended with %x\n", status);
  rmdir("jail/in");
  rmdir("jail");
  chdir("..");
  rmdir("r24root");
  printf("done\n");
  return 0;
}
