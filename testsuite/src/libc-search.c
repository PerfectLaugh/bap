// Search permission, as Linux's path walk has it: each directory that a path goes through, and the one that it ends in, may be looked
// in only by who may search it (exec), whatever the call, so that open, creat, mkdir, unlink, rename, a symlink through it, .. of it,
// openat of its descriptor and a name that isn't there are each EACCES, and a directory that may only be searched (0100) is walked.
// It works as user 1000 in a directory of its own, and says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static const char *error(long result) { return result < 0 ? strerror(errno) : "ok"; }

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("s-work", 0755);
  chown("s-work", 1000, 1000);
  chdir("s-work");
  setgid(1000);
  setuid(1000);
  mkdir("closed", 0755);
  close(creat("closed/file", 0644));
  mkdir("closed/inner", 0755);
  symlink("closed/file", "link");
  symlink("closed", "dirlink");
  int directory = open("closed", O_RDONLY | O_DIRECTORY);
  chmod("closed", 0600);
  struct stat status;
  printf("open %s, ", error(open("closed/file", O_RDONLY)));
  printf("creat %s, ", error(open("closed/new", O_CREAT | O_WRONLY, 0644)));
  printf("missing %s, ", error(stat("closed/missing", &status)));
  printf("mkdir %s, ", error(mkdir("closed/dir", 0755)));
  printf("unlink %s, ", error(unlink("closed/file")));
  printf("rename %s\n", error(rename("closed/file", "moved")));
  printf("symlink %s, ", error(stat("link", &status)));
  printf("through a link to it %s, ", error(stat("dirlink/file", &status)));
  printf(".. of it %s, ", error(stat("closed/..", &status)));
  printf("of inner %s, ", error(stat("closed/inner/..", &status)));
  printf("openat %s, ", error(openat(directory, "file", O_RDONLY)));
  printf("the directory itself %s\n", error(stat("closed", &status)));
  chmod("closed", 0100);
  printf("searched only: open %s, ", error(open("closed/file", O_RDONLY)));
  printf("..%s, ", error(stat("closed/inner/..", &status)));
  printf("listed %s\n", error(open("closed", O_RDONLY | O_DIRECTORY)));
  chdir("closed/inner");
  chmod("..", 0600);
  printf("from within: .. %s, ", error(stat("..", &status)));
  printf("../.. %s, ", error(stat("../..", &status)));
  printf("here %s\n", error(stat(".", &status)));
  chmod("..", 0755);
  chdir("../..");
  unlink("link");
  unlink("dirlink");
  rmdir("closed/inner");
  unlink("closed/file");
  rmdir("closed");
  chdir("..");
  rmdir("s-work");
  printf("done\n");
  return 0;
}
