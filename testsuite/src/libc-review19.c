// What Linux does that a review of the code found the machine didn't:
//   llseek: of a 64-bit target whose musl seeks by _llseek, as PowerPC64's does, the offset is the halves ORed, as Linux has them:
//     the low half is all of it there, and a seek back from the end or past 4 GiB is where it says.
//   pipe: a read of the end of a pipe that is written is EBADF, rather than one that waits, or EAGAIN of one that doesn't block.
//   at: a path is read before the directory it is of, and an absolute path doesn't look at the directory at all: a bad descriptor
//     or one of a file is nothing to it, though a bad address or an empty path is still EFAULT or ENOENT first.
// Each in a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

static void llseek(void) {
  int fd = open("file", O_CREAT | O_TRUNC | O_RDWR, 0644);
  write(fd, "hello world", 11);
  said("lseek -5 from the end", lseek(fd, -5, SEEK_END));
  said("lseek 5 GiB and 5", lseek(fd, 5LL * 1024 * 1024 * 1024 + 5, SEEK_SET));
  said("lseek -100 from the start", lseek(fd, -100, SEEK_SET));
  said("lseek 0 from where it is", lseek(fd, 0, SEEK_CUR));
  said("lseek -1 from where it is", lseek(fd, -1, SEEK_CUR));
  close(fd);
  unlink("file");
}

static void pipe_ends(void) {
  int ends[2];
  char byte;
  pipe(ends);
  said("read of the written end", read(ends[1], &byte, 1));
  fcntl(ends[1], F_SETFL, O_NONBLOCK);
  said("read of the written end that doesn't block", read(ends[1], &byte, 1));
  said("read of the read end that doesn't block", (fcntl(ends[0], F_SETFL, O_NONBLOCK), read(ends[0], &byte, 1)));
  close(ends[0]);
  close(ends[1]);
}

static void at(void) {
  int file = open("file", O_CREAT | O_TRUNC | O_RDWR, 0644);
  said("openat of a bad descriptor, absolute", openat(-1, "/", O_RDONLY | O_DIRECTORY) >= 0 ? 0 : -1);
  said("openat of a file, absolute", openat(file, "/", O_RDONLY | O_DIRECTORY) >= 0 ? 0 : -1);
  said("openat of a file, relative", openat(file, "x", O_RDONLY));
  said("openat of a bad descriptor, relative", openat(99, "x", O_RDONLY));
  said("mkdirat of a file, absolute that is there", mkdirat(file, "/", 0755));
  said("faccessat of a bad descriptor, absolute", faccessat(99, "/", F_OK, 0));
  char buffer[16];
  said("readlinkat of a bad descriptor, absolute", readlinkat(99, "/", buffer, sizeof buffer));
  said("faccessat of a bad descriptor, empty", faccessat(99, "", F_OK, 0));
  said("faccessat of a bad descriptor, bad address", faccessat(99, (const char *)8, F_OK, 0));
  said("fchmodat of a bad descriptor, absolute", fchmodat(99, "/nonexistent-review19", 0644, 0));
  close(file);
  unlink("file");
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  alarm(10);
  mkdir("review19", 0755);
  chdir("review19");
  llseek();
  pipe_ends();
  at();
  chdir("..");
  rmdir("review19");
  return 0;
}
