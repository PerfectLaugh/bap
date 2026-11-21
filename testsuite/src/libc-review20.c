// What Linux does that a review of the code found the machine didn't:
//   vectors: an array of buffers that isn't there to read is EFAULT of readv, writev and preadv, of a file, a pipe and an eventfd,
//     rather than what ends the run; as is where what inotify has to say can't be written.
//   futex: a word that isn't aligned is EINVAL of a wait and of a wake, rather than a wait that nothing ends.
//   flags: of x86_64, pushfq reads all of the flags, of which the one that is always set and that of interrupts are.
// Each in a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/futex.h>
#include <stdio.h>
#include <string.h>
#include <sys/eventfd.h>
#include <sys/inotify.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

static void vectors(void) {
  struct iovec *bad = (struct iovec *)16;
  int file = open("file", O_CREAT | O_TRUNC | O_RDWR, 0644);
  write(file, "hello", 5);
  lseek(file, 0, SEEK_SET);
  said("readv of a file, no vectors", readv(file, bad, 1));
  said("writev of a file, no vectors", writev(file, bad, 1));
  said("preadv of a file, no vectors", preadv(file, bad, 1, 0));
  said("pwritev of a file, no vectors", pwritev(file, bad, 1, 0));
  int ends[2];
  pipe(ends);
  write(ends[1], "x", 1);
  said("readv of a pipe, no vectors", readv(ends[0], bad, 1));
  said("writev of a pipe, no vectors", writev(ends[1], bad, 1));
  int event = eventfd(1, 0);
  said("readv of an eventfd, no vectors", readv(event, bad, 1));
  said("writev of the output, no vectors", writev(1, bad, 1));
  int watch = inotify_init1(IN_NONBLOCK);
  inotify_add_watch(watch, ".", IN_CREATE);
  close(open("made", O_CREAT | O_RDWR, 0644));
  said("read of inotify, nowhere", read(watch, (void *)16, 4096));
  close(watch);
  close(event);
  close(ends[0]);
  close(ends[1]);
  close(file);
  unlink("made");
  unlink("file");
}

static void futexes(void) {
  static int words[2];
  char *odd = (char *)words + 1;
  said("futex wait, not aligned", syscall(SYS_futex, odd, FUTEX_WAIT, 0, 0, 0, 0));
  said("futex wake, not aligned", syscall(SYS_futex, odd, FUTEX_WAKE, 1, 0, 0, 0));
  said("futex wake, aligned", syscall(SYS_futex, words, FUTEX_WAKE, 1, 0, 0, 0));
}

static void flags(void) {
#ifdef __x86_64__
  unsigned long all;
  __asm__ volatile("xor %%eax, %%eax; pushfq; pop %0" : "=r"(all) : : "rax", "cc");
  printf("flags after xor: %lx\n", all);
#else
  printf("flags after xor: none\n");
#endif
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("review20", 0755);
  chdir("review20");
  vectors();
  futexes();
  flags();
  chdir("..");
  rmdir("review20");
  return 0;
}
