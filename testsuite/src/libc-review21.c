// What Linux does that a review of the fixes of libc-review20.c found the machine didn't:
//   vectors: an array of buffers whose second isn't there to read is EFAULT before anything is done, as import_iovec reads
//     all of it first: a pipe keeps what it had, and a file is where it was, with what it had.
//   futex: a requeue of a word that isn't aligned, either of its two, is EINVAL, before the first is compared; and a wake
//     of a shared word that isn't there is EFAULT.
//   floats: of AArch64, a rounding to an integral value of a signaling NaN is invalid.
//   segments: of x86_64, an operand of SSE in memory is at its segment, as what is of a thread is at fs.
//   traced: a tracer that isn't the parent of what ends, and waits for it, lets its parent, which waits too, have it.
// In a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <fenv.h>
#include <math.h>
#include <signal.h>
#include <linux/futex.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

static void vectors(void) {
  char *page = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  munmap(page + 4096, 4096);
  struct iovec *iov = (struct iovec *)(page + 4096 - sizeof(struct iovec));
  char buf[8] = "XYZ", rest[16] = {0};
  iov[0].iov_base = buf;
  iov[0].iov_len = 3;
  int ends[2];
  pipe(ends);
  write(ends[1], "abcdef", 6);
  said("readv of a pipe, second vector not there", readv(ends[0], iov, 2));
  said("what the pipe still has", read(ends[0], rest, 16));
  printf("%s\n", rest);
  int file = open("file", O_CREAT | O_TRUNC | O_RDWR, 0644);
  write(file, "hello", 5);
  lseek(file, 0, SEEK_SET);
  said("readv of a file", readv(file, iov, 2));
  said("where the file is", lseek(file, 0, SEEK_CUR));
  memcpy(buf, "XYZ", 3);
  said("writev of a file", writev(file, iov, 2));
  said("where the file is", lseek(file, 0, SEEK_CUR));
  said("pwritev of a file", pwritev(file, iov, 2, 1));
  struct stat status;
  fstat(file, &status);
  char all[16] = {0};
  pread(file, all, 15, 0);
  printf("size %ld: %s\n", (long)status.st_size, all);
  close(file);
  unlink("file");
}

static void futexes(void) {
  static int words[4];
  char *odd = (char *)words + 1;
  said("requeue, first not aligned", syscall(SYS_futex, odd, FUTEX_REQUEUE, 1, 1, words + 2, 0));
  said("requeue, second not aligned", syscall(SYS_futex, words, FUTEX_REQUEUE, 1, 1, odd, 0));
  said("cmp requeue, first not aligned", syscall(SYS_futex, odd, FUTEX_CMP_REQUEUE, 1, 1, words + 2, 0));
  said("cmp requeue, second not aligned", syscall(SYS_futex, words, FUTEX_CMP_REQUEUE, 1, 1, odd, 0));
  said("cmp requeue, second not aligned, other value", syscall(SYS_futex, words, FUTEX_CMP_REQUEUE, 1, 1, odd, 7));
  said("cmp requeue, aligned, other value", syscall(SYS_futex, words, FUTEX_CMP_REQUEUE, 1, 1, words + 2, 7));
  said("cmp requeue, aligned", syscall(SYS_futex, words, FUTEX_CMP_REQUEUE, 1, 1, words + 2, 0));
  said("wake, not aligned, nowhere", syscall(SYS_futex, (char *)17, FUTEX_WAKE, 1, 0, 0, 0));
  said("wait, aligned, nowhere", syscall(SYS_futex, (char *)16, FUTEX_WAIT, 0, 0, 0, 0));
  said("wake, aligned, nowhere", syscall(SYS_futex, (char *)16, FUTEX_WAKE, 1, 0, 0, 0));
  said("wake, aligned, nowhere, private", syscall(SYS_futex, (char *)16, FUTEX_WAKE_PRIVATE, 1, 0, 0, 0));
}

static void floats(void) {
  volatile double signaling;
  unsigned long long bits = 0x7ff0000000000001ull;
  memcpy((void *)&signaling, &bits, 8);
  feclearexcept(FE_ALL_EXCEPT);
  volatile double rounded = rint(signaling);
  printf("rint of a signaling NaN is invalid: %d, and a NaN: %d\n", !!fetestexcept(FE_INVALID), rounded != rounded);
  feclearexcept(FE_ALL_EXCEPT);
  rounded = rint(1.5);
  printf("rint of 1.5 is invalid: %d, inexact: %d\n", !!fetestexcept(FE_INVALID), !!fetestexcept(FE_INEXACT));
}

/* What is of a thread, read by an instruction of SSE that has it for an operand, is at the segment of the thread */
static __thread double threadDouble = 2.0;
static __thread float threadFloat = 3.0f;

static void segments(void) {
  volatile double three = 3.0;
  volatile float one = 1.0f;
  printf("of the thread: %f %d %f\n", three * threadDouble, (int)threadDouble, one + threadFloat);
}

/* A tracer of a child that forks, as strace -f is: the child waits for its own child, which ends, and the tracer, which hears
   of that first, waits for it; the child then has what it waits for. */
static void traced(void) {
#ifndef __x86_64__
  /* which qemu, that says what the others do, can't run */
  printf("not traced\n");
#else
  int status;
  pid_t child = fork();
  if (!child) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    pid_t grandchild = fork();
    if (!grandchild) {
      usleep(30000);
      _exit(3);
    }
    int ended = 0;
    pid_t waited = waitpid(grandchild, &ended, 0);
    _exit(waited == grandchild && WEXITSTATUS(ended) == 3 ? 10 : 11);
  }
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACEFORK);
  ptrace(PTRACE_CONT, child, 0, 0);
  for (int round = 0; round < 30; round++) {
    usleep(60000);
    pid_t waited = waitpid(-1, &status, __WALL);
    if (waited < 0) {
      printf("no more to wait for: %s\n", strerror(errno));
      break;
    }
    printf("%s: status %x\n", waited == child ? "child" : "grandchild", status);
    if (WIFSTOPPED(status)) {
      int signal = WSTOPSIG(status);
      if (status >> 16 || signal == SIGSTOP || signal == SIGTRAP) signal = 0;
      ptrace(PTRACE_CONT, waited, 0, signal);
    }
  }
#endif
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("review21", 0755);
  chdir("review21");
  vectors();
  futexes();
  floats();
  segments();
  traced();
  chdir("..");
  rmdir("review21");
  return 0;
}
