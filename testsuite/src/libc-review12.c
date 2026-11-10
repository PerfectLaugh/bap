// What Linux does of futexes and clone that a fourth review found the machine didn't (testLinuxRaises):
//   requeue: FUTEX_REQUEUE of a count below 0, to wake or to move, is EINVAL.
//   realtime: FUTEX_WAIT of FUTEX_CLOCK_REALTIME is ENOSYS, as only a wait to a time takes a clock.
//   parenttid: clone of CLONE_PARENT_SETTID where nothing can be written goes on without it.
//   cleartid: what a thread that ends clears of set_tid_address, in memory that its process shares with another, wakes a wait of the
//     other there; and of the last thread of a process, which leaves its memory to no one, nothing is cleared.
#define _GNU_SOURCE
#include <errno.h>
#include <linux/futex.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static long futex(uint32_t *word, int operation, uint32_t value, long timeout, uint32_t *target, uint32_t compare) {
  return syscall(SYS_futex, word, operation, value, timeout, target, compare);
}

static const char *named(long result) {
  if (result >= 0) return "done";
  return errno == EINVAL ? "EINVAL" : errno == ENOSYS ? "ENOSYS" : errno == EAGAIN ? "EAGAIN" : errno == ETIMEDOUT ? "ETIMEDOUT" : "other";
}

static void *sleeping(void *unused) {
  (void)unused;
  for (;;) pause();
  return 0;
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  static uint32_t word = 1, other = 1;
  printf("requeue waking -1: %s\n", named(futex(&word, FUTEX_REQUEUE | FUTEX_PRIVATE_FLAG, (uint32_t)-1, 1, &other, 0)));
  printf("requeue moving -1: %s\n", named(futex(&word, FUTEX_REQUEUE | FUTEX_PRIVATE_FLAG, 1, -1, &other, 0)));
  struct timespec span = {0, 1000};
  printf("wait of the realtime clock: %s\n", named(futex(&word, FUTEX_WAIT | FUTEX_CLOCK_REALTIME, 1, (long)&span, 0, 0)));
  long child = syscall(SYS_clone, SIGCHLD | CLONE_PARENT_SETTID, 0, (void *)8, 0, 0);
  if (child == 0) _exit(3);
  int status = 0;
  waitpid((pid_t)child, &status, 0);
  printf("clone of a parent tid that can't be written: %s, exited %d\n", child > 0 ? "done" : "failed",
         WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  uint32_t *shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  for (int threads = 1; threads <= 2; threads++) {
    *shared = 1;
    pid_t ending = fork();
    if (ending == 0) {
      pthread_t sleeper;
      if (threads == 2) pthread_create(&sleeper, 0, sleeping, 0);
      syscall(SYS_set_tid_address, shared);
      usleep(100000);
      syscall(SYS_exit, 0);
    }
    struct timespec limit = {1, 0};
    long waited = futex(shared, FUTEX_WAIT, 1, (long)&limit, 0, 0);
    printf("a wait where a thread of %d clears its tid as it ends: %s, the word %u\n", threads, named(waited), *shared);
    kill(ending, SIGKILL);
    waitpid(ending, 0, 0);
  }
  return 0;
}
