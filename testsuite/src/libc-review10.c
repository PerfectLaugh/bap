// What Linux does of io_uring, timerfd and seccomp that a fourth review found the machine didn't, each in a process of its own, with an
// alarm that ends what would hang (testLinuxRaises):
//   ringcancel: IORING_OP_ASYNC_CANCEL completes, and then what it cancels.
//   hardlink: what IOSQE_IO_HARDLINK links goes on after a failure, which IOSQE_IO_LINK cancels, and waits for what waits.
//   timerfd: timerfd_gettime of a timer that repeats and expired says when it expires next.
//   strict: a call that strict mode doesn't take ends the thread by SIGKILL, and not the others of its process.
#define _GNU_SOURCE
#include <errno.h>
#include <linux/io_uring.h>
#include <linux/seccomp.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/timerfd.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void part(const char *name, void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(5);
    run();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("%s: ended by signal %d\n", name, WTERMSIG(status));
}

struct ring {
  int fd;
  struct io_uring_params params;
  char *submit, *complete;
  struct io_uring_sqe *entries;
  unsigned queued;
};

static int ringMake(struct ring *ring) {
  memset(ring, 0, sizeof *ring);
  ring->fd = (int)syscall(SYS_io_uring_setup, 8, &ring->params);
  if (ring->fd < 0) return -1;
  struct io_uring_params *params = &ring->params;
  ring->submit = mmap(0, params->sq_off.array + params->sq_entries * 4, PROT_READ | PROT_WRITE, MAP_SHARED, ring->fd, IORING_OFF_SQ_RING);
  ring->complete = mmap(0, params->cq_off.cqes + params->cq_entries * sizeof(struct io_uring_cqe), PROT_READ | PROT_WRITE, MAP_SHARED,
                        ring->fd, IORING_OFF_CQ_RING);
  ring->entries = mmap(0, params->sq_entries * sizeof(struct io_uring_sqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring->fd, IORING_OFF_SQES);
  return 0;
}

static struct io_uring_sqe *ringAdd(struct ring *ring, int opcode, int flags, unsigned long data) {
  unsigned *tail = (unsigned *)(ring->submit + ring->params.sq_off.tail);
  unsigned index = (*tail + ring->queued) & (ring->params.sq_entries - 1);
  struct io_uring_sqe *entry = &ring->entries[index];
  memset(entry, 0, sizeof *entry);
  entry->opcode = opcode;
  entry->flags = flags;
  entry->user_data = data;
  ((unsigned *)(ring->submit + ring->params.sq_off.array))[index] = index;
  ring->queued++;
  return entry;
}

static int ringEnter(struct ring *ring, unsigned wait) {
  unsigned *tail = (unsigned *)(ring->submit + ring->params.sq_off.tail);
  unsigned count = ring->queued;
  __atomic_store_n(tail, *tail + count, __ATOMIC_RELEASE);
  ring->queued = 0;
  return (int)syscall(SYS_io_uring_enter, ring->fd, count, wait, IORING_ENTER_GETEVENTS, 0, 0);
}

// What has completed, as its data and result, in order.
static void ringSay(struct ring *ring) {
  unsigned *head = (unsigned *)(ring->complete + ring->params.cq_off.head);
  unsigned tail = __atomic_load_n((unsigned *)(ring->complete + ring->params.cq_off.tail), __ATOMIC_ACQUIRE);
  struct io_uring_cqe *results = (struct io_uring_cqe *)(ring->complete + ring->params.cq_off.cqes);
  for (; *head != tail; (*head)++) {
    struct io_uring_cqe *result = &results[*head & (ring->params.cq_entries - 1)];
    printf(" %llu:%s", (unsigned long long)result->user_data, result->res >= 0 ? "ok" : result->res == -ETIME ? "ETIME"
                                                              : result->res == -ECANCELED ? "ECANCELED" : strerror(-result->res));
  }
}

static void ringCancel(void) {
  struct ring ring;
  if (ringMake(&ring) < 0) {
    printf("ringcancel: no io_uring\n");
    return;
  }
  int pipes[2];
  pipe(pipes);
  static char buffer[8];
  struct io_uring_sqe *entry = ringAdd(&ring, IORING_OP_READ, 0, 1);
  entry->fd = pipes[0];
  entry->addr = (unsigned long)buffer;
  entry->len = 1;
  ringEnter(&ring, 0);
  entry = ringAdd(&ring, IORING_OP_ASYNC_CANCEL, 0, 2);
  entry->addr = 1;
  ringEnter(&ring, 2);
  printf("ringcancel: completed");
  ringSay(&ring);
  printf("\n");
}

static void hardLink(void) {
  struct ring ring;
  if (ringMake(&ring) < 0) {
    printf("hardlink: no io_uring\n");
    return;
  }
  static char buffer[8];
  struct io_uring_sqe *entry = ringAdd(&ring, IORING_OP_READ, IOSQE_IO_HARDLINK, 1);
  entry->fd = 999;
  entry->addr = (unsigned long)buffer;
  entry->len = 1;
  ringAdd(&ring, IORING_OP_NOP, 0, 2);
  entry = ringAdd(&ring, IORING_OP_READ, IOSQE_IO_LINK, 3);
  entry->fd = 999;
  entry->addr = (unsigned long)buffer;
  entry->len = 1;
  ringAdd(&ring, IORING_OP_NOP, 0, 4);
  ringEnter(&ring, 4);
  // And one that waits holds up what it is hard linked to.
  int pipes[2];
  pipe(pipes);
  entry = ringAdd(&ring, IORING_OP_READ, IOSQE_IO_HARDLINK, 5);
  entry->fd = pipes[0];
  entry->addr = (unsigned long)buffer;
  entry->len = 1;
  ringAdd(&ring, IORING_OP_NOP, 0, 6);
  ringEnter(&ring, 0);
  usleep(50000);
  // By what each was, as they complete in what order they may.
  const char *results[7] = {"", "none", "none", "none", "none", "none", "none"};
  unsigned *head = (unsigned *)(ring.complete + ring.params.cq_off.head);
  unsigned tail = __atomic_load_n((unsigned *)(ring.complete + ring.params.cq_off.tail), __ATOMIC_ACQUIRE);
  struct io_uring_cqe *all = (struct io_uring_cqe *)(ring.complete + ring.params.cq_off.cqes);
  for (; *head != tail; (*head)++) {
    struct io_uring_cqe *result = &all[*head & (ring.params.cq_entries - 1)];
    if (result->user_data < 7)
      results[result->user_data] = result->res >= 0 ? "ok" : result->res == -ECANCELED ? "ECANCELED" : strerror(-result->res);
  }
  printf("hardlink: after one that failed, of a hard link %s, of a link %s, after one that waits %s\n", results[2], results[4], results[6]);
}

static void timerfdLeft(void) {
  int fd = timerfd_create(CLOCK_MONOTONIC, 0);
  struct itimerspec every = {{0, 100000000}, {0, 100000000}};
  timerfd_settime(fd, 0, &every, 0);
  usleep(250000);
  struct itimerspec now;
  timerfd_gettime(fd, &now);
  printf("timerfd: of one that repeats and expired, left before the next %d\n", now.it_value.tv_sec == 0 && now.it_value.tv_nsec > 0);
}

static void *strictThread(void *unused) {
  (void)unused;
  syscall(SYS_seccomp, SECCOMP_SET_MODE_STRICT, 0, 0);
  syscall(SYS_getpid);
  return (void *)1;
}

static void strict(void) {
  pid_t child = fork();
  if (child == 0) {
    syscall(SYS_seccomp, SECCOMP_SET_MODE_STRICT, 0, 0);
    syscall(SYS_getpid);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  printf("strict: of the only thread, ended by %d, ", WIFSIGNALED(status) ? WTERMSIG(status) : 0);
  pthread_t thread;
  pthread_create(&thread, 0, strictThread, 0);
  usleep(200000);
  printf("of another thread, the process goes on\n");
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part("ringcancel", ringCancel);
  part("hardlink", hardLink);
  part("timerfd", timerfdLeft);
  part("strict", strict);
  printf("done\n");
  return 0;
}
