// What Linux does of counts that a guest gives, which a fifth review found the machine made as much of the host of as they said, and
// of what goes with them (testLinuxRaises):
//   pselect6 of -1 is EINVAL, and of more than there are descriptors reads no more than there are;
//   rt_sigpending of more than a set is EINVAL, and of less is the first of it;
//   io_uring_register of a probe of 2^32-1 operations, of no buffers and of more files than there may be;
//   io_uring_enter submits no more than the ring has entries, whatever its tail says;
//   io_submit of more than its context has room for submits that many.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/aio_abi.h>
#include <linux/io_uring.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/select.h>
#include <sys/syscall.h>
#include <unistd.h>

static void say(const char *name, long result) {
  if (result < 0) printf("%s: -%d\n", name, errno);
  else printf("%s: %ld\n", name, result);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "x", 1);
  fd_set reads;
  FD_ZERO(&reads);
  FD_SET(pipes[0], &reads);
  struct timespec none = {0, 0};
  say("select of -1", syscall(SYS_pselect6, -1, &reads, 0, 0, &none, 0));
  say("select of 100000", syscall(SYS_pselect6, 100000, &reads, 0, 0, &none, 0));
  uint64_t set[2] = {0, 0};
  say("rt_sigpending of 16", syscall(SYS_rt_sigpending, set, 16));
  say("rt_sigpending of 4", syscall(SYS_rt_sigpending, set, 4));
  struct io_uring_params params;
  memset(&params, 0, sizeof params);
  int ring = (int)syscall(SYS_io_uring_setup, 8, &params);
  static char probe[4096 * 4];
  say("probe of 2^32-1", syscall(SYS_io_uring_register, ring, IORING_REGISTER_PROBE, probe, 0xffffffffu));
  say("probe of 256", syscall(SYS_io_uring_register, ring, IORING_REGISTER_PROBE, probe, 256) == 0);
  say("no buffers", syscall(SYS_io_uring_register, ring, IORING_REGISTER_BUFFERS, probe, 0));
  say("too many files", syscall(SYS_io_uring_register, ring, IORING_REGISTER_FILES, probe, 0x7fffffffu));
  char *submit = mmap(0, params.sq_off.array + params.sq_entries * 4, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQ_RING);
  mmap(0, params.cq_off.cqes + params.cq_entries * sizeof(struct io_uring_cqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring,
       IORING_OFF_CQ_RING);
  struct io_uring_sqe *entries = mmap(0, params.sq_entries * sizeof(struct io_uring_sqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring,
                                      IORING_OFF_SQES);
  memset(entries, 0, params.sq_entries * sizeof(struct io_uring_sqe));
  uint32_t *array = (uint32_t *)(submit + params.sq_off.array);
  for (unsigned index = 0; index < params.sq_entries; index++) array[index] = index;
  uint32_t *tail = (uint32_t *)(submit + params.sq_off.tail);
  __atomic_store_n(tail, *tail + 20, __ATOMIC_RELEASE);
  say("enter of 20 on 8 entries", syscall(SYS_io_uring_enter, ring, 0xffffffffu, 0, 0, 0, 0));
  aio_context_t context = 0;
  say("io_setup", syscall(SYS_io_setup, 1, &context));
  int file = open("review14.data", O_CREAT | O_RDWR | O_TRUNC, 0600);
  unlink("review14.data");
  struct iocb write1;
  memset(&write1, 0, sizeof write1);
  write1.aio_lio_opcode = IOCB_CMD_PWRITE;
  write1.aio_fildes = file;
  write1.aio_buf = (unsigned long)"x";
  write1.aio_nbytes = 1;
  struct iocb *list[2] = {&write1, &write1};
  long submitted = syscall(SYS_io_submit, context, 1ul << 40, list);
  printf("io_submit of 2^40 submits some: %d\n", submitted > 0);
  return 0;
}
