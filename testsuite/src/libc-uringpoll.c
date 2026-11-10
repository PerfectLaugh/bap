// io_uring's POLL_ADD of POLLIN on a pipe that has something in it completes with POLLIN, of the mask as liburing puts it in
// `poll32_events`: with its halves swapped on a big-endian machine, which the kernel swaps back (testLinuxRaises). Only the system calls,
// as musl has no liburing.
#define _GNU_SOURCE
#include <linux/io_uring.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

int main(void) {
  struct io_uring_params params;
  memset(&params, 0, sizeof params);
  int ring = (int)syscall(SYS_io_uring_setup, 4, &params);
  if (ring < 0) {
    printf("no io_uring\n");
    return 0;
  }
  size_t submitSize = params.sq_off.array + params.sq_entries * sizeof(uint32_t);
  size_t completeSize = params.cq_off.cqes + params.cq_entries * sizeof(struct io_uring_cqe);
  char *submit = mmap(0, submitSize, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQ_RING);
  char *complete = mmap(0, completeSize, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_CQ_RING);
  struct io_uring_sqe *entries = mmap(0, params.sq_entries * sizeof(struct io_uring_sqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring,
                                      IORING_OFF_SQES);
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "x", 1);
  struct io_uring_sqe *entry = &entries[0];
  memset(entry, 0, sizeof *entry);
  entry->opcode = IORING_OP_POLL_ADD;
  entry->fd = pipes[0];
  uint32_t mask = POLLIN;
#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
  mask = (mask << 16) | (mask >> 16);
#endif
  entry->poll32_events = mask;
  uint32_t *array = (uint32_t *)(submit + params.sq_off.array);
  uint32_t *tail = (uint32_t *)(submit + params.sq_off.tail);
  array[*tail & (params.sq_entries - 1)] = 0;
  __atomic_store_n(tail, *tail + 1, __ATOMIC_RELEASE);
  syscall(SYS_io_uring_enter, ring, 1, 1, IORING_ENTER_GETEVENTS, 0, 0);
  uint32_t head = *(uint32_t *)(complete + params.cq_off.head);
  struct io_uring_cqe *results = (struct io_uring_cqe *)(complete + params.cq_off.cqes);
  int result = results[head & (params.cq_entries - 1)].res;
  printf("poll of a readable pipe: %s\n", result > 0 && (result & POLLIN) ? "POLLIN" : "not POLLIN");
  return 0;
}
