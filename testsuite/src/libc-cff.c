/* A flattened machine of a few handlers that a dispatcher chooses by a
   state in memory: one asks the kernel something and adds a byte of a
   file, one decides by another byte of it, and the rounds repeat before it ends and leaves a verdict. Another
   thread runs a machine of its own. It says where its dispatcher, its state,
   its record, its verdict and its sum are, and then what it decided. Given an argument, its first thread starts another that runs the
   rounds once the first is over, and leaves by pthread_exit, so that the process goes on without it. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <stdlib.h>
#include <unistd.h>

static volatile int state;
static volatile long acc;
static volatile char record[4];
static char data[16];
static __thread volatile int other;

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

/* What the dispatcher is: one round, by the state, which says whether it is over. */
__attribute__((noinline)) static int step(void) {
  switch (state) {
    case 1: acc += 3; state = 2; break;
    case 2: if (data[2] == 'C') state = 3; else state = 4; break;
    case 3: acc ^= getpid() & 0; acc += data[5] & 15; state = 5; break;
    case 4: acc += 9; state = 5; break;
    case 5: acc += 1; state = acc > 40 ? 6 : 1; break;
    case 6: record[0] = acc > 60 ? 'P' : 'F'; return 1;
  }
  return 0;
}

/* Where the verdict is looked at. */
__attribute__((noinline)) static void verdict_point(void) { __asm__ volatile("" ::: "memory"); }

static void *worker(void *ignored) {
  for (other = 0; other < 50; other++) acc += 0;
  return ignored;
}

static pthread_t leader;

/* The rounds, of a thread that isn't the first, once the first is over. */
static void *rounds(void *ignored) {
  pthread_join(leader, 0);
  state = 1;
  while (!step()) {}
  verdict_point();
  char line[] = {record[0], '\n'};
  write(1, line, 2);
  exit(0);
  return ignored;
}

int main(int argc, char **argv) {
  (void)argv;
  put_hex((unsigned long)step);
  put_hex((unsigned long)&state);
  put_hex((unsigned long)record);
  put_hex((unsigned long)verdict_point);
  put_hex((unsigned long)&acc);
  int fd = open("/data", O_RDONLY);
  pread(fd, data, 16, 0);
  close(fd);
  if (argc > 1) {
    leader = pthread_self();
    pthread_t runner;
    pthread_create(&runner, 0, rounds, 0);
    pthread_exit(0);
  }
  pthread_t thread;
  pthread_create(&thread, 0, worker, 0);
  state = 1;
  while (!step()) {}
  verdict_point();
  pthread_join(thread, 0);
  char line[] = {record[0], '\n'};
  write(1, line, 2);
  return 0;
}
