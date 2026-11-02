/* What a run did and what went where: a dispatcher that comes to a deferred
   routine or doesn't by a byte of a file, a child that sends a byte back by a
   pipe, a byte through a file, a thread of its own and a pipe that ends. It
   says where things are, and then what it got, which is as on Linux. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <sys/mman.h>
#include <sys/wait.h>
#include <unistd.h>

static volatile char record[4];
static volatile int counted;
static char data[16];

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

__attribute__((noinline)) static void leaf(void) { counted++; }

__attribute__((noinline)) static void deferred(void) {
  leaf();
  counted += 100;
}

__attribute__((noinline)) static void ordinary(void) {
  counted += 10;
}

/* What a generated machine does: a table of handlers, and a state that says which. */
__attribute__((noinline)) static void dispatch(int state) {
  static void (*const table[])(void) = {ordinary, deferred};
  table[state]();
  counted += 1000;
}

__attribute__((noinline)) static void run_machine(char code) {
  int state = 0;
  if (code == 'C') state = 1;
  dispatch(state);
  counted += 10000;
}

static void *worker(void *ignored) {
  leaf();
  return 0;
}

int main(void) {
  put_hex((unsigned long)deferred);
  put_hex((unsigned long)leaf);
  put_hex((unsigned long)record);

  int fd = open("data", O_RDONLY);
  pread(fd, data, 16, 0);
  close(fd);

  run_machine(data[2]);

  pthread_t thread;
  pthread_create(&thread, 0, worker, 0);
  pthread_join(thread, 0);

  /* A byte to a child that it had, from it by a pipe, and the pipe ends when the child does. */
  int ends[2];
  pipe(ends);
  pid_t child = fork();
  if (!child) {
    close(ends[0]);
    write(ends[1], data + 0, 1);
    _exit(0);
  }
  close(ends[1]);
  char got = 0;
  read(ends[0], &got, 1);
  record[0] = got;
  char more = 'n';
  int last = read(ends[0], &more, 1);
  int code;
  waitpid(child, &code, 0);
  close(ends[0]);

  /* A byte to a file and back, in another descriptor. */
  int out = open("out", O_CREAT | O_RDWR | O_TRUNC, 0644);
  write(out, data + 1, 1);
  close(out);
  int in = open("out", O_RDONLY);
  char back = 0;
  read(in, &back, 1);
  close(in);
  record[1] = back;
  unlink("out");

  char line[] = {record[0], record[1], (char)('0' + last), '0' + WEXITSTATUS(code), more, '0' + counted / 10000, '0' + (counted / 100) % 10, '\n'};
  write(1, line, sizeof(line));

  /* A byte from a child by memory that they share. */
  volatile char *together = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  pid_t sharer = fork();
  if (!sharer) {
    *together = data[3];
    _exit(0);
  }
  waitpid(sharer, &code, 0);
  record[2] = *together;

  /* A pipe that no one reads, and one that says it doesn't wait. */
  int other[2];
  pipe2(other, O_NONBLOCK);
  char ignored;
  int empty = read(other[0], &ignored, 1);
  close(other[1]);
  int ended = read(other[0], &ignored, 1);
  char state[] = {empty == -1 ? 'a' : 'x', ended == 0 ? 'e' : 'x', '\n'};
  write(1, state, sizeof(state));
  return 0;
}
