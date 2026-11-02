/* A status that a check decides, by way of flattened control flow, a
   transformation with vectors and a copy into a record, next to bytes that
   come from elsewhere. The record says where it is on its first line. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

typedef unsigned char u8x16 __attribute__((vector_size(16)));

/* The record: 0 and 1 are bytes 7 and 8 of a file, 4 is the status, 5 is a
   constant, 6 is byte 3 of the file by way of a thread and 7 is what a child can't change. */
static volatile char record[8];
static volatile char from_thread;
static char data[16];

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

/* TracerPid from /proc, as a check against a debugger reads it. */
__attribute__((noinline)) static int tracer(void) {
  static char text[4096];
  int fd = open("/proc/self/status", O_RDONLY);
  int size = read(fd, text, sizeof(text) - 1);
  close(fd);
  text[size < 0 ? 0 : size] = 0;
  for (char *at = text; *at; at++) {
    if (!strncmp(at, "TracerPid:", 10)) {
      at += 10;
      while (*at == ' ' || *at == '\t') at++;
      int value = 0;
      while (*at >= '0' && *at <= '9') value = value * 10 + (*at++ - '0');
      return value;
    }
  }
  return -1;
}

/* What was a tree of ifs, flattened into a loop over a state. */
__attribute__((noinline)) static char verdict(int traced) {
  volatile int state = 3;
  char result = 0;
  for (;;) {
    switch (state) {
      case 3: state = traced == 0 ? 7 : 11; break;
      case 7: result = '1'; state = 5; break;
      case 11: result = '0'; state = 5; break;
      case 5: return result;
    }
  }
}

struct variant { int which; char text[16]; };

__attribute__((noinline)) static void transform(struct variant *out, const char *in) {
  u8x16 key = {0x5a, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15}, block;
  memcpy(&block, in, 16);
  volatile u8x16 sealed = block ^ key;
  block = sealed ^ key;
  out->which = 2;
  for (int i = 0; i < 16; i++) out->text[i] = ((volatile unsigned char *)&block)[i];
}

static void *worker(void *ignored) {
  from_thread = data[3];
  return 0;
}

int main(void) {
  put_hex((unsigned long)record);
  char status = verdict(tracer());
  char serial[16] = {0};
  serial[4] = status;
  struct variant first, second;
  transform(&first, serial);
  second = first;

  int fd = open("/data", O_RDONLY);
  pread(fd, data, 16, 0);
  close(fd);
  record[0] = data[7];
  record[1] = data[8];
  record[4] = second.text[4];
  record[5] = 'z';
  record[7] = 'p';

  pthread_t thread;
  pthread_create(&thread, 0, worker, 0);
  pthread_join(thread, 0);
  record[6] = from_thread;

  pid_t child = fork();
  if (!child) {
    record[7] = data[9];
    record[4] = 'c';
    _exit(0);
  }
  int code;
  waitpid(child, &code, 0);
  write(1, (const char *)record + 4, 1);
  write(1, "\n", 1);
  return 0;
}
