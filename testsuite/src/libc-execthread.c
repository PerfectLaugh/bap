// execve of a process with more than one thread, as Linux has it: the thread that calls it, whether a thread that pthread_create made
// or the first, goes on as the whole process in the new program, with the id of the process, which getpid and gettid both say, and the
// same parent; the other threads are gone, even one blocked on a futex; and its parent waits for the same process to end. It says what
// it found, the same on each target. The program runs itself again by the path that it was run by. The libc of the tests has no
// execve, so it is called by number.
#define _GNU_SOURCE
#include <fcntl.h>
#include <pthread.h>
#include <stddef.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

static long number(const char *text) {
  long value = 0;
  while (*text >= '0' && *text <= '9') value = value * 10 + (*text++ - '0');
  return value;
}

static void decimal(char *out, long value) {
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) *out++ = digits[--d];
  *out = 0;
}

// How many threads the process has, by the entries of /proc/self/task.
static long threads(void) {
  int fd = open("/proc/self/task", O_RDONLY | O_DIRECTORY);
  if (fd < 0) return -1;
  char buffer[1024];
  long count = 0;
  for (;;) {
    long size = syscall(SYS_getdents64, fd, buffer, sizeof buffer);
    if (size <= 0) break;
    for (long at = 0; at < size;) {
      unsigned short length = *(unsigned short *)(buffer + at + 16);
      const char *name = buffer + at + 19;
      if (name[0] != '.') count++;
      at += length;
    }
  }
  close(fd);
  return count;
}

static const char *self;
static char *environment[] = {NULL};
static char parent[24];

static void run(const char *mode) {
  char *arguments[] = {(char *)self, (char *)mode, parent, NULL};
  syscall(SYS_execve, self, arguments, environment);
  _exit(99);
}

static void *execs(void *mode) {
  run(mode);
  return NULL;
}

static volatile int word;
static volatile int waiting;

static void *blocks(void *unused) {
  waiting = 1;
  for (;;) syscall(SYS_futex, &word, 0 /* FUTEX_WAIT */, 0, NULL, NULL, 0);
  return unused;
}

int main(int argc, char **argv) {
  if (argc > 2) {
    long pid = getpid();
    say(argv[1], 0);
    say("pid is tid", pid == syscall(SYS_gettid));
    say("same parent", getppid() == number(argv[2]));
    say("threads", threads());
    _exit(strcmp(argv[1], "thread") == 0 ? 7 : 8);
  }
  self = argv[0];
  decimal(parent, getpid());
  // A thread that pthread_create made runs a program, while the first waits for it to end.
  pid_t child = fork();
  if (child == 0) {
    pthread_t thread;
    pthread_create(&thread, NULL, execs, "thread");
    pthread_join(thread, NULL);
    _exit(98);
  }
  int status = 0;
  pid_t waited = waitpid(child, &status, 0);
  say("waited for the child", waited == child);
  say("exited", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  // The first thread runs a program, while another is blocked on a futex.
  child = fork();
  if (child == 0) {
    pthread_t thread;
    pthread_create(&thread, NULL, blocks, NULL);
    while (!waiting) sched_yield();
    for (int i = 0; i < 100; i++) sched_yield();
    run("first");
  }
  waited = waitpid(child, &status, 0);
  say("waited for the child", waited == child);
  say("exited", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
  return 0;
}
