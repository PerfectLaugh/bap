// vfork: the child has the parent's memory, and the parent waits until it ends or runs a program, which then has memory of its own.
// It says what it found, the same on each target. The libc of the tests has no execve, so it is called by number.
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static volatile long shared = 0;

int main(int argc, char **argv) {
  if (argc > 1) {
    // The program that a child of vfork runs, in memory of its own: what it writes isn't the parent's.
    shared = 99;
    say("the program runs", 1, shared, 0);
    return 5;
  }
  int status = 0;
  // What the child writes, the parent sees, as it is the same memory, and the parent goes on once the child is over.
  pid_t child = vfork();
  if (child == 0) {
    for (long index = 0; index < 100000; index++) shared++;
    _exit(7);
  }
  say("the parent sees what the child wrote", 1, shared, 0);
  waitpid(child, &status, 0);
  say("and it ended with", 1, WEXITSTATUS(status), 0);
  // A child that runs a program lets the parent go on, with its memory as it was.
  long mine = 1234;
  child = vfork();
  if (child == 0) {
    char *arguments[] = {argv[0], "child", 0};
    char *environment[] = {0};
    syscall(SYS_execve, argv[0], arguments, environment);
    _exit(1);
  }
  waitpid(child, &status, 0);
  say("the parent goes on as it was", 2, mine, shared);
  say("and the program ended with", 1, WEXITSTATUS(status), 0);
  return 0;
}
