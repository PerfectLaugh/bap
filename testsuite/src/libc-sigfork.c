// What the child of fork has of the signals of the thread that made it: the handlers it is in, which it goes back from, and the
// alternate stack, which a child of vfork keeps too and a new thread doesn't have. It says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <signal.h>
#include <stddef.h>
#include <sys/wait.h>
#include <unistd.h>

static void say(const char *label, int count, long a, long b) {
  char line[128];
  size_t n = 0;
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

static char alternate[65536];

// Whether the alternate stack is the one above, and its flags.
static void sayAlternate(const char *label) {
  stack_t old;
  sigaltstack(0, &old);
  say(label, 2, old.ss_sp == alternate && old.ss_size == sizeof alternate, old.ss_flags);
}

// The status of the child, as its parent finds it.
static void sayChild(const char *label, int child) {
  int status = 0;
  waitpid(child, &status, 0);
  say(label, 2, WIFEXITED(status), WIFEXITED(status) ? WEXITSTATUS(status) : WTERMSIG(status));
}

static volatile int child = -1;

static void forks(int number) { child = fork(); }

static void forksOnAlternate(int number) {
  child = fork();
  if (child == 0) sayAlternate("child in a handler on the alternate stack: same alternate stack, flags");
}

static void *thread(void *unused) {
  stack_t old;
  sigaltstack(0, &old);
  say("new thread: alternate stack disabled", 1, old.ss_flags == SS_DISABLE, 0);
  return 0;
}

int main(void) {
  struct sigaction action = {0};
  action.sa_handler = forks;
  sigaction(SIGUSR1, &action, 0);
  raise(SIGUSR1);
  if (child == 0) { say("child back from the handler it was forked in", 0, 0, 0); _exit(7); }
  sayChild("fork in a handler: exited, code", child);

  stack_t given = {0};
  given.ss_sp = alternate;
  given.ss_size = sizeof alternate;
  say("sigaltstack", 1, sigaltstack(&given, 0), 0);
  child = fork();
  if (child == 0) { sayAlternate("child of fork: same alternate stack, flags"); _exit(0); }
  sayChild("fork: exited, code", child);

  child = vfork();
  if (child == 0) {
    stack_t old;
    sigaltstack(0, &old);
    _exit(old.ss_sp == alternate && old.ss_size == sizeof alternate && old.ss_flags == 0 ? 3 : 4);
  }
  sayChild("vfork: exited, code (3 if the same alternate stack)", child);

  pthread_t made;
  pthread_create(&made, 0, thread, 0);
  pthread_join(made, 0);
  sayAlternate("main thread after it: same alternate stack, flags");

  action.sa_handler = forksOnAlternate;
  action.sa_flags = SA_ONSTACK;
  sigaction(SIGUSR2, &action, 0);
  child = -1;
  raise(SIGUSR2);
  if (child == 0) { say("child back from the handler on the alternate stack", 0, 0, 0); _exit(9); }
  sayChild("fork in a handler on the alternate stack: exited, code", child);
  sayAlternate("parent back from it: same alternate stack, flags");

  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  raise(SIGUSR1);
  child = fork();
  if (child == 0) {
    sigset_t pending, mask;
    sigpending(&pending);
    sigprocmask(SIG_BLOCK, 0, &mask);
    say("child: SIGUSR1 pending, blocked", 2, sigismember(&pending, SIGUSR1), sigismember(&mask, SIGUSR1));
    _exit(0);
  }
  sayChild("fork with SIGUSR1 pending: exited, code", child);
  return 0;
}
