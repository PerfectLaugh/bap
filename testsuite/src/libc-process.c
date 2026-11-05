// Who a process is: process groups and sessions, a signal and a wait of a group, the ids of users and groups of one that gives up
// root, its capabilities, the limit of descriptors, its nice value, the scheduler, and clone3. It says what it found, the same on each
// target, as a process that isn't root. The libc of the tests has none of these but kill, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdint.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int digit = 0;
    do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (digit) line[n++] = digits[--digit];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d) {
  long result = syscall(number, a, b, c, d, 0L, 0L);
  return result < 0 ? -errno : result;
}

static void sleepMs(long ms) {
  struct timespec span = { ms / 1000, ms % 1000 * 1000000 };
  nanosleep(&span, 0);
}

#if defined(SYS_getuid32)
#define UID(name) SYS_##name##32
#else
#define UID(name) SYS_##name
#endif

static pid_t self(void) { return (pid_t)call(SYS_getpid, 0, 0, 0, 0); }

static int waitFor(pid_t pid) {
  int status = 0;
  pid_t got = (pid_t)call(SYS_wait4, pid, (long)&status, 0, 0);
  if (got < 0) return got;
  return WIFSIGNALED(status) ? -WTERMSIG(status) : WEXITSTATUS(status);
}

int main(void) {
  // A process that makes a group of its own, and a session.
  pid_t child = fork();
  if (child == 0) {
    long made = call(SYS_setpgid, 0, 0, 0, 0);
    long own = call(SYS_getpgid, 0, 0, 0, 0) == self();
    long leader = call(SYS_setsid, 0, 0, 0, 0) == -EPERM;
    _exit(made == 0 && own && leader ? 0 : 1);
  }
  say("a group of its own, of which it can't make a session", 1, waitFor(child), 0, 0);
  child = fork();
  if (child == 0) {
    long session = call(SYS_setsid, 0, 0, 0, 0);
    _exit(session == self() && call(SYS_getsid, 0, 0, 0, 0) == self() && call(SYS_getpgid, 0, 0, 0, 0) == self() ? 0 : 1);
  }
  say("a session", 1, waitFor(child), 0, 0);

  // A group of two that a signal ends, and a wait of a group, which leaves the others.
  pid_t first = fork();
  if (first == 0) { call(SYS_setpgid, 0, 0, 0, 0); for (;;) sleepMs(1000); }
  call(SYS_setpgid, first, first, 0, 0);
  pid_t second = fork();
  if (second == 0) { call(SYS_setpgid, 0, first, 0, 0); for (;;) sleepMs(1000); }
  call(SYS_setpgid, second, first, 0, 0);
  pid_t other = fork();
  if (other == 0) { sleepMs(50); _exit(4); }
  sleepMs(10);
  say("kill of a group", 1, call(SYS_kill, -first, SIGTERM, 0, 0), 0, 0);
  int ended = 0;
  for (int index = 0; index < 2; index++) {
    int status = 0;
    pid_t got = (pid_t)call(SYS_wait4, -first, (long)&status, 0, 0);
    if ((got == first || got == second) && WIFSIGNALED(status) && WTERMSIG(status) == SIGTERM) ended++;
  }
  say("ends each of it", 2, ended, call(SYS_wait4, -first, 0, WNOHANG, 0) == -ECHILD, 0);
  say("and the rest goes on", 1, waitFor(other), 0, 0);

  // A process that gives up root, which then can't take it back, nor have more than it has.
  child = fork();
  if (child == 0) {
    long gave = call(UID(setresgid), 1000, 1000, 1000, 0) | call(UID(setresuid), 1000, 1000, 1000, 0);
    unsigned int real = 0, effective = 0, saved = 0;
    call(UID(getresuid), (long)&real, (long)&effective, (long)&saved, 0);
    long ids = gave == 0 && real == 1000 && effective == 1000 && saved == 1000 && call(UID(getuid), 0, 0, 0, 0) == 1000;
    // Refused: EPERM, or EINVAL where the uid has no mapping, as in a namespace of one user.
    long back = call(UID(setuid), 65534, 0, 0, 0) < 0 && call(UID(setgroups), 0, 0, 0, 0) == -EPERM;
    struct { uint32_t version; int pid; } header = { 0x20080522, 0 };
    struct { uint32_t effective, permitted, inheritable; } capabilities[2] = {{1, 1, 1}, {1, 1, 1}};
    long none = call(SYS_capget, (long)&header, (long)capabilities, 0, 0) == 0 && capabilities[0].effective == 0 && capabilities[1].permitted == 0;
    // A nice value that it may give up, and not take back.
    long nicer = call(SYS_setpriority, 0, 0, 5, 0) == 0 && call(SYS_getpriority, 0, 0, 0, 0) == 15 && call(SYS_setpriority, 0, 0, 0, 0) == -EACCES;
    _exit((ids ? 1 : 0) | (back ? 2 : 0) | (none ? 4 : 0) | (nicer ? 8 : 0));
  }
  say("who it is when it gives up root", 1, waitFor(child), 0, 0);

  // No descriptor past RLIMIT_NOFILE.
  child = fork();
  if (child == 0) {
    struct { uint64_t soft, hard; } limit = { 16, 16 }, old;
    call(SYS_prlimit64, 0, 7, (long)&limit, 0);
    call(SYS_prlimit64, 0, 7, 0, (long)&old);
    int last = 0;
    long result = 0;
    while ((result = call(SYS_dup, 0, 0, 0, 0)) >= 0) last = (int)result;
    _exit(old.soft == 16 && last == 15 && result == -EMFILE ? 0 : 1);
  }
  say("the limit of descriptors", 1, waitFor(child), 0, 0);

  // The scheduler, of one processor.
  say("priorities of SCHED_FIFO", 2, call(SYS_sched_get_priority_max, 1, 0, 0, 0), call(SYS_sched_get_priority_min, 1, 0, 0, 0), 0);
  say("SCHED_OTHER", 1, call(SYS_sched_getscheduler, 0, 0, 0, 0), 0, 0);
  unsigned long cpus = 1;
  say("sched_setaffinity", 1, call(SYS_sched_setaffinity, 0, sizeof cpus, (long)&cpus, 0), 0, 0);

  // clone3 of a process, without a stack of its own.
  struct { uint64_t flags, pidfd, child, parent, exitSignal, stack, size, tls; } arguments = { 0, 0, 0, 0, SIGCHLD, 0, 0, 0 };
  long made = call(SYS_clone3, (long)&arguments, sizeof arguments, 0, 0);
  if (made == 0) _exit(9);
  say("clone3", 2, made > 0, waitFor((pid_t)made), 0);
  return 0;
}
