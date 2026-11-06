// A wait that a handled signal with SA_RESTART comes in the middle of goes on waiting, as Linux restarts it: waitid, wait4 and waitpid,
// each for a child that ends after the signal. It says what each wait gave, and that the handler ran.
#define _GNU_SOURCE
#include <signal.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a, long b) {
  char line[96];
  int n = 0;
  while (*label) line[n++] = *label++;
  long values[2] = {a, b};
  for (int index = 0; index < 2; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int count = 0;
    do { digits[count++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (count) line[n++] = digits[--count];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static volatile int alarms;
static void ring(int number) { (void)number; alarms++; }

// A child that ends with `code` after 100 ms, and a timer that rings after 30, while the parent waits.
static pid_t child(int code) {
  pid_t pid = fork();
  if (pid == 0) {
    struct timespec span = {0, 100000000};
    nanosleep(&span, 0);
    _exit(code);
  }
  struct itimerval timer;
  memset(&timer, 0, sizeof timer);
  timer.it_value.tv_usec = 30000;
  setitimer(ITIMER_REAL, &timer, 0);
  return pid;
}

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = ring;
  action.sa_flags = SA_RESTART;
  sigaction(SIGALRM, &action, 0);

  pid_t pid = child(5);
  siginfo_t info;
  memset(&info, 0, sizeof info);
  long result = syscall(SYS_waitid, P_PID, pid, &info, WEXITED, 0);
  say("waitid", result, info.si_status);

  int status = 0;
  pid = child(6);
  result = syscall(SYS_wait4, pid, &status, 0, 0);
  say("wait4", result == pid, WEXITSTATUS(status));

  status = 0;
  pid = child(7);
  result = waitpid(pid, &status, 0);
  say("waitpid", result == pid, WEXITSTATUS(status));
  say("alarms", alarms, 0);
  return 0;
}
