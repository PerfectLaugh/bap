// Faults that a handler takes, again and again, each after some work, as a runtime with write barriers or guard pages has them: what the
// machine counts of what ran, which its fuel is, is all that ran, and not one instruction for each fault and nothing of the work before it
// (testLinuxFaultFuel).
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <string.h>
#include <unistd.h>

static sigjmp_buf back;

static void handler(int signal) { siglongjmp(back, signal); }

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  sigaction(SIGSEGV, &action, 0);
  for (volatile int round = 0; round < 1000; round++) {
    if (sigsetjmp(back, 1) == 0) {
      for (volatile int index = 0; index < 100; index++) {
      }
      *(volatile int *)16 = 1;
    }
  }
  write(1, "done\n", 5);
  return 0;
}
