// Faults that a program ignores, and a handler that can't be entered, for what a machine says of them.
//   ignore: SIGSEGV is ignored, and then a load faults, after which it says that it went on.
//   nostack: the handler of SIGSEGV is to run on a stack that isn't there.
#include <signal.h>
#include <string.h>
#include <unistd.h>

static void handler(int signal) { (void)signal; _exit(3); }

int main(int argc, char **argv) {
  volatile int *nowhere = (volatile int *)16;
  if (argc > 1 && strcmp(argv[1], "ignore") == 0) {
    signal(SIGSEGV, SIG_IGN);
    int value = *nowhere;
    (void)value;
    write(1, "went on\n", 8);
    return 0;
  }
  stack_t stack = {0};
  stack.ss_sp = (void *)0x1000;
  stack.ss_size = 65536;
  sigaltstack(&stack, 0);
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  action.sa_flags = SA_ONSTACK;
  sigaction(SIGSEGV, &action, 0);
  int value = *nowhere;
  (void)value;
  return 0;
}
