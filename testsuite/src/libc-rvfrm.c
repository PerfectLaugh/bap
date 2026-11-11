// RISC-V of a rounding mode in frm that is reserved, 5 to 7 (testLinuxRaises): an instruction of the dynamic mode is illegal, which is
// SIGILL with ILL_ILLOPC at it, and one of its own mode isn't.
#define _GNU_SOURCE
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

static volatile int caught, code;

static void illegal(int signal, siginfo_t *info, void *context) {
  (void)signal;
  caught++;
  code = info->si_code;
  ucontext_t *state = context;
  state->uc_mcontext.__gregs[REG_PC] += 4;
}

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = illegal;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGILL, &action, 0);
  volatile float vx = 1.0f, vy = 3.0f;
  float x = vx, y = vy, r = 0;
  __asm__ volatile("csrwi frm, 5\n fdiv.s %0, %1, %2, dyn\n csrwi fcsr, 0" : "+f"(r) : "f"(x), "f"(y));
  printf("dynamic of frm 5: SIGILL %d, code %d\n", caught, code);
  caught = 0;
  __asm__ volatile("csrwi frm, 7\n fdiv.s %0, %1, %2, rne\n csrwi fcsr, 0" : "+f"(r) : "f"(x), "f"(y));
  unsigned bits;
  memcpy(&bits, &r, 4);
  printf("its own mode of frm 7: SIGILL %d, %08x\n", caught, bits);
  return 0;
}
