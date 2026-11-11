// MIPS's FCSR after floating point (testLinuxRaises): its flags, which stay, and Cause, bits 12 to 17, which is of the last operation
// alone: of what isn't exact, of a division by zero, of overflow and underflow, of what is invalid, and of what is exact after them.
#include <math.h>
#include <stdio.h>
#include <string.h>

#define OP(name, insn, A, B)                                                                                                             \
  do {                                                                                                                                   \
    volatile double va = (A), vb = (B);                                                                                                  \
    double a = va, b = vb, r;                                                                                                            \
    unsigned fcsr;                                                                                                                       \
    __asm__ volatile(insn " %0, %2, %3\n cfc1 %1, $31" : "=&f"(r), "=&r"(fcsr) : "f"(a), "f"(b));                                      \
    printf("%-16s fcsr %08x\n", name, fcsr);                                                                                             \
  } while (0)

int main(void) {
  __asm__ volatile("ctc1 $zero, $31");
  OP("add 1+1e-30", "add.d", 1.0, 1e-30);
  OP("add 1+1", "add.d", 1.0, 1.0);
  OP("div 1/0", "div.d", 1.0, 0.0);
  OP("mul big", "mul.d", 1e300, 1e300);
  OP("mul tiny", "mul.d", 1e-300, 1e-300);
  OP("sub inf-inf", "sub.d", INFINITY, INFINITY);
  OP("mul 2*3", "mul.d", 2.0, 3.0);
  __asm__ volatile("ctc1 $zero, $31");
  return 0;
}
