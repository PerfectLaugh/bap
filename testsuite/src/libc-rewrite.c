// Code that a program writes again at the same place, as a JIT does: an instruction of floating point there, then another, then the first
// again, each run as what it is now (testLinuxRewriteFloat), which is 5, 6 and 5.
#define _GNU_SOURCE
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>

// `fadd d0, d0, d1` or `fmul d0, d0, d1`, then `ret`.
static void put(uint32_t *code, uint32_t operation) {
  code[0] = operation;
  code[1] = 0xd65f03c0;
  __builtin___clear_cache((char *)code, (char *)(code + 2));
}

int main(void) {
  uint32_t *code = mmap(0, 4096, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  double (*run)(double, double) = (double (*)(double, double))code;
  uint32_t operations[] = {0x1e612800, 0x1e610800, 0x1e612800};
  for (int index = 0; index < 3; index++) {
    put(code, operations[index]);
    printf("%g\n", run(2, 3));
  }
  return 0;
}
