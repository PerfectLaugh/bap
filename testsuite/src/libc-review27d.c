// What a program wrote before its run ends in an error of the machine, here of a byte that is no instruction of 64 bits, is said
// before the error is, rather than lost with the turn that it was written in.
#include <unistd.h>
int main(void) {
  write(1, "said before the end\n", 20);
  __asm__ volatile(".byte 0x06");
  return 0;
}
