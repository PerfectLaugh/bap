// A program whose PT_GNU_STACK asks for a stack that runs, as `-z execstack` does, runs code that it puts there, as Linux lets it
// (testLinuxRaises). zig doesn't take `-z execstack`, so `execstack.py` marks what it builds:
//   zig cc -target x86_64-linux-musl -static -O1 libc-execstack.c -o ../bin/x86_64-linux-musl-libc-execstack
//   python3 execstack.py ../bin/x86_64-linux-musl-libc-execstack
#include <stdio.h>

int main(void) {
  // `ret`, on the stack.
  volatile unsigned char code[16];
  code[0] = 0xc3;
  ((void (*)(void))code)();
  printf("code on the stack ran\n");
  return 0;
}
