#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
/* Code that a program writes, runs until it is hot, and changes under itself: in the middle of an instruction, in an instruction after
   a loop, and by a whole new function, and that writes bytes around itself as a program that decrypts itself does. Whatever is stale
   of what was compiled changes the sum. */
typedef long (*fn)(long);
static volatile unsigned char *code;
static const unsigned char body[] = {
  0x48, 0x89, 0xf8,                   /* mov %rdi, %rax */
  0xb9, 0x03, 0x00, 0x00, 0x00,       /* mov $3, %ecx */
  0x48, 0x83, 0xc0, 0x05,             /* 1: add $5, %rax  (the immediate is at 11) */
  0xff, 0xc9,                         /* dec %ecx */
  0x75, 0xf8,                         /* jne 1b */
  0x48, 0x83, 0xf0, 0x07,             /* xor $7, %rax  (the immediate is at 19) */
  0xc3 };
/* A loop that patches the immediate of its own next block on each turn, with nothing between them to look at the bytes once it is one
   compiled range: only stopping the range for that write gives the right sum. */
static const unsigned char patching[] = {
  0x31, 0xc0,                         /* xor %eax, %eax */
  0x31, 0xd2,                         /* xor %edx, %edx */
  0x88, 0x15, 0x05, 0x00, 0x00, 0x00, /* 1: mov %dl, 5(%rip), which is the immediate of the add */
  0xeb, 0x00,                         /* jmp 2f */
  0x48, 0x83, 0xc0, 0x00,             /* 2: add $0, %rax */
  0xff, 0xc2,                         /* inc %edx */
  0x39, 0xfa,                         /* cmp %edi, %edx */
  0x75, 0xee,                         /* jne 1b */
  0xc3 };
int main(void) {
  code = mmap(0, 65536, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  for (unsigned i = 0; i < sizeof body; i++) code[i] = body[i];
  long total = 0;
  for (int round = 0; round < 3000; round++) {
    if (round % 7 == 0) code[11] = 1 + round % 50;
    if (round % 11 == 0) code[19] = round % 100;
    if (round % 500 == 499) { code[12] = 0x90; code[13] = 0xff; code[12] = 0xff; code[13] = 0xc9; }
    code[4096 + round % 4096] = round;
    total = total * 3 + ((fn)code)(round);
    total &= 0xffffffffffffL;
  }
  for (unsigned i = 0; i < sizeof patching; i++) code[8192 + i] = patching[i];
  total += ((fn)(code + 8192))(20000);
  printf("%ld\n", total);
  /* In the same page as what runs, and a new function over it. */
  for (int i = 0; i < 4096; i++) code[1024 + i] = i;
  code[0] = 0xb8; code[1] = 42; code[2] = 0; code[3] = 0; code[4] = 0; code[5] = 0xc3;
  total += ((fn)code)(0);
  printf("%ld\n", total);
  return 0; }
