/* Where bytes came from after what a tracker of them has to follow with care (testLinuxTaintReview). The record says where it is on
   its first line, and has:
   0, 1    of x86_64, bytes of an array that `rep stosb` filled with zeros, more of them than 65535, of which the second was of a file:
           both come from nothing;
   8..11   a register of a file taken from itself, by `eor` and by `sub`, of the whole register and of its low half: nothing;
   12      the byte that they were of, which comes from the file;
   16, 17  a byte that came from a file by way of a shared mapping of another, as `pread` reads it and as a private mapping of that has
           it: both from the first file;
   18      what `pwrite` wrote to the file, in the private mapping;
   24..31  the stack pointer of a thread, which is the argument of `clone` that gave it, read from a file;
   32..39  its thread pointer, the same, and of x86_64 a byte loaded through it at 32;
   40      of MIPS, the register after the arguments, which had a byte of a file before a call and has the flag of its result after. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

volatile unsigned char record[48];
/* What a thread that is made here has as its id until it ends, when the kernel clears it and wakes who waits for that. */
volatile int thread_id = 1;
static unsigned char data[256];

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

#if defined(__x86_64__)
#define LONG 66000
static unsigned char filled[LONG];

static void stosb(void *to, int value, unsigned long count) {
  __asm__ volatile("rep stosb" : "+D"(to), "+c"(count) : "a"(value) : "memory");
}

void idioms(unsigned char *from, volatile unsigned char *to);
__asm__(".globl idioms\nidioms:\n"
        " mov 96(%rdi), %rax\n xor %rax, %rax\n mov %al, 8(%rsi)\n"
        " mov 96(%rdi), %rax\n sub %rax, %rax\n mov %al, 9(%rsi)\n"
        " mov 96(%rdi), %eax\n xor %eax, %eax\n mov %al, 10(%rsi)\n"
        " mov 96(%rdi), %eax\n sub %eax, %eax\n mov %al, 11(%rsi)\n"
        " mov 96(%rdi), %al\n mov %al, 12(%rsi)\n"
        " ret\n");

/* CLONE_VM, FS, FILES, SIGHAND, THREAD, SYSVSEM, SETTLS and CHILD_CLEARTID: a thread, which stores where its stack is and a byte of
   its thread block, and ends. */
static void spawn(unsigned long stack, unsigned long tls) {
  register long r10 __asm__("r10") = (long)&thread_id;
  register long r8 __asm__("r8") = (long)tls;
  long result;
  __asm__ volatile("syscall\n"
                   "test %%rax, %%rax\n"
                   "jnz 1f\n"
                   "mov %%rsp, record+24(%%rip)\n"
                   "mov %%fs:0, %%al\n"
                   "mov %%al, record+32(%%rip)\n"
                   "mov $60, %%eax\n"
                   "xor %%edi, %%edi\n"
                   "syscall\n"
                   "1:\n"
                   : "=a"(result)
                   : "a"(56L), "D"(0x2d0f00L), "S"(stack), "d"(0L), "r"(r10), "r"(r8)
                   : "rcx", "r11", "memory");
}
#elif defined(__aarch64__)
void idioms(unsigned char *from, volatile unsigned char *to);
__asm__(".globl idioms\nidioms:\n"
        " ldr x3, [x0, #96]\n eor x3, x3, x3\n strb w3, [x1, #8]\n"
        " ldr x3, [x0, #96]\n sub x4, x3, x3\n strb w4, [x1, #9]\n"
        " ldr w3, [x0, #96]\n eor w4, w3, w3\n strb w4, [x1, #10]\n"
        " sub w4, w3, w3\n strb w4, [x1, #11]\n"
        " strb w3, [x1, #12]\n"
        " ret\n");

static void spawn(unsigned long stack, unsigned long tls) {
  register long x8 __asm__("x8") = 220;
  register long x0 __asm__("x0") = 0x2d0f00;
  register long x1 __asm__("x1") = (long)stack;
  register long x2 __asm__("x2") = 0;
  register long x3 __asm__("x3") = (long)tls;
  register long x4 __asm__("x4") = (long)&thread_id;
  __asm__ volatile("svc 0\n"
                   "cbnz x0, 1f\n"
                   "mov x9, sp\n"
                   "adrp x10, record\n"
                   "add x10, x10, :lo12:record\n"
                   "str x9, [x10, #24]\n"
                   "mrs x9, tpidr_el0\n"
                   "str x9, [x10, #32]\n"
                   "mov x8, #93\n"
                   "mov x0, #0\n"
                   "svc 0\n"
                   "1:\n"
                   : "+r"(x0)
                   : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4)
                   : "x9", "x10", "memory");
}
#elif defined(__arm__)
void idioms(unsigned char *from, volatile unsigned char *to);
__asm__(".globl idioms\n.type idioms, %function\nidioms:\n"
        " ldr r3, [r0, #96]\n eor r3, r3, r3\n strb r3, [r1, #8]\n"
        " ldr r3, [r0, #96]\n sub r2, r3, r3\n strb r2, [r1, #9]\n"
        " ldr r3, [r0, #96]\n eors r2, r3, r3\n strb r2, [r1, #10]\n"
        " rsb r2, r3, r3\n strb r2, [r1, #11]\n"
        " strb r3, [r1, #12]\n"
        " bx lr\n");
#endif

#if defined(__x86_64__) || defined(__aarch64__)
static unsigned char thread_stack[4096] __attribute__((aligned(16)));
static unsigned long thread_block[8];

static void mappings(void) {
  static unsigned char clean[64], back[8];
  for (int i = 0; i < 64; i++) clean[i] = 'c';
  int file = open("/g", O_CREAT | O_RDWR, 0600);
  write(file, clean, 64);
  unsigned char *private = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE, file, 0);
  unsigned char *shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, file, 0);
  shared[20] = data[80];
  pread(file, back, 2, 20);
  record[16] = back[0];
  record[17] = private[20];
  pwrite(file, data + 85, 1, 21);
  record[18] = private[21];
  /* What a thread is given, as bytes of the file: two addresses that differ, as the stack ends where the block starts. */
  unsigned long given[2] = {(unsigned long)(thread_stack + sizeof thread_stack), (unsigned long)(thread_block + 4)};
  pwrite(file, given, sizeof given, 32);
  pread(file, given, sizeof given, 32);
  spawn(given[0], given[1]);
  while (thread_id) syscall(SYS_futex, &thread_id, 0 /* FUTEX_WAIT */, 1, 0);
}
#endif

int main(void) {
  put_hex((unsigned long)record);
  int fd = open("/data", O_RDONLY);
  pread(fd, data, 256, 0);
#if defined(__x86_64__)
  pread(fd, filled + 100, 16, 32);
  pread(fd, filled + LONG - 100, 16, 96);
  stosb(filled, 0, LONG);
  record[0] = filled[101];
  record[1] = filled[LONG - 99];
#endif
  close(fd);
#if defined(__mips__)
  register long v0 __asm__("$2") = SYS_getpid;
  register long a3 __asm__("$7") = data[70];
  __asm__ volatile("syscall"
                   : "+r"(v0), "+r"(a3)
                   :
                   : "$1", "$3", "$8", "$9", "$10", "$11", "$12", "$13", "$14", "$15", "$24", "$25", "hi", "lo", "memory");
  record[40] = a3;
#else
  idioms(data, record);
#endif
#if defined(__x86_64__) || defined(__aarch64__)
  mappings();
#endif
  write(1, "done\n", 5);
  return 0;
}
