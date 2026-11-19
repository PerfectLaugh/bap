/* A byte of a file that a child of fork has in a register, as the parent had it there when it forked, and stores: the child's
   registers are its parent's, and so is where what is in them came from. The record says where it is on its first line. */

#define _GNU_SOURCE
#include <fcntl.h>
#include <sys/wait.h>
#include <unistd.h>

static volatile char record[4];
static char data[16];

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

/* What is passed in a register to the child, and only there: a fork with no wrapper to save it on the stack. */
__attribute__((noinline)) static long fork_now(void) {
#if defined(__x86_64__)
  long result;
  __asm__ volatile("syscall" : "=a"(result) : "a"(57) : "rcx", "r11", "memory");
  return result;
#elif defined(__aarch64__)
  register long x8 __asm__("x8") = 220, x0 __asm__("x0") = 17 /* SIGCHLD */, x1 __asm__("x1") = 0;
  __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1) : "memory");
  return x0;
#endif
}

int main(void) {
  put_hex((unsigned long)record);
  int fd = open("/data", O_RDONLY);
  pread(fd, data, 16, 0);
  close(fd);
  register char held __asm__(
#if defined(__x86_64__)
    "bl"
#else
    "w19"
#endif
  ) = data[10];
  __asm__ volatile("" : "+r"(held));
  long child = fork_now();
  __asm__ volatile("" : "+r"(held));
  if (!child) {
    record[0] = held;
    _exit(0);
  }
  int code;
  waitpid(child, &code, 0);
  record[1] = held;
  write(1, "done\n", 5);
  return 0;
}
