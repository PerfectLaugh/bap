/* A mapping much bigger than what it uses: it touches a byte at each end and in the middle, cuts a page out of it to guard, and a
   hole, and then stops where it says, to be looked at, before it checks what it reads and says whether that was right. */

#define _GNU_SOURCE
#include <sys/mman.h>
#include <unistd.h>

static void put_hex(unsigned long value) {
  char out[32];
  int n = 0;
  out[n++] = '@';
  for (int shift = sizeof(value) * 8 - 4; shift >= 0; shift -= 4) out[n++] = "0123456789abcdef"[(value >> shift) & 15];
  out[n++] = '\n';
  write(1, out, n);
}

/* Where it is looked at. */
__attribute__((noinline)) static void pause_point(void) { __asm__ volatile("" ::: "memory"); }

int main(void) {
  put_hex((unsigned long)pause_point);
  unsigned long size = sizeof(long) == 8 ? 1UL << 30 : 1UL << 28;
  volatile unsigned char *p = mmap(0, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (p == MAP_FAILED) return 1;
  p[0] = 1;
  p[size / 2] = 2;
  p[size - 1] = 3;
  if (mprotect((void *)(p + 4096 * 10), 4096, PROT_NONE)) return 2;
  if (munmap((void *)(p + size / 4), 4096 * 16)) return 3;
  pause_point();
  int right = p[0] == 1 && p[size / 2] == 2 && p[size - 1] == 3 && p[4096 * 11] == 0 && p[12345] == 0 && p[size / 4 + 4096 * 16] == 0;
  char line[] = {right ? 'y' : 'n', '\n'};
  write(1, line, 2);
  return 0;
}
