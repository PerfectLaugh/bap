/* Prefixed instructions of Power10, whose eight bytes have to be fetched. */
#include <stdio.h>
static long table[4] = {11, 22, 33, 44};
int main(void) {
  long a = 5, b = 0, c = 0, d = 0;
  __asm__ volatile("paddi %0, %1, 1000000, 0" : "=r"(b) : "b"(a));
  __asm__ volatile("pli %0, 123456789" : "=r"(c));
  __asm__ volatile("pld %0, 8(%1), 0" : "=r"(d) : "b"(table));
  long e = 0; __asm__ volatile("plwz %0, 16(%1), 0" : "=r"(e) : "b"(table));
  long f = 7; __asm__ volatile("pstd %0, 24(%1), 0" :: "r"(f), "b"(table) : "memory");
  long g = 0; __asm__ volatile("paddi %0, 0, 0, 1" : "=r"(g));
  printf("%ld %ld %ld %ld %ld %d\n", b, c, d, e, table[3], g != 0);
  return 0;
}
