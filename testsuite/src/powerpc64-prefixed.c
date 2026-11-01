/* The prefixed instructions of Power10, whose eight bytes have to be fetched: arithmetic, loads and stores of each size at
   offsets too large for a word to hold, and what is relative to where it is. */
#include <stdio.h>
#include <string.h>

static unsigned char data[1 << 18];

#define LOAD(op, type) do { type value = 0; __asm__ volatile(op " %0, 100000(%1), 0" : "=r"(value) : "b"(base)); \
    printf(op " %llx\n", (unsigned long long)value); } while (0)
#define STORE(op, offset) do { __asm__ volatile(op " %0, " #offset "(%1), 0" :: "r"(pattern), "b"(base) : "memory"); } while (0)

int main(void) {
  unsigned char *base = data;
  for (unsigned i = 0; i < 64; i++) data[100000 + i] = (unsigned char)(0x81 + i * 3);
  long a = 5, b, c, g;
  __asm__ volatile("paddi %0, %1, 1000000, 0" : "=r"(b) : "b"(a));
  __asm__ volatile("paddi %0, %1, -1000000, 0" : "=r"(c) : "b"(a));
  __asm__ volatile("pli %0, 123456789" : "=r"(g));
  printf("%ld %ld %ld\n", b, c, g);
  LOAD("plbz", long); LOAD("plhz", long); LOAD("plha", long); LOAD("plwz", long); LOAD("plwa", long); LOAD("pld", long);

  double d = 0; float s = 0;
  __asm__ volatile("plfd %0, 100000(%1), 0" : "=d"(d) : "b"(base));
  __asm__ volatile("plfs %0, 100008(%1), 0" : "=f"(s) : "b"(base));
  unsigned long long dbits, sbits; memcpy(&dbits, &d, 8); memcpy(&sbits, &s, 4);
  printf("%llx %llx\n", dbits, sbits & 0xffffffffull);

  long pattern = 0x1122334455667788;
  STORE("pstb", 110000); STORE("psth", 110008); STORE("pstw", 110016); STORE("pstd", 110024);
  double e = 1.5; float f = 2.5f;
  __asm__ volatile("pstfd %0, 110032(%1), 0" :: "d"(e), "b"(base) : "memory");
  __asm__ volatile("pstfs %0, 110040(%1), 0" :: "f"(f), "b"(base) : "memory");
  for (unsigned i = 0; i < 48; i++) printf("%02x", data[110000 + i]);
  printf("\n");

  __asm__ volatile("plxv 34, 100000(%0), 0\n pstxv 34, 120000(%0), 0" :: "b"(base) : "vs34", "memory");
  __asm__ volatile("plxsd 3, 100000(%0), 0\n pstxsd 3, 120016(%0), 0" :: "b"(base) : "f3", "vs35", "memory");
  __asm__ volatile("plxssp 3, 100008(%0), 0\n pstxssp 3, 120024(%0), 0" :: "b"(base) : "f3", "vs35", "memory");
  for (unsigned i = 0; i < 28; i++) printf("%02x", data[120000 + i]);
  printf("\n");

  /* Relative to where it is, which the distance between two of them shows. */
  long first, second;
  __asm__ volatile("paddi %0, 0, 0, 1\n paddi %1, 0, 0, 1" : "=&r"(first), "=&r"(second));
  printf("%ld\n", second - first);
  long near;
  __asm__ volatile("pld %0, 12(0), 1\n b 12\n .quad 0x1234567890" : "=r"(near));
  printf("%lx\n", near);
  return 0;
}
