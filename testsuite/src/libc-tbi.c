// AArch64 Top Byte Ignore: what a program does with pointers that carry a tag in their top byte.
#include <stdint.h>
#include <sys/mman.h>
#include <unistd.h>

#define PR_SET_TAGGED_ADDR_CTRL 55
#define PR_GET_TAGGED_ADDR_CTRL 56
#define PR_TAGGED_ADDR_ENABLE 1

// `prctl`, which the libc of the tests doesn't have.
static long prctl(long option, long a, long b, long c, long d) {
  register long x8 __asm__("x8") = 167;
  register long x0 __asm__("x0") = option;
  register long x1 __asm__("x1") = a;
  register long x2 __asm__("x2") = b;
  register long x3 __asm__("x3") = c;
  register long x4 __asm__("x4") = d;
  __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4) : "memory");
  return x0;
}

static void *memory(size_t size) {
  return mmap(0, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
}

static void *tag(void *pointer, unsigned tag) {
  return (void *)(((uintptr_t)pointer & ((1ULL << 56) - 1)) | ((uintptr_t)tag << 56));
}

// A label and numbers on a line, without printf, which needs what this libc leaves out.
static void say(const char *label, int count, long a, long b, long c) {
  char line[96];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

__attribute__((noinline)) static int twice(int value) { return value * 2; }

int main(void) {
  long set = prctl(PR_SET_TAGGED_ADDR_CTRL, PR_TAGGED_ADDR_ENABLE, 0, 0, 0);
  long get = prctl(PR_GET_TAGGED_ADDR_CTRL, 0, 0, 0, 0);
  say("prctl", 2, set, get, 0);

  // Loads and stores through a tagged pointer reach what the untagged one does.
  volatile uint64_t *plain = memory(4096);
  volatile uint64_t *tagged = tag((void *)plain, 0x5a);
  tagged[1] = 0x1122334455667788ULL;
  plain[2] = 42;
  say("data", 2, plain[1] == 0x1122334455667788ULL, tagged[2] == 42, 0);

  // Bytes, pairs and an atomic through another tag.
  volatile uint8_t *bytes = tag((void *)plain, 0xf3);
  bytes[0] = 7;
  __atomic_fetch_add((uint64_t *)tag((void *)plain, 0x11), 5, __ATOMIC_SEQ_CST);
  say("bytes", 2, ((uint8_t *)plain)[0] == 12, bytes[0] == 12, 0);

  // Enough times round that the loop is compiled, with a tag that differs each time.
  volatile uint32_t *table = memory(4096);
  long sum = 0;
  for (int index = 0; index < 1000; index++) {
    volatile uint32_t *slot = tag((void *)(table + index % 64), index & 0x7f);
    *slot += index;
    sum += *slot;
  }
  say("loop", 2, sum, table[5], 0);

  // A call through a tagged function pointer goes where the untagged one does.
  int (*volatile function)(int) = tag((void *)twice, 0x77);
  say("call", 1, function(21), 0, 0);

  // The kernel takes a tagged buffer.
  char *message = memory(4096);
  for (int index = 0; index < 7; index++) message[index] = "kernel\n"[index];
  write(1, tag(message, 0x2c), 7);

  // And tagged ranges to protect and unmap.
  char *page = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  page[4096] = 1;
  int protect = mprotect(tag(page + 4096, 0x40), 4096, PROT_READ);
  int unmap = munmap(tag(page, 0x40), 4096);
  say("ranges", 3, protect, unmap, page[4096]);
  return 0;
}
