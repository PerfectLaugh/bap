// A program whose first segment doesn't start at the start of the file, as libc-elfphdr.ld lays it out: AT_PHDR is where its program
// headers are in memory, so that it finds them there. It says what it found, the same on each target.
// Built with the linker script:
//   python3 testsuite/musl/build.py TARGET testsuite/src/libc-elfphdr.c testsuite/bin/TARGET-linux-musl-libc-elfphdr -T testsuite/src/libc-elfphdr.ld
#include <elf.h>
#include <string.h>
#include <sys/auxv.h>
#include <unistd.h>

#if __LP64__
typedef Elf64_Phdr Phdr;
#else
typedef Elf32_Phdr Phdr;
#endif

static void say(const char *label, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

int main(void) {
  const Phdr *headers = (const Phdr *)getauxval(AT_PHDR);
  unsigned long count = getauxval(AT_PHNUM);
  say("headers", count);
  say("entry size", getauxval(AT_PHENT) == sizeof(Phdr));
  long loads = 0, self = 0;
  for (unsigned long index = 0; index < count; index++) {
    if (headers[index].p_type == PT_LOAD) loads++;
    if (headers[index].p_type == PT_PHDR) self = headers[index].p_vaddr == (unsigned long)headers;
  }
  say("first is PT_PHDR", headers[0].p_type == PT_PHDR);
  say("PT_PHDR is where they are", self);
  say("loads", loads);
  return 0;
}
