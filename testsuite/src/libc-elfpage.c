// A program whose code and data are in segments that share a page, as libc-elfpage.ld lays them out: the page has the bytes of the
// file and the protection of the data, which is writable and executable. It says what it found, the same on each target.
// Built with the linker script:
//   python3 testsuite/musl/build.py TARGET testsuite/src/libc-elfpage.c testsuite/bin/TARGET-linux-musl-libc-elfpage -T testsuite/src/libc-elfpage.ld
#include <string.h>
#include <unistd.h>

static void say(const char *label, const char *text, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  if (text) { line[n++] = ' '; for (size_t i = 0; text[i]; i++) line[n++] = text[i]; }
  if (value >= 0) {
    line[n++] = ' ';
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

int counter = 41;
char message[] = "data";
static const char constant[] = "constant";

int main(void) {
  say("data", message, counter);
  say("constant", constant, -1);
  counter++;
  message[0] = 'D';
  say("written", message, counter);
  return 0;
}
