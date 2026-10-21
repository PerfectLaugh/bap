/* the tables of the pointers of a position-independent executable,
   which the RELATIVE relocations fix up, and an indirect function,
   whose resolver the IRELATIVE relocation calls */
#include "common.h"

static int one(void) { return 1; }
static int two(void) { return 2; }
static int three(void) { return 3; }
static int (*const table[])(void) = { one, two, three };
static const char *const names[] = { "first", "second", "third" };

static int fast(void) { return 0x10; }
static int (*resolve(void))(void) { return fast; }
int chosen(void) __attribute__((ifunc("resolve")));

int main(void) {
    int sum = 0;
    for (int i = 0; i < 3; i++) sum += table[i]();
    line("table", sum);
    print(names[2]);
    putchar('\n');
    line("ifunc", chosen());
    return 0;
}

void _start(void) { exit(main()); }
