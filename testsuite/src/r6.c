/* a freestanding program of the release 6 of MIPS, whose entry the
   lifters cases overwrite, see tools/testsuite/inputs/lifters */

int add(int a, int b) { return a + b; }
int pick(int c, int a, int b) { return c ? a : b; }

void _start(void) {
    volatile int r = pick(add(1, 2), 3, 4);
    (void)r;
    for (;;) {
    }
}
