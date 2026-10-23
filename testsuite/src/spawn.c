/* main waits, until the two threads, that the script creates with
   Bap_emu.spawn_thread, see tools/testsuite/inputs/emu/spawn, wrote
   their results, and yields to them, so that they return, and exit,
   and prints the results, 11 and 21, of the arguments, 1 and 2. It
   links the stand-in libc of stub-libc.c, for putchar, see spawn.sh,
   with the system calls of threads-arch.h. */

int putchar(int);

#include "threads-arch.h"

volatile long out[3];

long worker(long arg) {
    out[arg] = arg * 10 + 1;
    return arg;
}

static void yield(void) { syscall6(SYS_sched_yield, 0, 0, 0, 0, 0, 0); }

static void print(long x) {
    if (x >= 10) print(x / 10);
    putchar('0' + x % 10);
}

int main(void) {
    while (!out[1] || !out[2]) yield();
    for (int i = 0; i < 20; i++) yield();
    print(out[1]);
    putchar(' ');
    print(out[2]);
    putchar('\n');
    return 0;
}

void _start(void) { start_main((main_t)main); }
