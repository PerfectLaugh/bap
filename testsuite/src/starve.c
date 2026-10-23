/* main yields to the thread, that the script creates, see
   tools/testsuite/inputs/emu/starve.ml, which calls tick, at which the
   script pauses the program each time, until main stops it, so main
   runs again, only if the pauses don't renew the time slice of the
   thread, and prints the number of the ticks, that it waited, and ok.
   It is built as spawn.c, see spawn.sh. */

int putchar(int);

#include "threads-arch.h"

volatile long stop, ticks, done;

int lock(volatile long *);

__attribute__((noinline)) void tick(void) { ticks++; }

/* the thread, that calls the external function, through its slot and
   its trampoline, at which the script pauses */
long locker(long arg) {
    while (!stop) lock(&ticks);
    done = 1;
    return 0;
}

long spinner(long arg) {
    while (!stop) tick();
    done = 1;
    return 0;
}

static void yield(void) { syscall6(SYS_sched_yield, 0, 0, 0, 0, 0, 0); }

int main(void) {
    yield();
    stop = 1;
    while (!done) yield();
    putchar(ticks > 0 ? 'o' : '-');
    putchar('k');
    putchar('\n');
    return 0;
}

void _start(void) { start_main((main_t)main); }
