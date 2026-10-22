/* The odd uses of the threads, that the system calls of Linux create, as
   threads.c does, one after another, each of which prints its line:

   - taint: main passes a value of the secret to a thread, that clone
     creates, in a register, and the thread mixes the secret, after it
     waited on a futex, into the memory, which the scripts taint and
     check, see tools/testsuite/inputs/emu/threads-weird, where they
     also save the checkpoints, while the thread waits;
   - tls: the threads of CLONE_SETTLS read their own thread pointers,
     while they are preempted;
   - nested: a thread creates a thread, and joins it;
   - pingpong: two threads take turns on a futex, strictly;
   - errors: the futex, whose value differs, EAGAIN, the futex, that no
     thread wakes, with a timeout, ETIMEDOUT, clone without CLONE_VM,
     and clone3, which the emulator doesn't have, ENOSYS;
   - many: 24 threads, which yield;
   - orphan: main exits, with exit, not exit_group, and the last thread
     joins it, by the TID of set_tid_address, prints, and exits, with
     the code of the process, 7.

   It links the stand-in libc of stub-libc.c, for putchar, on each
   target of Linux, see threads.sh, with the system calls of
   threads-arch.h. */

int putchar(int);

#define CLONE_VM 0x100
#define CLONE_FS 0x200
#define CLONE_FILES 0x400
#define CLONE_SIGHAND 0x800
#define CLONE_THREAD 0x10000
#define CLONE_SYSVSEM 0x40000
#define CLONE_SETTLS 0x80000
#define CLONE_PARENT_SETTID 0x100000
#define CLONE_CHILD_CLEARTID 0x200000

#define THREAD                                                               \
    (CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND | CLONE_THREAD |      \
     CLONE_SYSVSEM | CLONE_PARENT_SETTID | CLONE_CHILD_CLEARTID)

#include "threads-arch.h"

static long futex_wait(int *addr, int value, void *timeout) {
    return syscall6(SYS_futex, (long)addr, 0, value, (long)timeout, 0, 0);
}

static void futex_wake(int *addr, int n) {
    syscall6(SYS_futex, (long)addr, 1, n, 0, 0, 0);
}

static void yield(void) { syscall6(SYS_sched_yield, 0, 0, 0, 0, 0, 0); }

static void put(const char *s) {
    while (*s) putchar(*s++);
}

static void print(long x) {
    char buf[24];
    int n = 0;
    unsigned long u = x < 0 ? -x : x;
    if (x < 0) putchar('-');
    do {
        buf[n++] = '0' + u % 10;
        u /= 10;
    } while (u);
    while (n) putchar(buf[--n]);
}

/* joins the thread, as pthread_join does */
static void join(int *tid) {
    int t;
    while ((t = __atomic_load_n(tid, __ATOMIC_ACQUIRE)) != 0)
        futex_wait(tid, t, 0);
}

static void set(int *x, int value) {
    __atomic_store_n(x, value, __ATOMIC_RELEASE);
    futex_wake(x, 1 << 30);
}

static void await(int *x, int value) {
    int v;
    while ((v = __atomic_load_n(x, __ATOMIC_ACQUIRE)) != value)
        futex_wait(x, v, 0);
}

#define STACK 16384
static char stacks[32][STACK] __attribute__((aligned(16)));
static int tids[32];

static long start(int i, void (*fn)(long), long arg) {
    return spawn(THREAD, stacks[i] + STACK - 64, &tids[i], &tids[i], 0, fn,
                 arg);
}

/* the marks of the scripts, which they pause at, whose arguments are
   the addresses of the data, that they taint and check */
__attribute__((noinline)) void taint_started(long *secret) {
    __asm__ volatile("" ::"r"(secret));
}
__attribute__((noinline)) void mixer_waits(void) { __asm__ volatile(""); }
__attribute__((noinline)) void taint_joined(long *inherited, long *mixed,
                                            long *clean) {
    __asm__ volatile("" ::"r"(inherited), "r"(mixed), "r"(clean));
}
__attribute__((noinline)) void pinged(void) { __asm__ volatile(""); }
__attribute__((noinline)) void orphaned(void) { __asm__ volatile(""); }

/* taint */

static long secret[2] = {0x1234, 0x5678};
static long mixed[2];
static long inherited;
static long clean;
static int mixer_go;
static int mixer_waiting;

static void mixer(long arg) {
    /* the argument is of the secret, in the register of the parent */
    inherited = arg;
    set(&mixer_waiting, 1);
    await(&mixer_go, 1);
    for (int i = 0; i < 2; i++) mixed[i] = secret[i] ^ 0x5a5a;
    clean = 42;
}

static void taint(void) {
    taint_started(secret);
    start(0, mixer, secret[0] + 1);
    await(&mixer_waiting, 1);
    /* the mixer waits on the futex, while main is at the mark */
    mixer_waits();
    set(&mixer_go, 1);
    join(&tids[0]);
    taint_joined(&inherited, mixed, &clean);
    put("taint ");
    print(mixed[0] ^ mixed[1] ^ inherited ^ clean);
    putchar('\n');
}

/* tls */

static long blocks[3][4];
static void *seen_tp[3];
static volatile int tls_started;

static void tls_worker(long n) {
    __atomic_add_fetch(&tls_started, 1, __ATOMIC_SEQ_CST);
    /* without calls, so that the threads are preempted */
    while (tls_started < 3)
        ;
    seen_tp[n] = thread_pointer();
}

static long main_block[4];

static void tls(void) {
    main_block[0] = (long)main_block;
    init_tls(main_block);
    void *before = thread_pointer();
    for (int i = 0; i < 3; i++) {
        blocks[i][0] = (long)blocks[i];
        spawn(THREAD | CLONE_SETTLS, stacks[i] + STACK - 64, &tids[i],
              &tids[i], tls_arg(i, blocks[i]), tls_worker, i);
    }
    for (int i = 0; i < 3; i++) join(&tids[i]);
    int ok = thread_pointer() == before;
    for (int i = 0; i < 3; i++)
        if (seen_tp[i] != blocks[i]) ok = 0;
    put(ok ? "tls ok\n" : "tls bad\n");
}

/* nested */

static int grandchild_tid;
static long nested_value;

static void grandchild(long x) { nested_value = x * 3; }

static void child(long x) {
    spawn(THREAD, stacks[1] + STACK - 64, &grandchild_tid, &grandchild_tid, 0,
          grandchild, x + 1);
    join(&grandchild_tid);
    nested_value += 1;
}

static void nested(void) {
    start(0, child, 13);
    join(&tids[0]);
    put("nested ");
    print(nested_value);
    putchar('\n');
}

/* pingpong */

#define ROUNDS 100
static int turn;
static char log_[2 * ROUNDS];
static int logged;

static void player(long me) {
    for (int i = 0; i < ROUNDS; i++) {
        await(&turn, me);
        log_[logged++] = me;
        if (me == 1 && i == ROUNDS / 2) pinged();
        set(&turn, 1 - me);
    }
}

static void pingpong(void) {
    start(0, player, 0);
    start(1, player, 1);
    join(&tids[0]);
    join(&tids[1]);
    int ok = logged == 2 * ROUNDS;
    for (int i = 0; i < logged; i++)
        if (log_[i] != i % 2) ok = 0;
    put(ok ? "pingpong ok\n" : "pingpong bad\n");
}

/* errors */

static void errors(void) {
    int x = 1;
    long timeout[2] = {0, 1000000};
    long eagain = futex_wait(&x, 2, 0);
    long etimedout = futex_wait(&x, 1, timeout);
    long fork = syscall6(SYS_clone, 17, 0, 0, 0, 0, 0);
    long clone3 = syscall6(SYS_clone3, 0, 0, 0, 0, 0, 0);
    put("errors ");
    print(eagain);
    putchar(' ');
    print(etimedout);
    putchar(' ');
    print(fork);
    putchar(' ');
    print(clone3);
    putchar('\n');
}

/* many */

#define MANY 24
static int total;

static void adder(long n) {
    for (int i = 0; i < 100; i++) {
        __atomic_add_fetch(&total, 1, __ATOMIC_SEQ_CST);
        if (i % 10 == n % 10) yield();
    }
}

static void many(void) {
    for (int i = 0; i < MANY; i++) start(i, adder, i);
    for (int i = 0; i < MANY; i++) join(&tids[i]);
    put("many ");
    print(total);
    putchar('\n');
}

/* orphan */

static int main_tid;

static void orphan_worker(long code) {
    /* joins main, whose TID set_tid_address cleared, when it exited */
    join(&main_tid);
    orphaned();
    put("orphan\n");
    syscall6(SYS_exit, code, 0, 0, 0, 0, 0);
}

static void orphan(void) {
    main_tid = syscall6(SYS_set_tid_address, (long)&main_tid, 0, 0, 0, 0, 0);
    start(0, orphan_worker, 7);
    syscall6(SYS_exit, 0, 0, 0, 0, 0, 0);
}

int main(int argc, char **argv, char **envp) {
    taint();
    tls();
    nested();
    pingpong();
    errors();
    many();
    orphan();
    return 1;
}

void _start(void) { start_main(main); }
