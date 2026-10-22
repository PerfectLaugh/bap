/* Starts 4 threads with the system calls of Linux, clone and futex, as
   pthread does, which wait, as main does, until they all started, and
   main lets them go, without calls, so that the threads and main are
   preempted, and add to a counter, 2000 times each, under
   a lock of a futex, after which main joins them by their TIDs, which
   they clear, when they exit, and prints the counter, 8000, and ok, if
   the TIDs were distinct and gettid returned them. It links the
   stand-in libc of stub-libc.c, for putchar:

   T="--target=$TARGET -fuse-ld=lld -nostdlib -O1 -fno-builtin \
      -fno-unwind-tables -fno-asynchronous-unwind-tables"
   clang $T -shared -fPIC -Wl,-soname,libc.so.6 stub-libc.c -o libc.so.6
   clang $T -fno-pie -no-pie -Wl,--dynamic-linker=$LOADER \
     threads.c libc.so.6 -o ../bin/$TARGET-threads

   with TARGET=x86_64-linux-gnu and LOADER=/lib64/ld-linux-x86-64.so.2,
   and TARGET=aarch64-linux-gnu and LOADER=/lib/ld-linux-aarch64.so.1,
   and -mno-outline-atomics, as the stand-in libc has no atomics */

int putchar(int);
int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

#define THREADS 4
#define STEPS 2000

#define CLONE_VM 0x100
#define CLONE_FS 0x200
#define CLONE_FILES 0x400
#define CLONE_SIGHAND 0x800
#define CLONE_THREAD 0x10000
#define CLONE_SYSVSEM 0x40000
#define CLONE_PARENT_SETTID 0x100000
#define CLONE_CHILD_CLEARTID 0x200000

#if defined(__x86_64__)
#define SYS_futex 202
#define SYS_gettid 186
#define SYS_sched_yield 24

static long syscall3(long n, long a, long b, long c) {
    long r;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(n), "D"(a), "S"(b), "d"(c)
                     : "rcx", "r11", "memory");
    return r;
}

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    long r;
    register long r10 __asm__("r10") = d;
    register long r8 __asm__("r8") = e;
    register long r9 __asm__("r9") = f;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8),
                       "r"(r9)
                     : "rcx", "r11", "memory");
    return r;
}

/* the child runs fn(arg) on its stack, and exits */
static long spawn(long flags, void *stack, int *ptid, int *ctid,
                  void (*fn)(long), long arg) {
    long r;
    register long r10 __asm__("r10") = (long)ctid;
    register long r8 __asm__("r8") = 0;
    register long r12 __asm__("r12") = arg;
    register long r13 __asm__("r13") = (long)fn;
    __asm__ volatile("syscall\n"
                     "test %%rax, %%rax\n"
                     "jnz 1f\n"
                     "xor %%ebp, %%ebp\n"
                     "mov %%r12, %%rdi\n"
                     "call *%%r13\n"
                     "mov $60, %%eax\n"
                     "xor %%edi, %%edi\n"
                     "syscall\n"
                     "1:\n"
                     : "=a"(r)
                     : "a"(56), "D"(flags), "S"(stack), "d"(ptid), "r"(r10),
                       "r"(r8), "r"(r12), "r"(r13)
                     : "rcx", "r11", "memory");
    return r;
}
#elif defined(__aarch64__)
#define SYS_futex 98
#define SYS_gettid 178
#define SYS_sched_yield 124

static long syscall3(long n, long a, long b, long c) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    __asm__ volatile("svc #0"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2)
                     : "memory");
    return x0;
}

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    register long x3 __asm__("x3") = d;
    register long x4 __asm__("x4") = e;
    register long x5 __asm__("x5") = f;
    __asm__ volatile("svc #0"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5)
                     : "memory");
    return x0;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid,
                  void (*fn)(long), long arg) {
    register long x8 __asm__("x8") = 220;
    register long x0 __asm__("x0") = flags;
    register long x1 __asm__("x1") = (long)stack;
    register long x2 __asm__("x2") = (long)ptid;
    register long x3 __asm__("x3") = 0;
    register long x4 __asm__("x4") = (long)ctid;
    register long x19 __asm__("x19") = arg;
    register long x20 __asm__("x20") = (long)fn;
    __asm__ volatile("svc #0\n"
                     "cbnz x0, 1f\n"
                     "mov x29, #0\n"
                     "mov x0, x19\n"
                     "blr x20\n"
                     "mov x8, #93\n"
                     "mov x0, #0\n"
                     "svc #0\n"
                     "1:\n"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x19),
                       "r"(x20)
                     : "x30", "memory");
    return x0;
}
#endif

static void futex_wait(int *addr, int value) {
    syscall6(SYS_futex, (long)addr, 0, value, 0, 0, 0);
}

static void futex_wake(int *addr, int n) {
    syscall6(SYS_futex, (long)addr, 1, n, 0, 0, 0);
}

static int lock;
static volatile int started;
static volatile int go;
static int counter;
static int tids[THREADS];
static int seen[THREADS];
static char stacks[THREADS][16384] __attribute__((aligned(16)));

static void acquire(void) {
    while (__atomic_exchange_n(&lock, 1, __ATOMIC_ACQUIRE))
        futex_wait(&lock, 1);
}

static void release(void) {
    __atomic_store_n(&lock, 0, __ATOMIC_RELEASE);
    futex_wake(&lock, 1);
}

static void worker(long n) {
    /* without calls, until main lets it go, after all threads started,
       so that the threads and main are preempted */
    __atomic_add_fetch(&started, 1, __ATOMIC_SEQ_CST);
    while (!go)
        ;
    seen[n] = syscall3(SYS_gettid, 0, 0, 0);
    for (int i = 0; i < STEPS; i++) {
        acquire();
        int x = counter;
        if (i % 500 == 0) syscall3(SYS_sched_yield, 0, 0, 0);
        counter = x + 1;
        release();
    }
}

static void print(unsigned x) {
    char buf[16];
    int n = 0;
    do {
        buf[n++] = '0' + x % 10;
        x /= 10;
    } while (x);
    while (n) putchar(buf[--n]);
    putchar('\n');
}

int main(int argc, char **argv, char **envp) {
    long flags = CLONE_VM | CLONE_FS | CLONE_FILES | CLONE_SIGHAND |
                 CLONE_THREAD | CLONE_SYSVSEM | CLONE_PARENT_SETTID |
                 CLONE_CHILD_CLEARTID;
    int created[THREADS];
    for (int i = 0; i < THREADS; i++)
        created[i] = spawn(flags, stacks[i] + sizeof stacks[i], &tids[i],
                           &tids[i], worker, i);
    while (started < THREADS)
        ;
    go = 1;
    /* joins the threads, as pthread_join does */
    for (int i = 0; i < THREADS; i++) {
        int tid;
        while ((tid = __atomic_load_n(&tids[i], __ATOMIC_ACQUIRE)) != 0)
            futex_wait(&tids[i], tid);
    }
    print(counter);
    int ok = 1;
    for (int i = 0; i < THREADS; i++) {
        if (seen[i] != created[i]) ok = 0;
        for (int j = 0; j < i; j++)
            if (created[i] == created[j]) ok = 0;
    }
    if (ok) {
        putchar('o');
        putchar('k');
        putchar('\n');
    }
    return 0;
}

void _start(void) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
