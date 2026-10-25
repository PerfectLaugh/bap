/* The threads of POSIX, whose functions the program imports, without
   the libc, that has them, as a payload does, which the executor runs,
   and the threads, that the program creates with clone itself, whose
   TIDs are their handles too:

   - two threads of pthread_create, whose results pthread_join gives;
   - a thread of clone, that pthread_detach detaches, once, and EINVAL
     after, as std::thread::detach does, while it runs, and another, that
     pthread_join joins, after it exited;
   - a detached thread of the attributes, that pthread_join can't join,
     EINVAL, and pthread_self, pthread_equal, and the joins of main, and
     of an unknown thread, EDEADLK and ESRCH;

   each of which prints its line, and ok. It links the stand-in libc of
   stub-libc.c, built with -DPTHREAD, whose functions of the threads
   fail, so that the emulator runs its own, see pthreads.sh, with the
   system calls of threads-arch.h. */

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

typedef unsigned long pthread_t;
typedef struct { long words[8]; } pthread_attr_t;

int pthread_create(pthread_t *, const pthread_attr_t *, void *(*)(void *),
                   void *);
int pthread_join(pthread_t, void **);
int pthread_detach(pthread_t);
pthread_t pthread_self(void);
int pthread_equal(pthread_t, pthread_t);
int pthread_attr_init(pthread_attr_t *);
int pthread_attr_setdetachstate(pthread_attr_t *, int);
int pthread_attr_destroy(pthread_attr_t *);

static void print(const char *s) {
    while (*s) putchar(*s++);
    putchar('\n');
}

static void check(const char *what, int ok) {
    print(what);
    print(ok ? "ok" : "failed");
}

#define STACK 16384
static char stacks[2][STACK] __attribute__((aligned(16)));
static int tids[2];
static volatile int counter;

static void *worker(void *arg) {
    __atomic_add_fetch(&counter, 1, __ATOMIC_SEQ_CST);
    return (void *)((long)arg * 10);
}

/* the threads, that wait, until main lets them go, so that they run,
   while main detaches and joins them */
static volatile int released[2];

static void hold(int i) {
    while (!released[i]) syscall6(SYS_sched_yield, 0, 0, 0, 0, 0, 0);
}

static void cloned(long n) { hold(0); }

static void *held(void *arg) {
    hold(1);
    return arg;
}

static int clone_thread(int i) {
    return spawn(THREAD, stacks[i] + STACK - 64, &tids[i], &tids[i], 0, cloned,
                 i);
}

static void created(void) {
    pthread_t a, b;
    void *ra = 0, *rb = 0;
    int ok = pthread_create(&a, 0, worker, (void *)1) == 0 &&
             pthread_create(&b, 0, worker, (void *)2) == 0 &&
             pthread_join(a, &ra) == 0 && pthread_join(b, &rb) == 0 &&
             (long)ra == 10 && (long)rb == 20 && !pthread_equal(a, b);
    check("created", ok);
}

static void mixed(void) {
    int detached = clone_thread(0);
    int joined = clone_thread(1);
    int ok = detached > 0 && pthread_detach(detached) == 0 &&
             pthread_detach(detached) == 22;
    released[0] = 1;
    while (__atomic_load_n(&tids[1], __ATOMIC_ACQUIRE) != 0)
        syscall6(SYS_sched_yield, 0, 0, 0, 0, 0, 0);
    void *r = (void *)1;
    ok = ok && pthread_join(joined, &r) == 0 && r == 0;
    check("cloned", ok);
}

static void attributes(void) {
    pthread_attr_t attr;
    pthread_t t;
    int ok = pthread_attr_init(&attr) == 0 &&
             pthread_attr_setdetachstate(&attr, 1) == 0 &&
             pthread_create(&t, &attr, held, 0) == 0 &&
             pthread_join(t, 0) == 22 && pthread_attr_destroy(&attr) == 0;
    released[1] = 1;
    pthread_t self = pthread_self();
    ok = ok && pthread_equal(self, pthread_self()) &&
         pthread_join(self, 0) == 35 && pthread_join(9999, 0) == 3;
    check("attributes", ok);
}

int main(int argc, char **argv, char **envp) {
    created();
    mixed();
    attributes();
    return 0;
}

void _start(void) { start_main(main); }
