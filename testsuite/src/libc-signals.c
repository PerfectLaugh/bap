/* What a program sees of signals, on real Linux and on the machine of Bap.Linux, which have to agree. It prints no addresses and
   nothing that a target has a number of its own for, so that every target says the same, and it needs no floating point, which
   lets it link without compiler-rt:

     zig cc -target aarch64-linux-musl -static -O1 libc-signals.c -o ../bin/aarch64-linux-musl-libc-signals */

#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <sched.h>
#include <semaphore.h>
#include <setjmp.h>
#include <signal.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>

static void say(const char *text) { write(1, text, strlen(text)); }

static void number(long value) {
    char buf[24];
    int n = sizeof buf;
    int negative = value < 0;
    unsigned long left = negative ? -(unsigned long)value : (unsigned long)value;
    do {
        buf[--n] = '0' + (int)(left % 10);
        left /= 10;
    } while (left);
    if (negative) buf[--n] = '-';
    write(1, buf + n, sizeof buf - n);
}

static void line(const char *label, long value) {
    say(label);
    say(" ");
    number(value);
    say("\n");
}

static pid_t gettid_(void) { return syscall(SYS_gettid); }

static volatile sig_atomic_t count, other, last, depth, deepest;
static volatile int order[8];
static volatile int orders;

static void plain(int sig) {
    count++;
    last = sig;
}
static void noted(int sig) { order[orders++] = sig == SIGUSR1 ? 1 : 2; }

static void use(int sig, void (*handler)(int), int flags) {
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_handler = handler;
    action.sa_flags = flags;
    sigemptyset(&action.sa_mask);
    sigaction(sig, &action, 0);
}

static void useInfo(int sig, void (*handler)(int, siginfo_t *, void *), int flags) {
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_sigaction = handler;
    action.sa_flags = flags | SA_SIGINFO;
    sigemptyset(&action.sa_mask);
    sigaction(sig, &action, 0);
}

static void reset(void) {
    count = other = last = depth = deepest = 0;
    orders = 0;
}

static void blockOnly(int sig, sigset_t *old) {
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, sig);
    sigprocmask(SIG_BLOCK, &set, old);
}

/* Handlers. */

static volatile int infoSigno, infoCode, infoPidOk, infoStatus, infoSelfBlocked, infoContext, infoValue;
static void informed(int sig, siginfo_t *info, void *context) {
    sigset_t now;
    infoSigno = info->si_signo == sig;
    infoCode = info->si_code;
    infoPidOk = info->si_pid == getpid();
    infoValue = info->si_value.sival_int;
    infoContext = context != 0;
    sigprocmask(SIG_BLOCK, 0, &now);
    infoSelfBlocked = sigismember(&now, sig);
    count++;
}

static void masking(int sig) {
    (void)sig;
    noted(SIGUSR1);
    raise(SIGUSR2);
    noted(SIGUSR1);
}

static void recursive(int sig) {
    depth++;
    if (depth > deepest) deepest = depth;
    if (depth < 3) raise(sig);
    depth--;
}

/* What is in registers and in memory across a handler is as it was. */
static void clobbering(int sig) {
    volatile long junk[32];
    for (int i = 0; i < 32; i++) junk[i] = i * sig;
    count += (int)junk[3] * 0 + 1;
}

static volatile long threadTid, threadSawTid;
static void whoAmI(int sig) {
    (void)sig;
    threadSawTid = gettid_();
    count++;
}

static sigjmp_buf back;
static volatile int faultCode, faultAddressOk;
static void *volatile faultAddress;
static void faulted(int sig, siginfo_t *info, void *context) {
    (void)sig;
    (void)context;
    faultCode = info->si_code;
    faultAddressOk = info->si_addr == faultAddress;
    count++;
    siglongjmp(back, 1);
}

/* The context of a handler is where the program goes when it returns, and what it changes there goes. */
static unsigned long pcOf(ucontext_t *context) {
#if defined(__x86_64__)
    return context->uc_mcontext.gregs[REG_RIP];
#elif defined(__i386__)
    return context->uc_mcontext.gregs[REG_EIP];
#elif defined(__aarch64__)
    return context->uc_mcontext.pc;
#elif defined(__arm__)
    return context->uc_mcontext.arm_pc;
#elif defined(__riscv)
    return context->uc_mcontext.__gregs[0];
#elif defined(__mips__)
    return context->uc_mcontext.pc;
#elif defined(__powerpc64__)
    return context->uc_mcontext.gp_regs[32];
#elif defined(__powerpc__)
    return context->uc_mcontext.gregs[32];
#endif
}

static void setPc(ucontext_t *context, unsigned long pc) {
#if defined(__x86_64__)
    context->uc_mcontext.gregs[REG_RIP] = pc;
#elif defined(__i386__)
    context->uc_mcontext.gregs[REG_EIP] = pc;
#elif defined(__aarch64__)
    context->uc_mcontext.pc = pc;
#elif defined(__arm__)
    context->uc_mcontext.arm_pc = pc & ~1ul;
    if (pc & 1) context->uc_mcontext.arm_cpsr |= 0x20;
    else context->uc_mcontext.arm_cpsr &= ~0x20ul;
#elif defined(__riscv)
    context->uc_mcontext.__gregs[0] = pc;
#elif defined(__mips__)
    context->uc_mcontext.pc = pc;
#elif defined(__powerpc64__)
    context->uc_mcontext.gp_regs[32] = pc;
#elif defined(__powerpc__)
    context->uc_mcontext.gregs[32] = pc;
#endif
}

static unsigned long spOf(ucontext_t *context) {
#if defined(__x86_64__)
    return context->uc_mcontext.gregs[REG_RSP];
#elif defined(__i386__)
    return context->uc_mcontext.gregs[REG_ESP];
#elif defined(__aarch64__)
    return context->uc_mcontext.sp;
#elif defined(__arm__)
    return context->uc_mcontext.arm_sp;
#elif defined(__riscv)
    return context->uc_mcontext.__gregs[2];
#elif defined(__mips__)
    return context->uc_mcontext.gregs[29];
#elif defined(__powerpc64__)
    return context->uc_mcontext.gp_regs[1];
#elif defined(__powerpc__)
    return context->uc_mcontext.gregs[1];
#endif
}

static volatile int contextPcOk, contextSpOk;
static volatile unsigned long stackHere;
static void recovered(void) { siglongjmp(back, 2); }
#if defined(__powerpc64__) && (!defined(_CALL_ELF) || _CALL_ELF == 1)
/* A function is a descriptor of its address, and it is the address that a context has. */
#define CODE_OF(f) (*(unsigned long *)(void *)(f))
#else
#define CODE_OF(f) ((unsigned long)(f))
#endif
static void redirecting(int sig, siginfo_t *info, void *opaque) {
    ucontext_t *context = opaque;
    (void)sig;
    (void)info;
    unsigned long pc = pcOf(context);
    contextPcOk = pc != 0 && pc != CODE_OF(recovered);
    contextSpOk = spOf(context) <= stackHere + 4096 && spOf(context) + 65536 > stackHere;
    setPc(context, CODE_OF(recovered));
#if defined(__mips__)
    /* A function of MIPS finds its data from the address that it was called at. */
    context->uc_mcontext.gregs[25] = (unsigned long)recovered;
#elif defined(__powerpc64__) && defined(_CALL_ELF) && _CALL_ELF == 2
    context->uc_mcontext.gp_regs[12] = (unsigned long)recovered;
#elif defined(__powerpc64__)
    context->uc_mcontext.gp_regs[2] = ((unsigned long *)(void *)recovered)[1];
#endif
    count++;
}

static volatile int altInside, altFlag;
static char altStack[64 * 1024];
static void onAlternate(int sig) {
    char here;
    stack_t now;
    (void)sig;
    altInside = &here >= altStack && &here < altStack + sizeof altStack;
    sigaltstack(0, &now);
    altFlag = (now.ss_flags & SS_ONSTACK) != 0;
    count++;
}

static volatile int childCode, childStatus, childPidOk;
static volatile pid_t expectedChild;
static void childChanged(int sig, siginfo_t *info, void *context) {
    (void)sig;
    (void)context;
    childCode = info->si_code;
    childStatus = info->si_status;
    childPidOk = expectedChild == 0 || info->si_pid == expectedChild;
    count++;
}

/* Threads. */

static volatile int ready, leave, workerMaskHas;
static void *spinning(void *unused) {
    (void)unused;
    threadTid = gettid_();
    sigset_t now;
    sigprocmask(SIG_BLOCK, 0, &now);
    workerMaskHas = sigismember(&now, SIGUSR2);
    ready = 1;
    while (!leave) sched_yield();
    return 0;
}

static sem_t semaphore;
static volatile int waitResult, waitErrno, waited;
static void *waiting(void *unused) {
    (void)unused;
    ready = 1;
    waitResult = sem_wait(&semaphore);
    waitErrno = errno;
    waited = 1;
    return 0;
}

static void *cancelledWhileWaiting(void *unused) {
    (void)unused;
    ready = 1;
    sem_wait(&semaphore);
    return (void *)7;
}

static void *cancelledWhileSpinning(void *unused) {
    (void)unused;
    pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, 0);
    ready = 1;
    for (;;) count = count;
    return (void *)7;
}

static void yields(int times) {
    for (int i = 0; i < times; i++) sched_yield();
}

int main(void) {
    sigset_t old, set, pending;
    struct sigaction action, previous;

    reset();
    use(SIGUSR1, plain, 0);
    raise(SIGUSR1);
    line("a handler runs", count);
    line("it is given its signal", last == SIGUSR1);

    reset();
    kill(getpid(), SIGUSR1);
    line("kill reaches this process", count);

    reset();
    useInfo(SIGUSR1, informed, 0);
    raise(SIGUSR1);
    line("info has the signal", infoSigno);
    line("info says tkill", infoCode == SI_TKILL);
    line("info has the pid", infoPidOk);
    line("a handler has a context", infoContext);
    line("a signal is blocked in its handler", infoSelfBlocked);
    reset();
    sigset_t afterHandler;
    sigprocmask(SIG_BLOCK, 0, &afterHandler);
    line("it isn't after", sigismember(&afterHandler, SIGUSR1));
    kill(getpid(), SIGUSR1);
    line("kill says the user", infoCode == SI_USER);

    reset();
    use(SIGUSR1, plain, 0);
    blockOnly(SIGUSR1, &old);
    raise(SIGUSR1);
    raise(SIGUSR1);
    line("a blocked signal waits", count);
    sigpending(&pending);
    line("and is pending", sigismember(&pending, SIGUSR1));
    sigprocmask(SIG_SETMASK, &old, 0);
    line("unblocked it runs at once and once", count);
    sigpending(&pending);
    line("and isn't pending", sigismember(&pending, SIGUSR1));

    /* Those of real time are all kept, and the lowest comes first. */
    reset();
    useInfo(SIGRTMIN + 1, informed, 0);
    blockOnly(SIGRTMIN + 1, &old);
    raise(SIGRTMIN + 1);
    raise(SIGRTMIN + 1);
    raise(SIGRTMIN + 1);
    line("real time waits", count);
    sigprocmask(SIG_SETMASK, &old, 0);
    line("real time is each one", count);
    reset();
    union sigval value;
    value.sival_int = 4242;
    blockOnly(SIGRTMIN + 1, &old);
    sigqueue(getpid(), SIGRTMIN + 1, value);
    sigprocmask(SIG_SETMASK, &old, 0);
    line("a value comes with it", infoValue);
    line("says queue", infoCode == SI_QUEUE);

    reset();
    use(SIGUSR2, noted, 0);
    memset(&action, 0, sizeof action);
    action.sa_handler = masking;
    sigemptyset(&action.sa_mask);
    sigaddset(&action.sa_mask, SIGUSR2);
    sigaction(SIGUSR1, &action, 0);
    raise(SIGUSR1);
    line("what a handler masks waits for it", orders == 3 && order[0] == 1 && order[1] == 1 && order[2] == 2);

    reset();
    sigaction(SIGUSR1, 0, &previous);
    line("an action reads back", previous.sa_handler == masking && sigismember(&previous.sa_mask, SIGUSR2));

    reset();
    use(SIGUSR1, recursive, SA_NODEFER);
    raise(SIGUSR1);
    line("a handler can be in itself", deepest);

    reset();
    use(SIGUSR1, plain, SA_RESETHAND);
    raise(SIGUSR1);
    sigaction(SIGUSR1, 0, &previous);
    line("reset goes back to the default", previous.sa_handler == SIG_DFL && count == 1);

    reset();
    use(SIGUSR1, SIG_IGN, 0);
    raise(SIGUSR1);
    line("what is ignored does nothing", count);

    errno = 0;
    memset(&action, 0, sizeof action);
    action.sa_handler = plain;
    line("kill can't be caught", sigaction(SIGKILL, &action, 0) == -1 && errno == EINVAL);
    line("stop can't be caught", sigaction(SIGSTOP, &action, 0) == -1 && errno == EINVAL);
    sigemptyset(&set);
    sigaddset(&set, SIGKILL);
    sigprocmask(SIG_BLOCK, &set, &old);
    sigprocmask(SIG_BLOCK, 0, &set);
    line("kill can't be blocked", sigismember(&set, SIGKILL));
    sigprocmask(SIG_SETMASK, &old, 0);

    /* Registers and memory come through. */
    reset();
    use(SIGUSR1, clobbering, 0);
    {
        volatile long a = 11;
        long b = a + 1, c = a + 2, d = a + 3, e = a + 4, f = a + 5, g = a + 6, h = a + 7;
        raise(SIGUSR1);
        line("what a function holds comes through", b + c + d + e + f + g + h == 105 && count == 1);
    }

    /* sigsuspend and waiting for a signal. */
    reset();
    use(SIGUSR1, plain, 0);
    blockOnly(SIGUSR1, &old);
    raise(SIGUSR1);
    sigemptyset(&set);
    errno = 0;
    int suspended = sigsuspend(&set);
    line("sigsuspend runs it and fails", suspended == -1 && errno == EINTR && count == 1);
    sigprocmask(SIG_BLOCK, 0, &set);
    line("sigsuspend puts the mask back", sigismember(&set, SIGUSR1));
    raise(SIGUSR1);
    sigemptyset(&set);
    sigaddset(&set, SIGUSR1);
    siginfo_t waitedInfo;
    line("sigwaitinfo takes it", sigwaitinfo(&set, &waitedInfo) == SIGUSR1 && count == 1 && waitedInfo.si_signo == SIGUSR1);
    struct timespec none = {0, 0};
    errno = 0;
    line("sigtimedwait of nothing times out", sigtimedwait(&set, 0, &none) == -1 && errno == EAGAIN);
    sigprocmask(SIG_SETMASK, &old, 0);

    /* A stack of its own. */
    reset();
    stack_t alternate, former;
    alternate.ss_sp = altStack;
    alternate.ss_size = sizeof altStack;
    alternate.ss_flags = 0;
    sigaltstack(&alternate, &former);
    line("there was no alternate stack", (former.ss_flags & SS_DISABLE) != 0);
    use(SIGUSR1, onAlternate, SA_ONSTACK);
    raise(SIGUSR1);
    line("a handler runs on it", altInside);
    line("and knows that", altFlag);
    sigaltstack(0, &former);
    line("not after", (former.ss_flags & SS_ONSTACK) != 0);
    use(SIGUSR2, onAlternate, 0);
    raise(SIGUSR2);
    line("only if asked", altInside);
    alternate.ss_flags = SS_DISABLE;
    sigaltstack(&alternate, 0);

    /* Faults. */
    reset();
    useInfo(SIGSEGV, faulted, 0);
    faultAddress = (void *)16;
    if (sigsetjmp(back, 1) == 0) *(volatile int *)faultAddress = 1;
    line("a store to nowhere faults", count);
    line("says not mapped", faultCode == SEGV_MAPERR);
    line("says where", faultAddressOk);
    sigprocmask(SIG_BLOCK, 0, &set);
    line("the mask is back", sigismember(&set, SIGSEGV));
    reset();
    char *page = mmap(0, 4096, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    faultAddress = page + 8;
    if (sigsetjmp(back, 1) == 0) *(volatile char *)faultAddress = 1;
    line("a store to what can't be written faults", count);
    line("says denied", faultCode == SEGV_ACCERR);
    reset();
    faultAddress = (void *)24;
    if (sigsetjmp(back, 1) == 0) (void)*(volatile int *)faultAddress;
    if (sigsetjmp(back, 1) == 0) (void)*(volatile int *)faultAddress;
    line("a load faults, and again", count);

    /* What a handler changes in its context is where it goes. */
    reset();
    char anchor;
    stackHere = (unsigned long)&anchor;
    useInfo(SIGSEGV, redirecting, 0);
    if (sigsetjmp(back, 1) == 0) *(volatile int *)32 = 1;
    else line("a context can be sent elsewhere", count);
    line("it says where it was", contextPcOk);
    line("and its stack", contextSpOk);

    /* A signal for a thread goes to that thread. */
    reset();
    use(SIGUSR1, whoAmI, 0);
    sigemptyset(&set);
    sigaddset(&set, SIGUSR2);
    sigprocmask(SIG_BLOCK, &set, &old);
    ready = leave = 0;
    pthread_t thread;
    pthread_create(&thread, 0, spinning, 0);
    while (!ready) sched_yield();
    sigprocmask(SIG_SETMASK, &old, 0);
    line("a thread has the mask of what made it", workerMaskHas);
    pthread_kill(thread, SIGUSR1);
    while (!count) sched_yield();
    line("pthread_kill goes to the thread", threadSawTid == threadTid);
    leave = 1;
    pthread_join(thread, 0);

    /* One for a process goes to a thread that doesn't block it. */
    reset();
    ready = leave = 0;
    pthread_create(&thread, 0, spinning, 0);
    while (!ready) sched_yield();
    blockOnly(SIGUSR1, &old);
    kill(getpid(), SIGUSR1);
    while (!count) sched_yield();
    line("kill goes to a thread that takes it", threadSawTid == threadTid);
    sigprocmask(SIG_SETMASK, &old, 0);
    leave = 1;
    pthread_join(thread, 0);

    /* A thread that waits is interrupted, and goes on. */
    reset();
    use(SIGUSR1, plain, 0);
    sem_init(&semaphore, 0, 0);
    ready = waited = 0;
    pthread_create(&thread, 0, waiting, 0);
    while (!ready) sched_yield();
    while (!waited) {
        pthread_kill(thread, SIGUSR1);
        yields(50);
    }
    pthread_join(thread, 0);
    line("a wait is interrupted", waitResult == -1 && waitErrno == EINTR && count >= 1);

    /* Cancelling goes by a signal, and by the context of its handler. */
    ready = 0;
    pthread_create(&thread, 0, cancelledWhileWaiting, 0);
    while (!ready) sched_yield();
    yields(50);
    pthread_cancel(thread);
    void *result = 0;
    pthread_join(thread, &result);
    line("a wait is cancelled", result == PTHREAD_CANCELED);
    ready = 0;
    pthread_create(&thread, 0, cancelledWhileSpinning, 0);
    while (!ready) sched_yield();
    pthread_cancel(thread);
    pthread_join(thread, &result);
    line("a loop is cancelled", result == PTHREAD_CANCELED);

    /* A wait for a child is interrupted by a signal, or goes on if the signal says so. */
    {
        int waitStatus = 0;
        reset();
        use(SIGUSR1, plain, 0);
        pid_t waitedFor = fork();
        if (waitedFor == 0) {
            kill(getppid(), SIGUSR1);
            yields(200);
            _exit(5);
        }
        errno = 0;
        pid_t got;
        while ((got = waitpid(waitedFor, &waitStatus, 0)) == -1 && errno == EINTR) other = 1;
        line("a wait comes to the child", got == waitedFor && WEXITSTATUS(waitStatus) == 5);
        line("the signal ran", count);
        reset();
        use(SIGUSR1, plain, SA_RESTART);
        waitedFor = fork();
        if (waitedFor == 0) {
            kill(getppid(), SIGUSR1);
            yields(200);
            _exit(6);
        }
        errno = 0;
        got = waitpid(waitedFor, &waitStatus, 0);
        line("a wait goes on if it may", got == waitedFor && WEXITSTATUS(waitStatus) == 6 && count == 1);
        siginfo_t childInfo;
        waitedFor = fork();
        if (waitedFor == 0) _exit(9);
        memset(&childInfo, 0, sizeof childInfo);
        line("waitid has it", waitid(P_PID, waitedFor, &childInfo, WEXITED) == 0 && childInfo.si_code == CLD_EXITED && childInfo.si_status == 9 && childInfo.si_pid == waitedFor);
        waitedFor = fork();
        if (waitedFor == 0) {
            use(SIGTERM, SIG_DFL, 0);
            raise(SIGTERM);
            _exit(1);
        }
        memset(&childInfo, 0, sizeof childInfo);
        line("waitid says killed", waitid(P_ALL, 0, &childInfo, WEXITED) == 0 && childInfo.si_code == CLD_KILLED && childInfo.si_status == SIGTERM);
        errno = 0;
        line("waitid of nothing", waitid(P_ALL, 0, &childInfo, WEXITED) == -1 && errno == ECHILD);
    }

    /* Children. */
    int status = 0;
    pid_t child = fork();
    if (child == 0) {
        sigprocmask(SIG_BLOCK, 0, &set);
        reset();
        use(SIGUSR2, plain, 0);
        raise(SIGUSR2);
        _exit(count);
    }
    waitpid(child, &status, 0);
    line("a child has handlers", WEXITSTATUS(status));

    reset();
    use(SIGUSR1, plain, 0);
    blockOnly(SIGUSR1, &old);
    raise(SIGUSR1);
    child = fork();
    if (child == 0) {
        sigset_t inChild;
        sigprocmask(SIG_BLOCK, 0, &inChild);
        sigpending(&pending);
        _exit(sigismember(&inChild, SIGUSR1) * 2 + sigismember(&pending, SIGUSR1));
    }
    waitpid(child, &status, 0);
    line("a child has the mask and nothing pending", WEXITSTATUS(status));
    sigprocmask(SIG_SETMASK, &old, 0);

    reset();
    useInfo(SIGCHLD, childChanged, SA_RESTART);
    child = fork();
    if (child == 0) _exit(7);
    expectedChild = child;
    waitpid(child, &status, 0);
    while (!count) sched_yield();
    line("sigchld comes", count);
    line("says it exited", childCode == CLD_EXITED);
    line("with its status", childStatus);
    line("and who", childPidOk);
    line("and waiting got it", WEXITSTATUS(status));
    use(SIGCHLD, SIG_DFL, 0);

    reset();
    child = fork();
    if (child == 0) {
        use(SIGTERM, SIG_DFL, 0);
        raise(SIGTERM);
        _exit(1);
    }
    waitpid(child, &status, 0);
    line("a default ends the child", WIFSIGNALED(status) && WTERMSIG(status) == SIGTERM);
    child = fork();
    if (child == 0) {
        for (;;) sched_yield();
    }
    kill(child, SIGKILL);
    waitpid(child, &status, 0);
    line("kill ends the child", WIFSIGNALED(status) && WTERMSIG(status) == SIGKILL);
    child = fork();
    if (child == 0) {
        use(SIGSEGV, SIG_DFL, 0);
        *(volatile int *)8 = 1;
        _exit(1);
    }
    waitpid(child, &status, 0);
    line("a fault ends the child", WIFSIGNALED(status) && WTERMSIG(status) == SIGSEGV);
    child = fork();
    if (child == 0) abort();
    waitpid(child, &status, 0);
    line("abort ends the child", WIFSIGNALED(status) && WTERMSIG(status) == SIGABRT);
    child = fork();
    if (child == 0) {
        raise(SIGCHLD);
        raise(SIGWINCH);
        raise(SIGURG);
        _exit(3);
    }
    waitpid(child, &status, 0);
    line("some defaults do nothing", WIFEXITED(status) ? WEXITSTATUS(status) : -1);
    child = fork();
    if (child == 0) {
        sigset_t all;
        sigfillset(&all);
        sigprocmask(SIG_BLOCK, &all, 0);
        kill(getpid(), SIGTERM);
        sigset_t none_;
        sigemptyset(&none_);
        sigprocmask(SIG_SETMASK, &none_, 0);
        _exit(1);
    }
    waitpid(child, &status, 0);
    line("a default waits for its mask", WIFSIGNALED(status) && WTERMSIG(status) == SIGTERM);

    /* And what is in another thread's future: the last goes through a thread. */
    say("done\n");
    return 0;
}
