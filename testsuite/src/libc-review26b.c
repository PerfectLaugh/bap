// What Linux does that a review of the processes of the machine found it didn't:
//   hangup: a process that ends sends SIGHUP and SIGCONT only to a process group that its end orphans, and not to one that was
//     orphaned before, as that of the first process is, of which something is stopped.
//   robust: a thread or a process that ends holding a robust mutex leaves it to the next to lock it, which is told that its owner
//     died, by the robust list that `set_robust_list` gave, which `get_robust_list` gives back.
//   memory: what is mapped to be written and not read can be read, and `/proc/self/maps` says what was asked for; a mapping of
//     MAP_GROWSDOWN grows down to a fault below it; `mprotect` of a range with a hole changes what is mapped before the hole and is
//     ENOMEM, and of bits that there aren't, EINVAL; MAP_SHARED with MAP_PRIVATE of no file, and MAP_GROWSDOWN of what is shared,
//     are EINVAL; a file offset past what a file can have is EOVERFLOW; `brk` stays within RLIMIT_DATA; and what is reserved of
//     addresses and not of memory is given whatever its size, and committed a piece at a time.
//   context: `rt_sigreturn` goes back to the state of floating point that the context points to, as a handler left it, and with a
//     code segment that isn't the program's it is SIGSEGV; a fault at an address that isn't canonical is SI_KERNEL of no address.
//   signals: `rt_sigqueueinfo` delivers the pid that it was given; what is queued of real time is within RLIMIT_SIGPENDING; an
//     ignored signal has no flags after `execve`; `epoll_wait` is EINTR after a stop and SIGCONT.
//   tasks: `prctl` has PR_SET_PDEATHSIG, PR_GET_DUMPABLE and PR_SET_CHILD_SUBREAPER, and is EINVAL of what it doesn't know;
//     strict seccomp after a filter is EINVAL; `clone` of CLONE_SIGHAND without CLONE_VM is EINVAL, and of CLONE_FILES shares the
//     descriptors; a process has the status of its last thread to end; `sched_getaffinity` of a mask too small, `clock_settime`
//     of a clock that can't be set and `timerfd_settime` of flags that there aren't are EINVAL; FUTEX_WAKE_OP and the locks of
//     priority inheritance are there.
//   tracing: PTRACE_LISTEN leaves a tracee in a group stop to stop anew for SIGCONT, as PTRACE_EVENT_STOP, which it does without
//     it too once it is let go on; options that there aren't are EINVAL, or EIO of PTRACE_SEIZE; PTRACE_GETSIGMASK gives the
//     mask; a request of what isn't a tracee is ESRCH; and registers with no code segment are EIO.
//   loading: `execve` of a file whose segment ends past the address space ends the process with SIGSEGV.
// With the argument `zombies` it makes 40 children that end and that it doesn't wait for, says `made` and waits, for a test to look
// at what the machine keeps of them.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/filter.h>
#include <linux/futex.h>
#include <linux/seccomp.h>
#include <poll.h>
#include <pthread.h>
#include <sched.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/mman.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/timerfd.h>
#include <sys/uio.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
  errno = 0;
}

static const char *ended(int status) {
  static char text[64];
  if (WIFEXITED(status)) snprintf(text, sizeof text, "exited %d", WEXITSTATUS(status));
  else if (WIFSIGNALED(status)) snprintf(text, sizeof text, "signal %d", WTERMSIG(status));
  else if (WIFSTOPPED(status)) snprintf(text, sizeof text, "stopped %d event %d", WSTOPSIG(status), status >> 16);
  else snprintf(text, sizeof text, "status %x", status);
  return text;
}

static volatile int count;
static void counted(int signal) { count++; }

/* What a child does is run in a child, and how it ended is said. */
#define IN_CHILD(name, ...) do { \
    fflush(stdout); \
    pid_t child_ = fork(); \
    if (!child_) { __VA_ARGS__; fflush(stdout); _exit(0); } \
    int status_; \
    waitpid(child_, &status_, 0); \
    printf("%s: %s\n", name, ended(status_)); \
  } while (0)

static void hangup(void) {
  int status;
  pid_t stopped = fork();
  if (!stopped) { raise(SIGSTOP); _exit(3); }
  waitpid(stopped, &status, WUNTRACED);
  pid_t other = fork();
  if (!other) _exit(0);
  waitpid(other, &status, 0);
  kill(stopped, SIGCONT);
  waitpid(stopped, &status, 0);
  printf("hangup: what was stopped while another ended: %s\n", ended(status));
}

static pthread_mutex_t mutex;
static void *locker(void *unused) { pthread_mutex_lock(&mutex); return 0; }

static void robust(void) {
  pthread_mutexattr_t attributes;
  pthread_mutexattr_init(&attributes);
  pthread_mutexattr_setrobust(&attributes, PTHREAD_MUTEX_ROBUST);
  pthread_mutex_init(&mutex, &attributes);
  pthread_t thread;
  pthread_create(&thread, 0, locker, 0);
  pthread_join(thread, 0);
  printf("robust: a lock whose thread ended is EOWNERDEAD: %d\n", pthread_mutex_lock(&mutex) == EOWNERDEAD);
  pthread_mutex_consistent(&mutex);
  pthread_mutex_unlock(&mutex);
  pthread_mutex_t *shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  pthread_mutexattr_setpshared(&attributes, PTHREAD_PROCESS_SHARED);
  pthread_mutex_init(shared, &attributes);
  pid_t child = fork();
  if (!child) { pthread_mutex_lock(shared); usleep(50000); _exit(0); }
  usleep(10000);
  printf("robust: a lock whose process ended is EOWNERDEAD: %d\n", pthread_mutex_lock(shared) == EOWNERDEAD);
  wait(0);
  void *head = 0;
  size_t size = 0;
  said("robust: get_robust_list", syscall(SYS_get_robust_list, 0, &head, &size));
  printf("robust: a list of a head of %zu bytes, which there is: %d\n", size, head != 0);
  said("robust: set_robust_list of another size", syscall(SYS_set_robust_list, head, size + 1));
  said("robust: get_robust_list of no thread", syscall(SYS_get_robust_list, 999999, &head, &size));
  /* a lock of priority inheritance, which the kernel hands on */
  pthread_mutexattr_t inherit;
  pthread_mutexattr_init(&inherit);
  pthread_mutexattr_setprotocol(&inherit, PTHREAD_PRIO_INHERIT);
  static pthread_mutex_t handed;
  pthread_mutex_init(&handed, &inherit);
  static volatile int held;
  pthread_mutex_lock(&handed);
  child = 0;
  pthread_t waiter;
  extern void *take(void *);
  pthread_create(&waiter, 0, take, &handed);
  usleep(20000);
  held = 1;
  pthread_mutex_unlock(&handed);
  void *got;
  pthread_join(waiter, &got);
  printf("robust: a lock of priority inheritance that was waited for: %ld\n", (long)got);
}

void *take(void *lock) {
  long result = pthread_mutex_lock(lock);
  pthread_mutex_unlock(lock);
  return (void *)result;
}

static sigjmp_buf back;
static volatile int fault_code;
static void *volatile fault_address;
static void faulted(int signal, siginfo_t *info, void *context) {
  fault_code = info->si_code;
  fault_address = info->si_addr;
  siglongjmp(back, 1);
}

/* Whether a byte can be read or written, by doing it. */
static int reads(volatile char *address) {
  if (sigsetjmp(back, 1)) return 0;
  (void)*address;
  return 1;
}

static int writes(volatile char *address) {
  if (sigsetjmp(back, 1)) return 0;
  *address = 1;
  return 1;
}

static void permissions(void *address) {
  FILE *maps = fopen("/proc/self/maps", "r");
  char line[512];
  while (maps && fgets(line, sizeof line, maps)) {
    unsigned long first, last;
    char mode[8];
    if (sscanf(line, "%lx-%lx %7s", &first, &last, mode) == 3 && first <= (unsigned long)address && (unsigned long)address < last)
      printf("memory: what maps says of it: %s\n", mode);
  }
  if (maps) fclose(maps);
}

static void memory(void) {
  struct sigaction action = {0};
  action.sa_sigaction = faulted;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &action, 0);
  long page = 4096;
  char *only = mmap(0, page, PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  printf("memory: what is mapped to be written is read: %d\n", reads(only));
  permissions(only);
  char *area = mmap(0, 4 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  said("memory: mprotect to be written alone", mprotect(area, page, PROT_WRITE));
  printf("memory: and it is read: %d\n", reads(area));
  permissions(area);
  munmap(area + 2 * page, page);
  said("memory: mprotect over a hole", mprotect(area, 4 * page, PROT_READ));
  printf("memory: what was before the hole is written: %d, and after it: %d\n", writes(area + page), writes(area + 3 * page));
  said("memory: mprotect of bits that there aren't", mprotect(area, page, 0x800));
  said("memory: mprotect to grow both ways", mprotect(area, page, PROT_READ | PROT_GROWSDOWN | PROT_GROWSUP));
  said("memory: mprotect of nothing", mprotect(area, 0, PROT_READ));
  said("memory: shared and private of no file", mmap(0, page, PROT_READ, MAP_SHARED | MAP_PRIVATE | MAP_ANONYMOUS, -1, 0) == MAP_FAILED ? -1 : 0);
  said("memory: shared that grows down", mmap(0, page, PROT_READ, MAP_SHARED | MAP_ANONYMOUS | MAP_GROWSDOWN, -1, 0) == MAP_FAILED ? -1 : 0);
  int file = open("review26b.tmp", O_RDWR | O_CREAT | O_TRUNC, 0600);
  ftruncate(file, page);
  said("memory: a file at an offset past any", mmap(0, page, PROT_READ, MAP_SHARED, file, 0x7ffffffffffff000L) == MAP_FAILED ? -1 : 0);
  said("memory: a file that grows down", mmap(0, page, PROT_READ, MAP_PRIVATE | MAP_GROWSDOWN, file, 0) == MAP_FAILED ? -1 : 0);
  close(file);
  unlink("review26b.tmp");
  /* far from anything else, as a stack that grows needs room below it */
  char *stack = mmap((void *)0x70000000, page, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_GROWSDOWN | MAP_FIXED, -1, 0);
  printf("memory: a mapping that grows down is written a word below it: %d, and 40 pages below: %d\n", writes(stack - 8),
    writes(stack - 40 * page));
  printf("memory: and what was written is there: %d\n", stack[-8] + stack[-40 * page]);
  said("memory: mprotect of all that grew", mprotect(stack, page, PROT_READ | PROT_GROWSDOWN));
  printf("memory: which isn't written then: %d\n", writes(stack - 40 * page));
  IN_CHILD("memory: brk within RLIMIT_DATA", {
    long start = syscall(SYS_brk, 0);
    struct rlimit limit = {1 << 20, 1 << 20};
    setrlimit(RLIMIT_DATA, &limit);
    printf("memory: brk past RLIMIT_DATA stays: %d, and within it moves: %d\n", syscall(SYS_brk, start + (2 << 20)) == start,
      syscall(SYS_brk, start + 65536) == start + 65536);
  });
  /* addresses that are reserved and not memory, of any size, and committed a piece at a time: up to 2^44 bytes, as the host of the
     machine has its own address space to give them from, which other machines may be given of too */
  int reserved = 0;
  for (int bits = 36; bits <= 44; bits++) {
    void *much = mmap(0, 1UL << bits, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
    if (much != MAP_FAILED) { reserved++; munmap(much, 1UL << bits); }
  }
  printf("memory: reservations of 2^36 to 2^44 bytes that were made: %d\n", reserved);
  char *arena = mmap(0, 1UL << 40, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
  long sum = 0;
  for (long piece = 0; piece < 300; piece++) {
    char *at = arena + (piece << 30);
    if (mprotect(at, 65536, PROT_READ | PROT_WRITE)) break;
    at[piece] = piece & 0x7f;
    sum += at[piece] + at[65535];
  }
  printf("memory: what was committed of 2^40 bytes, a piece of each 2^30: %ld\n", sum);
  for (long piece = 0; piece < 300; piece++) munmap(arena + (piece << 30), 65536);
  said("memory: and unmapped", munmap(arena, 1UL << 40));
#ifdef __x86_64__
  fault_code = 0;
  printf("memory: an address that isn't canonical is read: %d", reads((char *)0x0000900000000000UL));
  printf(", of the code %d and at %p\n", fault_code, fault_address);
#endif
  signal(SIGSEGV, SIG_DFL);
}

#ifdef __x86_64__
static void changing(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  if (user->uc_mcontext.fpregs) {
    user->uc_mcontext.fpregs->_xmm[5].element[0] = 0xdeadbeef;
    user->uc_mcontext.fpregs->mxcsr |= 0x8000;
  }
}

static void segments(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  user->uc_mcontext.gregs[REG_CSGSFS] = 0;
}

static void context(void) {
  struct sigaction action = {0};
  action.sa_sigaction = changing;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGUSR1, &action, 0);
  unsigned low, control;
  __asm__ volatile("pxor %%xmm5, %%xmm5\n mov $62, %%eax\n syscall\n movd %%xmm5, %0\n stmxcsr %1"
    : "=&r"(low), "=m"(control) : "D"(getpid()), "S"(SIGUSR1) : "rax", "rcx", "r11", "xmm5", "memory");
  printf("context: what a handler left of xmm5 in its context: %x, and of mxcsr: %x\n", low, control & 0x8000);
  __asm__ volatile("ldmxcsr %0" : : "m"((unsigned){0x1f80}));
  IN_CHILD("context: a return to no code segment", {
    action.sa_sigaction = segments;
    sigaction(SIGUSR1, &action, 0);
    raise(SIGUSR1);
    printf("context: went on\n");
  });
}
#endif

static void queued(int signal, siginfo_t *info, void *context) {
  printf("signals: what was queued is of pid %d, with %d\n", info->si_pid, info->si_value.sival_int);
}

static int closing(void *descriptor) { close(*(int *)descriptor); return 0; }
static void *leaves(void *code) { usleep(20000); syscall(SYS_exit, 7); return 0; }

static void signals(char *program) {
  struct sigaction action = {0};
  action.sa_sigaction = queued;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGUSR2, &action, 0);
  siginfo_t info = {0};
  info.si_signo = SIGUSR2;
  info.si_code = SI_QUEUE;
  info.si_pid = 4242;
  info.si_value.sival_int = 9;
  said("signals: rt_sigqueueinfo", syscall(SYS_rt_sigqueueinfo, getpid(), SIGUSR2, &info));
  IN_CHILD("signals: within RLIMIT_SIGPENDING", {
    sigset_t blocked;
    sigemptyset(&blocked);
    sigaddset(&blocked, SIGRTMIN);
    sigprocmask(SIG_BLOCK, &blocked, 0);
    struct rlimit limit;
    getrlimit(RLIMIT_SIGPENDING, &limit);
    printf("signals: RLIMIT_SIGPENDING is finite: %d\n", limit.rlim_cur != RLIM_INFINITY);
    limit.rlim_cur = 20;
    setrlimit(RLIMIT_SIGPENDING, &limit);
    int made = 0;
    while (made < 1000 && !sigqueue(getpid(), SIGRTMIN, (union sigval){0})) made++;
    printf("signals: no more than 20 are queued: %d, and then: %s\n", made <= 20, strerror(errno));
    /* one that isn't of real time is sent all the same */
    printf("signals: and kill then: %d\n", kill(getpid(), 0));
  });
  /* an ignored signal across execve */
  IN_CHILD("signals: across execve", {
    struct sigaction ignored = {0};
    ignored.sa_handler = SIG_IGN;
    ignored.sa_flags = SA_RESTART | SA_NOCLDSTOP;
    sigaddset(&ignored.sa_mask, SIGUSR2);
    sigaction(SIGUSR1, &ignored, 0);
    execl(program, program, "flags", (char *)0);
    printf("signals: no execve: %s\n", strerror(errno));
  });
  /* epoll_wait across a stop */
  fflush(stdout);
  int pipes[2];
  pipe(pipes);
  pid_t waits = fork();
  if (!waits) {
    int epoll = epoll_create1(0);
    struct epoll_event event = {.events = EPOLLIN};
    epoll_ctl(epoll, EPOLL_CTL_ADD, pipes[0], &event);
    int result = epoll_wait(epoll, &event, 1, 2000);
    printf("signals: epoll_wait across a stop and SIGCONT: %d %s\n", result, result < 0 ? strerror(errno) : "");
    fflush(stdout);
    _exit(0);
  }
  usleep(20000);
  int status;
  kill(waits, SIGSTOP);
  waitpid(waits, &status, WUNTRACED);
  kill(waits, SIGCONT);
  waitpid(waits, &status, 0);
}

static void *waiter(void *word) {
  syscall(SYS_futex, word, FUTEX_WAIT, 0, 0, 0, 0);
  return 0;
}

static void tasks(void) {
  said("tasks: PR_GET_DUMPABLE", prctl(PR_GET_DUMPABLE));
  said("tasks: PR_SET_DUMPABLE of 2", prctl(PR_SET_DUMPABLE, 2));
  IN_CHILD("tasks: dumpable", {
    said("tasks: PR_SET_DUMPABLE of 0", prctl(PR_SET_DUMPABLE, 0));
    said("tasks: PR_GET_DUMPABLE then", prctl(PR_GET_DUMPABLE));
    fflush(stdout);
    if (!fork()) { said("tasks: and of a child", prctl(PR_GET_DUMPABLE)); fflush(stdout); _exit(0); }
    wait(0);
  });
  said("tasks: prctl of what there isn't", prctl(9999, 0, 0, 0, 0));
  said("tasks: PR_SET_PDEATHSIG of no signal", prctl(PR_SET_PDEATHSIG, 100));
  int signal_ = -1;
  said("tasks: PR_SET_PDEATHSIG", prctl(PR_SET_PDEATHSIG, SIGUSR1));
  said("tasks: PR_GET_PDEATHSIG", prctl(PR_GET_PDEATHSIG, &signal_));
  printf("tasks: which is %d\n", signal_ == SIGUSR1);
  prctl(PR_SET_PDEATHSIG, 0);
  /* a grandchild hears of its parent's end, and is then a child of what takes such in */
  int pipes[2];
  pipe(pipes);
  int flag = -1;
  said("tasks: PR_SET_CHILD_SUBREAPER", prctl(PR_SET_CHILD_SUBREAPER, 1));
  said("tasks: PR_GET_CHILD_SUBREAPER", prctl(PR_GET_CHILD_SUBREAPER, &flag));
  printf("tasks: which is %d\n", flag);
  fflush(stdout);
  pid_t me = getpid();
  pid_t child = fork();
  if (!child) {
    if (!fork()) {
      sigset_t blocked, none;
      sigemptyset(&none);
      sigemptyset(&blocked);
      sigaddset(&blocked, SIGUSR1);
      sigprocmask(SIG_BLOCK, &blocked, 0);
      signal(SIGUSR1, counted);
      prctl(PR_SET_PDEATHSIG, SIGUSR1);
      write(pipes[1], "r", 1);
      while (!count) sigsuspend(&none);
      char parent = getppid() == me ? 'y' : 'n';
      write(pipes[1], &parent, 1);
      _exit(5);
    }
    char ready;
    read(pipes[0], &ready, 1);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  char parent = '?';
  read(pipes[0], &parent, 1);
  printf("tasks: a grandchild heard of its parent's end, and its parent is then this: %c\n", parent);
  pid_t adopted = wait(&status);
  printf("tasks: and it is waited for here: %d, %s\n", adopted > 0, ended(status));
  prctl(PR_SET_CHILD_SUBREAPER, 0);
  /* seccomp */
  IN_CHILD("tasks: strict after a filter", {
    struct sock_filter allow[] = {BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)};
    struct sock_fprog program = {1, allow};
    prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
    said("tasks: a filter", prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &program));
    said("tasks: strict mode after it", prctl(PR_SET_SECCOMP, SECCOMP_MODE_STRICT));
  });
  /* clone */
  static char stack[65536];
  said("tasks: clone of CLONE_SIGHAND without CLONE_VM", clone(closing, stack + sizeof stack, CLONE_SIGHAND | SIGCHLD, &pipes[0]));
  said("tasks: clone of CLONE_THREAD without CLONE_SIGHAND", clone(closing, stack + sizeof stack, CLONE_THREAD | CLONE_VM, &pipes[0]));
  said("tasks: clone of CLONE_NEWNS with CLONE_FS", clone(closing, stack + sizeof stack, CLONE_NEWNS | CLONE_FS | SIGCHLD, &pipes[0]));
  child = clone(closing, stack + sizeof stack, CLONE_FILES | SIGCHLD, &pipes[0]);
  waitpid(child, &status, 0);
  said("tasks: a descriptor that a child of CLONE_FILES closed", fcntl(pipes[0], F_GETFD));
  said("tasks: and one that it didn't", fcntl(pipes[1], F_GETFD));
  close(pipes[1]);
  /* the status of the last thread */
  IN_CHILD("tasks: a process whose first thread ended with 1 and whose last with 7", {
    pthread_t thread;
    pthread_create(&thread, 0, leaves, 0);
    syscall(SYS_exit, 1);
  });
  /* calls */
  unsigned long mask[16];
  said("tasks: sched_getaffinity of a byte", syscall(SYS_sched_getaffinity, 0, 1, mask));
  said("tasks: sched_getaffinity of no room", syscall(SYS_sched_getaffinity, 0, 0, mask));
  printf("tasks: sched_getaffinity of words gives some: %d\n", syscall(SYS_sched_getaffinity, 0, sizeof mask, mask) > 0);
  struct timespec time = {1, 0};
  said("tasks: clock_settime of CLOCK_MONOTONIC", clock_settime(CLOCK_MONOTONIC, &time));
  said("tasks: clock_settime of no clock", clock_settime(99, &time));
  int timer = timerfd_create(CLOCK_MONOTONIC, 0);
  struct itimerspec spec = {{0, 0}, {1, 0}};
  said("tasks: timerfd_settime of flags that there aren't", timerfd_settime(timer, 4, &spec, 0));
  said("tasks: timerfd_settime", timerfd_settime(timer, 0, &spec, 0));
  close(timer);
  /* FUTEX_WAKE_OP: the second word is set to 5, and as it was 0, those that wait on it are woken too */
  static uint32_t first, second;
  pthread_t thread;
  pthread_create(&thread, 0, waiter, &second);
  usleep(20000);
  long woken = syscall(SYS_futex, &first, FUTEX_WAKE_OP, 1, 1, &second, FUTEX_OP(FUTEX_OP_SET, 5, FUTEX_OP_CMP_EQ, 0));
  pthread_join(thread, 0);
  printf("tasks: FUTEX_WAKE_OP woke %ld, and left %u\n", woken, second);
  woken = syscall(SYS_futex, &first, FUTEX_WAKE_OP, 1, 1, &second, FUTEX_OP(FUTEX_OP_ADD, 3, FUTEX_OP_CMP_GT, 9));
  printf("tasks: FUTEX_WAKE_OP of none woke %ld, and left %u\n", woken, second);
}

#ifdef __x86_64__
static void show(const char *what, pid_t child) {
  int status;
  waitpid(child, &status, __WALL);
  printf("tracing: %s: %s\n", what, ended(status));
}

static void tracing(void) {
  said("tracing: a request of what isn't a tracee", ptrace(9999, getpid(), 0, 0));
  fflush(stdout);
  pid_t child = fork();
  if (!child) { for (;;) usleep(1000); }
  /* once it runs, as a child is made with every signal blocked */
  usleep(20000);
  said("tracing: PTRACE_SEIZE with options that there aren't", ptrace(PTRACE_SEIZE, child, 0, 0x80000000));
  said("tracing: PTRACE_SEIZE", ptrace(PTRACE_SEIZE, child, 0, 0));
  said("tracing: PTRACE_INTERRUPT", ptrace(PTRACE_INTERRUPT, child, 0, 0));
  show("interrupted", child);
  said("tracing: PTRACE_SETOPTIONS of what there isn't", ptrace(PTRACE_SETOPTIONS, child, 0, 0x80000000));
  said("tracing: PTRACE_LISTEN at the stop of PTRACE_INTERRUPT", ptrace(PTRACE_LISTEN, child, 0, 0));
  unsigned long mask = 99;
  said("tracing: PTRACE_GETSIGMASK while it listens", ptrace(PTRACE_GETSIGMASK, child, 8, &mask));
  said("tracing: PTRACE_INTERRUPT again", ptrace(PTRACE_INTERRUPT, child, 0, 0));
  show("interrupted again", child);
  said("tracing: PTRACE_GETSIGMASK", ptrace(PTRACE_GETSIGMASK, child, 8, &mask));
  printf("tracing: a mask of %lx\n", mask);
  said("tracing: PTRACE_GETSIGMASK of another size", ptrace(PTRACE_GETSIGMASK, child, 4, &mask));
  struct user_regs_struct registers;
  ptrace(PTRACE_GETREGS, child, 0, &registers);
  unsigned long long segment = registers.cs;
  registers.cs = 0;
  said("tracing: PTRACE_SETREGS with no code segment", ptrace(PTRACE_SETREGS, child, 0, &registers));
  registers.cs = segment;
  said("tracing: PTRACE_SETREGS with its own", ptrace(PTRACE_SETREGS, child, 0, &registers));
  struct user_fpregs_struct floats;
  memset(&floats, 0, sizeof floats);
  said("tracing: PTRACE_GETFPREGS", ptrace(PTRACE_GETFPREGS, child, 0, &floats));
  printf("tracing: its control word is %x and its mxcsr %x\n", floats.cwd, floats.mxcsr);
  /* a group stop, left to listen, stops anew for SIGCONT */
  ptrace(PTRACE_CONT, child, 0, 0);
  kill(child, SIGSTOP);
  show("the signal that stops it", child);
  ptrace(PTRACE_CONT, child, 0, SIGSTOP);
  show("its group stop", child);
  said("tracing: PTRACE_LISTEN", ptrace(PTRACE_LISTEN, child, 0, 0));
  said("tracing: PTRACE_CONT of what listens", ptrace(PTRACE_CONT, child, 0, 0));
  kill(child, SIGCONT);
  show("what listens, of SIGCONT", child);
  ptrace(PTRACE_CONT, child, 0, 0);
  show("then SIGCONT itself", child);
  /* and without listening, once it is let go on */
  ptrace(PTRACE_CONT, child, 0, 0);
  kill(child, SIGSTOP);
  show("the signal that stops it", child);
  ptrace(PTRACE_CONT, child, 0, SIGSTOP);
  show("its group stop", child);
  kill(child, SIGCONT);
  ptrace(PTRACE_CONT, child, 0, 0);
  show("what was let go on, of SIGCONT", child);
  ptrace(PTRACE_CONT, child, 0, 0);
  show("then SIGCONT itself", child);
  kill(child, SIGKILL);
  show("killed", child);
}
#endif

/* The program itself with the size in memory of its last segment that is loaded made 2^47, which no address space has room for. */
static void loading(char *program) {
  int file = open(program, O_RDONLY);
  struct stat stat;
  fstat(file, &stat);
  unsigned char *bytes = malloc(stat.st_size);
  read(file, bytes, stat.st_size);
  close(file);
#if __SIZEOF_POINTER__ == 8
  unsigned long long table = *(unsigned long long *)(bytes + 32);
  unsigned entry = *(unsigned short *)(bytes + 54), entries = *(unsigned short *)(bytes + 56);
  for (unsigned index = 0; index < entries; index++)
    if (*(unsigned *)(bytes + table + index * entry) == 1) *(unsigned long long *)(bytes + table + index * entry + 40) = 1ULL << 47;
#endif
  file = open("review26b.bin", O_WRONLY | O_CREAT | O_TRUNC, 0700);
  write(file, bytes, stat.st_size);
  close(file);
  IN_CHILD("loading: a program with a segment of 2^47 bytes", {
    execl("./review26b.bin", "review26b.bin", "flags", (char *)0);
    printf("loading: no execve: %s\n", strerror(errno));
  });
  unlink("review26b.bin");
}

int main(int count_, char **arguments) {
  setvbuf(stdout, 0, _IOLBF, 0);
  if (count_ > 1 && !strcmp(arguments[1], "zombies")) {
    /* children that end and aren't waited for, which keep nothing but that they ended */
    for (int made = 0; made < 40; made++) {
      int pipes[2];
      char end;
      pipe(pipes);
      if (!fork()) _exit(0);
      close(pipes[1]);
      read(pipes[0], &end, 1);
      close(pipes[0]);
    }
    printf("made\n");
    pause();
    return 0;
  }
  if (count_ > 1) {
    /* what an ignored signal has after execve */
    struct sigaction now;
    sigaction(SIGUSR1, 0, &now);
    printf("signals: after execve it is ignored: %d, with the flags %lx and SIGUSR2 in its mask: %d\n", now.sa_handler == SIG_IGN,
      (unsigned long)now.sa_flags, sigismember(&now.sa_mask, SIGUSR2));
    return 0;
  }
  hangup();
  robust();
  memory();
#ifdef __x86_64__
  context();
#endif
  signals(arguments[0]);
  tasks();
#ifdef __x86_64__
  tracing();
#endif
  loading(arguments[0]);
  return 0;
}
