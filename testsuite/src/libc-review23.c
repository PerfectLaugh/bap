// What Linux does that a review of the kernel of the machine found it didn't:
//   child: a wait that a child ends has the handler of SIGCHLD run before the program goes on after it.
//   flags: the context of a handler has the flags as they were, of x86_64 with what the page fault was, and what the handler
//     makes of them is what they are after it.
//   sizes: a break, a mapping, a segment and a range that are more than there can be are refused, rather than made.
//   timers: a timer comes while the program runs on without a call, or with calls that don't wait, and a sleep ends while
//     another thread or process runs on.
//   bus: a page of a mapping that its file has no page for is SIGBUS, as the file is when it is mapped, cut short and made longer.
//   shared: two shared mappings of the same pages are the same memory, as soon as one is written, and code that is written
//     through one of them is what runs through the other.
#define _GNU_SOURCE
#include <errno.h>
#include <pthread.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/shm.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>

static volatile int got;

static void counted(int signal) { got = signal; }

static void child(void) {
  struct sigaction action = {0};
  action.sa_handler = counted;
  sigaction(SIGCHLD, &action, 0);
  got = 0;
  pid_t made = fork();
  if (!made) _exit(5);
  int status;
  pid_t waited = waitpid(made, &status, 0);
  int seen = got;
  printf("wait: the child %d, status %d, the handler ran %d\n", waited == made, WEXITSTATUS(status), seen == SIGCHLD);
  signal(SIGCHLD, SIG_DFL);
}

static volatile unsigned long flagsSeen, trapSeen, errorSeen, addressSeen, segmentsSeen, flagsSet;

#ifdef __x86_64__
// The arithmetic flags and the direction flag.
#define FLAGS 0xcd5
static void faulted(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  greg_t *registers = user->uc_mcontext.gregs;
  flagsSeen = registers[REG_EFL];
  trapSeen = registers[REG_TRAPNO];
  errorSeen = registers[REG_ERR];
  addressSeen = registers[REG_CR2];
  segmentsSeen = registers[REG_CSGSFS];
  registers[REG_EFL] = (registers[REG_EFL] & ~(unsigned long)FLAGS) | flagsSet;
  // The load is of three bytes.
  registers[REG_RIP] += 3;
}

// The flags of a decrement of `value`, after a carry, in the handler of a load that faults after it, and after that.
static void decrement(long value, long *at) {
  unsigned long after;
  __asm__ volatile("stc\n decq %0\n movq (%2), %%rax\n pushfq\n popq %1" : "+r"(value), "=r"(after) : "r"(at) : "cc", "rax");
  printf("flags: in the handler %lx, after it %lx\n", flagsSeen & FLAGS, after & FLAGS);
}

static void flags(void) {
  struct sigaction action = {0};
  action.sa_sigaction = faulted;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &action, 0);
  sigaction(SIGUSR1, &action, 0);
  for (int round = 0; round < 2; round++) {
    // The second time the handler leaves others than there were.
    flagsSet = round ? 0x8c4 : 0x11;
    decrement(96, 0);
    decrement(1, 0);
    decrement(0, 0);
    decrement((long)(1UL << 63), 0);
  }
  printf("flags: bit 1 and the interrupt flag %lx, the resume flag of a fault %lx, segments %lx\n", flagsSeen & 0x202,
         flagsSeen & 0x10000, segmentsSeen);
  // What the page fault was: of a load of what isn't there, a store to it, a store to what may only be read, and a call of what
  // may not be run, after each of which a signal that is no fault says the same.
  char *page = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  page[0] = (char)0xc3;
  page[4096] = 1;
  mprotect(page, 4096, PROT_READ);
  munmap(page + 4096, 4096);
  long *at = (long *)(page + 4096 + 16);
  __asm__ volatile("movq (%0), %%rax" : : "r"(at) : "rax");
  printf("flags: a load, trap %lu error %lx at the page + %lu\n", trapSeen, errorSeen, addressSeen - (unsigned long)page);
  __asm__ volatile("movq %%rax, (%0)" : : "r"(at) : "memory");
  printf("flags: a store, trap %lu error %lx at the page + %lu\n", trapSeen, errorSeen, addressSeen - (unsigned long)page);
  __asm__ volatile("movq %%rax, (%0)" : : "r"(page + 8) : "memory");
  printf("flags: a store to what is read, trap %lu error %lx at the page + %lu\n", trapSeen, errorSeen,
         addressSeen - (unsigned long)page);
  flagsSeen = 0;
  kill(getpid(), SIGUSR1);
  printf("flags: a signal after, trap %lu error %lx at the page + %lu, the resume flag %lx\n", trapSeen, errorSeen,
         addressSeen - (unsigned long)page, flagsSeen & 0x10000);
  signal(SIGSEGV, SIG_DFL);
  signal(SIGUSR1, SIG_DFL);
}
#else
// N, Z, C and V.
#define FLAGS 0xf0000000UL
static void faulted(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  flagsSeen = user->uc_mcontext.pstate;
  addressSeen = user->uc_mcontext.fault_address;
  user->uc_mcontext.pstate = (user->uc_mcontext.pstate & ~FLAGS) | flagsSet;
  user->uc_mcontext.pc += 4;
}

// The flags of a comparison, in the handler of a load that faults after it, and after that.
static void compare(long left, long right, long *at) {
  unsigned long after;
  __asm__ volatile("cmp %1, %2\n ldr x9, [%3]\n mrs %0, nzcv" : "=&r"(after) : "r"(left), "r"(right), "r"(at) : "cc", "x9");
  printf("flags: in the handler %lx, after it %lx\n", (flagsSeen & FLAGS) >> 28, (after & FLAGS) >> 28);
}

static void flags(void) {
  struct sigaction action = {0};
  action.sa_sigaction = faulted;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGSEGV, &action, 0);
  for (int round = 0; round < 2; round++) {
    flagsSet = round ? 0x90000000UL : 0x60000000UL;
    compare(1, 1, 0);
    compare(1, 2, 0);
    compare(2, 1, 0);
    compare((long)(1UL << 63), 1, 0);
  }
  char *page = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  munmap(page + 4096, 4096);
  compare(1, 1, (long *)(page + 4096 + 16));
  printf("flags: the fault at the page + %lu\n", addressSeen - (unsigned long)page);
  signal(SIGSEGV, SIG_DFL);
}
#endif

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

static long mapped(void *at) { return at == MAP_FAILED ? -1 : 0; }

static void sizes(void) {
  void *end = sbrk(0);
  said("sizes: a break of 2^46 moved it", (void *)syscall(SYS_brk, 1UL << 46) == end ? 0 : 1);
  said("sizes: 2^46 bytes to write", mapped(mmap(0, 1UL << 46, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)));
  said("sizes: 2^48 bytes of nothing", mapped(mmap(0, 1UL << 48, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)));
  said("sizes: a shared 2^46 bytes", mapped(mmap(0, 1UL << 46, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0)));
  said("sizes: a segment of 2^45 bytes", shmget(IPC_PRIVATE, 1UL << 45, 0600));
  said("sizes: munmap of 2^50 bytes", munmap((void *)0x100000, 1UL << 50));
  char *big = mmap(0, 1UL << 30, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  said("sizes: 2^30 bytes to write", mapped(big));
  big[(1UL << 30) - 1] = 2;
  big[1UL << 29] = 3;
  said("sizes: what was written of them", big[(1UL << 30) - 1] + big[1UL << 29] + big[12345678]);
  said("sizes: munmap of them", munmap(big, 1UL << 30));
#ifdef __x86_64__
  // qemu has its own of these.
  char *page = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  said("sizes: mremap to 2^50 bytes", mapped(mremap(page, 4096, 1UL << 50, MREMAP_MAYMOVE)));
  said("sizes: mremap to 2^46 bytes", mapped(mremap(page, 4096, 1UL << 46, MREMAP_MAYMOVE)));
  said("sizes: madvise of what ends before it starts", madvise(page, -4096UL, MADV_DONTNEED));
#endif
}

static volatile int flag;

static void *sleeper(void *unused) {
  usleep(1000);
  flag = 1;
  return 0;
}

// Whether a signal came while the program ran on, which takes it many times as long as the timer.
static int spun(void) {
  for (volatile long round = 0; round < 400000000 && !got; round++) {}
  return got;
}

static void timers(void) {
  struct sigaction action = {0};
  action.sa_handler = counted;
  sigaction(SIGALRM, &action, 0);
  sigaction(SIGVTALRM, &action, 0);
  sigaction(SIGPROF, &action, 0);
  sigaction(SIGUSR2, &action, 0);
  struct itimerval once = {{0, 0}, {0, 1000}};
  int signals[3] = {SIGALRM, SIGVTALRM, SIGPROF};
  for (int which = 0; which < 3; which++) {
    got = 0;
    setitimer(which, &once, 0);
    printf("timers: setitimer %d came while it ran: %d\n", which, spun() == signals[which]);
  }
  timer_t timer;
  struct sigevent event = {0};
  event.sigev_notify = SIGEV_SIGNAL;
  event.sigev_signo = SIGUSR2;
  timer_create(CLOCK_MONOTONIC, &event, &timer);
  struct itimerspec soon = {{0, 0}, {0, 1000000}};
  got = 0;
  timer_settime(timer, 0, &soon, 0);
  printf("timers: timer_create came while it ran: %d\n", spun() == SIGUSR2);
  timer_delete(timer);
  got = 0;
  setitimer(ITIMER_REAL, &once, 0);
  for (long round = 0; round < 20000000 && !got; round++) getppid();
  printf("timers: setitimer came between calls: %d\n", got == SIGALRM);
  pthread_t thread;
  pthread_create(&thread, 0, sleeper, 0);
  for (volatile long round = 0; round < 400000000 && !flag; round++) {}
  printf("timers: a thread's sleep ended while another ran: %d\n", flag);
  pthread_join(thread, 0);
  pid_t spinner = fork();
  if (!spinner) for (;;) {}
  struct timespec before, after;
  clock_gettime(CLOCK_MONOTONIC, &before);
  usleep(1000);
  clock_gettime(CLOCK_MONOTONIC, &after);
  long took = (after.tv_sec - before.tv_sec) * 1000000000L + after.tv_nsec - before.tv_nsec;
  printf("timers: a sleep beside a process that runs on took its time: %d\n", took >= 1000000 && took < 1000000000);
  kill(spinner, SIGKILL);
  waitpid(spinner, 0, 0);
}

static sigjmp_buf back;
static volatile int lastSignal, lastCode;
static volatile long lastAddress;

static void jumped(int signal, siginfo_t *info, void *context) {
  lastSignal = signal;
  lastCode = info->si_code;
  lastAddress = (long)info->si_addr;
  siglongjmp(back, 1);
}

// What a byte holds, after it is written if it is to be, or what signal the access was.
static void probe(const char *what, volatile char *at, char *base, int write) {
  if (!sigsetjmp(back, 1)) {
    if (write) *at = 7;
    int value = *at;
    printf("bus: %s: %d\n", what, value);
  } else
    printf("bus: %s: %s, code %d, at %ld\n", what, lastSignal == SIGBUS ? "SIGBUS" : "SIGSEGV", lastCode, lastAddress - (long)base);
}

static void bus(void) {
  struct sigaction action = {0};
  action.sa_sigaction = jumped;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGBUS, &action, 0);
  sigaction(SIGSEGV, &action, 0);
  long page = 4096;
  int file = memfd_create("file", 0);
  ftruncate(file, 100);
  char *shared = mmap(0, 3 * page, PROT_READ | PROT_WRITE, MAP_SHARED, file, 0);
  char *own = mmap(0, 3 * page, PROT_READ | PROT_WRITE, MAP_PRIVATE, file, 0);
  probe("in the page of the end", shared + 200, shared, 1);
  probe("a page past it", shared + page + 3, shared, 0);
  probe("a store two pages past it", shared + 2 * page + 3, shared, 1);
  probe("a page past it of a private mapping", own + page + 3, own, 0);
  ftruncate(file, page + 1);
  probe("the second page of a longer file", shared + page, shared, 1);
  probe("its third", shared + 2 * page + 3, shared, 0);
  ftruncate(file, 0);
  probe("the first page of an empty file", shared + 3, shared, 0);
  probe("and of the private mapping", own + 3, own, 0);
  said("bus: mprotect of it", mprotect(shared, 3 * page, PROT_READ));
  probe("the first page, to be read", shared + 3, shared, 0);
  ftruncate(file, 3 * page);
  probe("the first page of a file of three", shared + 3, shared, 0);
  probe("the second, which was written", shared + page, shared, 0);
  probe("a store to what is to be read", shared + page + 3, shared, 1);
  said("bus: mprotect of it", mprotect(shared, 3 * page, PROT_READ | PROT_WRITE));
  shared[5] = 9;
  ftruncate(file, 10);
  pid_t made = fork();
  if (!made) {
    signal(SIGBUS, SIG_DFL);
    shared[page] = 1;
    _exit(0);
  }
  int status;
  waitpid(made, &status, 0);
  printf("bus: a child that handles nothing ended of SIGBUS: %d, and the parent has %d\n",
         WIFSIGNALED(status) && WTERMSIG(status) == SIGBUS, shared[5]);
  made = fork();
  if (!made) {
    ftruncate(file, 2 * page);
    shared[page] = 3;
    _exit(0);
  }
  waitpid(made, &status, 0);
  probe("the second page that a child made and wrote", shared + page, shared, 0);
  probe("the third", shared + 2 * page, shared, 0);
  munmap(shared, 3 * page);
  munmap(own, 3 * page);
  shared = mmap(0, 2 * page, PROT_READ, MAP_SHARED, file, page);
  probe("a mapping from the second page", shared, shared, 0);
  probe("its second", shared + page, shared, 0);
  munmap(shared, 2 * page);
  close(file);
  signal(SIGBUS, SIG_DFL);
  signal(SIGSEGV, SIG_DFL);
}

// Code that gives back `value`, and code that stores its second argument where its first says.
static void giving(unsigned char *at, int value) {
#ifdef __x86_64__
  unsigned char code[] = {0xb8, (unsigned char)value, 0, 0, 0, 0xc3};
#else
  unsigned int code[] = {0x52800000u | ((unsigned)value << 5), 0xd65f03c0u};
#endif
  memcpy(at, code, sizeof code);
}

static void storing(unsigned char *at) {
#ifdef __x86_64__
  unsigned char code[] = {0x89, 0x37, 0xc3};
#else
  unsigned int code[] = {0xb9000001u, 0xd65f03c0u};
#endif
  memcpy(at, code, sizeof code);
}

static void shared(void) {
  int segment = shmget(IPC_PRIVATE, 10000, 0600);
  char *first = shmat(segment, 0, 0), *second = shmat(segment, 0, 0), *reads = shmat(segment, 0, SHM_RDONLY);
  strcpy(first, "one");
  printf("shared: a segment attached twice, and to be read: '%s' '%s'\n", second, reads);
  strcpy(second + 5000, "two");
  printf("shared: its second page, written by the second: '%s' '%s'\n", first + 5000, reads + 5000);
  char *third = shmat(segment, 0, 0);
  strcpy(first + 16, "late");
  printf("shared: attached once more: '%s' '%s' '%s'\n", third, second + 16, third + 16);
  // Back and forth, and a copy from one to the other.
  int same = 1;
  for (int round = 0; round < 50; round++) {
    first[100] = (char)round;
    same &= second[100] == (char)round;
    second[101] = (char)(round + 1);
    same &= first[101] == (char)(round + 1) && reads[100] == (char)round;
  }
  memcpy(first + 200, "copied from the first", 22);
  memcpy(second + 300, first + 200, 22);
  memmove(second + 310, second + 300, 22);
  printf("shared: each sees what the other wrote: %d, and a copy between them: '%s' '%s'\n", same, third + 300, first + 310);
  if (!fork()) {
    strcpy(first + 32, "child");
    _exit(strcmp(second + 32, "child") != 0);
  }
  int status;
  wait(&status);
  printf("shared: a child saw its own: %d, and the parent: '%s' '%s'\n", WEXITSTATUS(status) == 0, second + 32, reads + 32);
  shmdt(second);
  shmdt(third);
  strcpy(first + 64, "alone");
  printf("shared: with the others gone: '%s' '%s'\n", first + 64, reads + 64);
  shmdt(reads);
  shmdt(first);
  shmctl(segment, IPC_RMID, 0);
  int file = memfd_create("file", 0);
  ftruncate(file, 8192);
  char *all = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_SHARED, file, 0);
  char *again = mmap(0, 8192, PROT_READ, MAP_SHARED, file, 0);
  char *part = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, file, 4096);
  strcpy(all, "file");
  strcpy(all + 4096, "page");
  printf("shared: a file mapped three times: '%s' '%s' '%s'\n", again, again + 4096, part);
  strcpy(part + 8, "part");
  char read4[5] = {0};
  pread(file, read4, 4, 4096 + 8);
  printf("shared: written by the one of its second page: '%s' '%s', and read: '%s'\n", all + 4096 + 8, again + 4096 + 8, read4);
  pwrite(file, "WXYZ", 4, 100);
  printf("shared: what pwrite wrote: '%.4s' '%.4s'\n", all + 100, again + 100);
  munmap(all, 8192);
  munmap(again, 8192);
  munmap(part, 4096);
  close(file);
  // Code, written through one mapping and run through another.
  file = memfd_create("code", 0);
  ftruncate(file, 4096);
  unsigned char *written = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, file, 0);
  unsigned char *run = mmap(0, 4096, PROT_READ | PROT_EXEC, MAP_SHARED, file, 0);
  int (*give)(void) = (int (*)(void))run;
  giving(written, 1);
  __builtin___clear_cache((char *)run, (char *)run + 64);
  int one = give();
  giving(written, 2);
  __builtin___clear_cache((char *)run, (char *)run + 64);
  int two = give();
  printf("shared: code written through one mapping gives %d, and written again %d\n", one, two);
  // And code that stores, through the one that is written, to the page that it is in.
  storing(written + 512);
  __builtin___clear_cache((char *)run, (char *)run + 1024);
  void (*store)(void *, int) = (void (*)(void *, int))(run + 512);
  int sum = 0;
  for (int round = 1; round <= 5; round++) {
    store(written + 1024, round);
    sum += *(int *)(run + 1024);
  }
  printf("shared: code that stores to its own page through the other mapping: %d\n", sum);
  munmap(written, 4096);
  munmap(run, 4096);
  close(file);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  child();
  flags();
  sizes();
  timers();
  bus();
  shared();
  return 0;
}
