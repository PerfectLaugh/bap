// What Linux does of signals, waits, timers and io_uring that a third review found the machine didn't, each in a process of its own, with
// an alarm that ends what would hang (testLinuxRaises):
//   ringlink: an entry of a chain that waits holds up only its chain, and one after it completes.
//   ringtimeout: a timeout that is linked holds up what comes after it, which it cancels when it runs out.
//   ringshort: a read that is linked and has less than it asked for cancels what comes after it.
//   tracedwait: a signal of a tracee that its tracer suppresses doesn't end a poll or a sleep, which go on as they were.
//   ppoll: ppoll, pselect and epoll_pwait of what is ready say so, even when the mask that they take lets a pending signal in.
//   timedrestart: a recv of SO_RCVTIMEO and a futex wait with a time end with EINTR of a handler of SA_RESTART.
//   nocldstop: a handler of SIGCHLD of SA_NOCLDSTOP hears of the exit of a child and not of its stop or continue.
//   contdiscard: SIGCONT takes away a stop signal that is pending.
//   order: a signal of the thread comes before one of the process.
//   dflstop: a stop signal that is pending stays when its action is set to the default.
//   chldmerge: SIGCHLD of two children while it is blocked is one.
//   timers: timer_create of no signal, of a signal past the last, and of a thread that there isn't, is EINVAL; setitimer of no value disarms.
//   futexwake: FUTEX_WAKE of 0 wakes one.
//   wait4fault: wait4 of a status that can't be written is EFAULT, and the child is gone.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/futex.h>
#include <linux/io_uring.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/select.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void part(const char *name, void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(5);
    run();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("%s: ended by signal %d\n", name, WTERMSIG(status));
}

static long seconds(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return now.tv_sec * 1000 + now.tv_nsec / 1000000;
}

struct ring {
  int fd;
  struct io_uring_params params;
  char *submit, *complete;
  struct io_uring_sqe *entries;
  unsigned queued;
};

static int ringMake(struct ring *ring) {
  memset(ring, 0, sizeof *ring);
  ring->fd = (int)syscall(SYS_io_uring_setup, 8, &ring->params);
  if (ring->fd < 0) return -1;
  struct io_uring_params *params = &ring->params;
  ring->submit = mmap(0, params->sq_off.array + params->sq_entries * 4, PROT_READ | PROT_WRITE, MAP_SHARED, ring->fd, IORING_OFF_SQ_RING);
  ring->complete = mmap(0, params->cq_off.cqes + params->cq_entries * sizeof(struct io_uring_cqe), PROT_READ | PROT_WRITE, MAP_SHARED,
                        ring->fd, IORING_OFF_CQ_RING);
  ring->entries = mmap(0, params->sq_entries * sizeof(struct io_uring_sqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring->fd, IORING_OFF_SQES);
  return 0;
}

static struct io_uring_sqe *ringAdd(struct ring *ring, int opcode, int flags, unsigned long data) {
  unsigned *tail = (unsigned *)(ring->submit + ring->params.sq_off.tail);
  unsigned index = (*tail + ring->queued) & (ring->params.sq_entries - 1);
  struct io_uring_sqe *entry = &ring->entries[index];
  memset(entry, 0, sizeof *entry);
  entry->opcode = opcode;
  entry->flags = flags;
  entry->user_data = data;
  ((unsigned *)(ring->submit + ring->params.sq_off.array))[index] = index;
  ring->queued++;
  return entry;
}

static int ringEnter(struct ring *ring, unsigned wait) {
  unsigned *tail = (unsigned *)(ring->submit + ring->params.sq_off.tail);
  unsigned count = ring->queued;
  __atomic_store_n(tail, *tail + count, __ATOMIC_RELEASE);
  ring->queued = 0;
  return (int)syscall(SYS_io_uring_enter, ring->fd, count, wait, IORING_ENTER_GETEVENTS, 0, 0);
}

// What has completed, as its data and result, in order.
static void ringSay(struct ring *ring) {
  unsigned *head = (unsigned *)(ring->complete + ring->params.cq_off.head);
  unsigned tail = __atomic_load_n((unsigned *)(ring->complete + ring->params.cq_off.tail), __ATOMIC_ACQUIRE);
  struct io_uring_cqe *results = (struct io_uring_cqe *)(ring->complete + ring->params.cq_off.cqes);
  for (; *head != tail; (*head)++) {
    struct io_uring_cqe *result = &results[*head & (ring->params.cq_entries - 1)];
    printf(" %llu:%s", (unsigned long long)result->user_data, result->res >= 0 ? "ok" : result->res == -ETIME ? "ETIME"
                                                              : result->res == -ECANCELED ? "ECANCELED" : strerror(-result->res));
  }
}

static void ringLink(void) {
  struct ring ring;
  if (ringMake(&ring) < 0) {
    printf("ringlink: no io_uring\n");
    return;
  }
  int pipes[2];
  pipe(pipes);
  static char buffer[8];
  struct io_uring_sqe *entry = ringAdd(&ring, IORING_OP_READ, IOSQE_IO_LINK, 1);
  entry->fd = pipes[0];
  entry->addr = (unsigned long)buffer;
  entry->len = 1;
  ringAdd(&ring, IORING_OP_NOP, 0, 2);
  ringAdd(&ring, IORING_OP_NOP, 0, 3);
  ringEnter(&ring, 1);
  printf("ringlink: completed");
  ringSay(&ring);
  write(pipes[1], "x", 1);
  syscall(SYS_io_uring_enter, ring.fd, 0, 2, IORING_ENTER_GETEVENTS, 0, 0);
  printf(", then");
  ringSay(&ring);
  printf("\n");
}

static void ringTimeout(void) {
  struct ring ring;
  if (ringMake(&ring) < 0) {
    printf("ringtimeout: no io_uring\n");
    return;
  }
  int pipes[2];
  pipe(pipes);
  static struct __kernel_timespec span = {0, 200000000};
  struct io_uring_sqe *entry = ringAdd(&ring, IORING_OP_TIMEOUT, IOSQE_IO_LINK, 1);
  entry->addr = (unsigned long)&span;
  entry->len = 1;
  entry = ringAdd(&ring, IORING_OP_WRITE, 0, 2);
  entry->fd = pipes[1];
  entry->addr = (unsigned long)"x";
  entry->len = 1;
  long start = seconds();
  ringEnter(&ring, 2);
  printf("ringtimeout: after a while %d:", seconds() - start >= 150);
  ringSay(&ring);
  char got;
  printf(", the pipe has %s\n", read(pipes[0], &got, 0) == 0 && fcntl(pipes[0], F_SETFL, O_NONBLOCK) == 0 &&
                                        read(pipes[0], &got, 1) == 1 ? "it" : "nothing");
}

static void ringShort(void) {
  struct ring ring;
  if (ringMake(&ring) < 0) {
    printf("ringshort: no io_uring\n");
    return;
  }
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "ab", 2);
  static char buffer[8];
  struct io_uring_sqe *entry = ringAdd(&ring, IORING_OP_READ, IOSQE_IO_LINK, 1);
  entry->fd = pipes[0];
  entry->addr = (unsigned long)buffer;
  entry->len = 8;
  ringAdd(&ring, IORING_OP_NOP, 0, 2);
  ringEnter(&ring, 2);
  printf("ringshort: completed");
  ringSay(&ring);
  printf("\n");
}

static void tracedWait(void) {
  int pipes[2];
  pipe(pipes);
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    struct pollfd watched = {pipes[0], POLLIN, 0};
    int result = poll(&watched, 1, 3000);
    printf("tracedwait: poll %d %s, ", result, result < 0 ? strerror(errno) : "");
    struct timespec span = {1, 0};
    result = nanosleep(&span, 0);
    printf("nanosleep %d %s\n", result, result < 0 ? strerror(errno) : "");
    _exit(0);
  }
  usleep(200000);
  int status;
  kill(child, SIGWINCH);
  waitpid(child, &status, 0);
  ptrace(PTRACE_CONT, child, 0, 0);
  usleep(300000);
  write(pipes[1], "x", 1);
  usleep(300000);
  kill(child, SIGWINCH);
  waitpid(child, &status, 0);
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
}

static volatile int handled;
static void onSignal(int signal) {
  (void)signal;
  handled++;
}

static void ppollReady(void) {
  signal(SIGUSR1, onSignal);
  sigset_t blocked, none;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigemptyset(&none);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "x", 1);
  struct pollfd watched = {pipes[0], POLLIN, 0};
  raise(SIGUSR1);
  int result = ppoll(&watched, 1, 0, &none);
  printf("ppoll: of what is ready %d, handled %d, ", result, handled);
  fd_set readable;
  FD_ZERO(&readable);
  FD_SET(pipes[0], &readable);
  result = pselect(pipes[0] + 1, &readable, 0, 0, 0, &none);
  printf("pselect %d, ", result);
  int poller = epoll_create1(0);
  struct epoll_event event = {EPOLLIN, {0}};
  epoll_ctl(poller, EPOLL_CTL_ADD, pipes[0], &event);
  result = epoll_pwait(poller, &event, 1, -1, &none);
  printf("epoll_pwait %d, handled %d\n", result, handled);
}

static void timedRestart(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = onSignal;
  action.sa_flags = SA_RESTART;
  sigaction(SIGALRM, &action, 0);
  int pair[2];
  socketpair(AF_UNIX, SOCK_STREAM, 0, pair);
  struct timeval limit = {2, 0};
  setsockopt(pair[0], SOL_SOCKET, SO_RCVTIMEO, &limit, sizeof limit);
  char buffer[4];
  alarm(1);
  long start = seconds();
  int result = recv(pair[0], buffer, sizeof buffer, 0);
  printf("timedrestart: recv %d %s after %ld s, ", result, result < 0 ? strerror(errno) : "", (seconds() - start + 500) / 1000);
  static int word = 0;
  struct timespec span = {3, 0};
  alarm(1);
  start = seconds();
  result = (int)syscall(SYS_futex, &word, FUTEX_WAIT_PRIVATE, 0, &span, 0, 0);
  printf("futex %d %s after %ld s\n", result, result < 0 ? strerror(errno) : "", (seconds() - start + 500) / 1000);
}

static void noCldStop(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = onSignal;
  action.sa_flags = SA_NOCLDSTOP;
  sigaction(SIGCHLD, &action, 0);
  int go[2];
  pipe(go);
  pid_t child = fork();
  if (child == 0) {
    raise(SIGSTOP);
    // It ends when it is told, which is after the parent looked at what it heard of the continue.
    char got;
    read(go[0], &got, 1);
    _exit(0);
  }
  int status;
  waitpid(child, &status, WUNTRACED);
  usleep(100000);
  int stopped = handled;
  kill(child, SIGCONT);
  waitpid(child, &status, WCONTINUED);
  usleep(100000);
  int continued = handled;
  write(go[1], "g", 1);
  waitpid(child, &status, 0);
  usleep(100000);
  printf("nocldstop: heard at the stop %d, the continue %d, the exit %d\n", stopped, continued, handled);
}

static void contDiscard(void) {
  pid_t child = fork();
  if (child == 0) {
    sigset_t blocked;
    sigemptyset(&blocked);
    sigaddset(&blocked, SIGTSTP);
    sigprocmask(SIG_BLOCK, &blocked, 0);
    raise(SIGTSTP);
    kill(getpid(), SIGCONT);
    sigprocmask(SIG_UNBLOCK, &blocked, 0);
    _exit(7);
  }
  int status;
  waitpid(child, &status, WUNTRACED);
  printf("contdiscard: %s %d\n", WIFEXITED(status) ? "exited" : "stopped by", WIFEXITED(status) ? WEXITSTATUS(status) : WSTOPSIG(status));
  if (!WIFEXITED(status)) {
    kill(child, SIGKILL);
    waitpid(child, 0, 0);
  }
}

static char heard[8];
static int count;
static void noted(int signal) { heard[count++] = signal == SIGUSR1 ? 'U' : 'T'; }

static void order(void) {
  signal(SIGUSR1, noted);
  signal(SIGTERM, noted);
  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigaddset(&blocked, SIGTERM);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  syscall(SYS_tgkill, getpid(), gettid(), SIGTERM);
  kill(getpid(), SIGUSR1);
  sigprocmask(SIG_UNBLOCK, &blocked, 0);
  printf("order: of the thread's and the process's, handlers ran %s\n", heard);
}

static void dflStop(void) {
  sigset_t blocked, pending;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGTSTP);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  raise(SIGTSTP);
  signal(SIGTSTP, SIG_DFL);
  sigpending(&pending);
  printf("dflstop: SIGTSTP pending still %d\n", sigismember(&pending, SIGTSTP));
}

static void chldMerge(void) {
  signal(SIGCHLD, onSignal);
  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGCHLD);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  for (int index = 0; index < 2; index++)
    if (fork() == 0) {
      usleep(100000 * (index + 1));
      _exit(0);
    }
  waitpid(-1, 0, 0);
  waitpid(-1, 0, 0);
  sigprocmask(SIG_UNBLOCK, &blocked, 0);
  printf("chldmerge: of two exits, handled %d\n", handled);
}

static const char *invalid(int result) { return result == 0 ? "made" : errno == EINVAL ? "EINVAL" : strerror(errno); }

static void timers(void) {
  timer_t timer;
  struct sigevent event;
  memset(&event, 0, sizeof event);
  event.sigev_notify = SIGEV_SIGNAL;
  event.sigev_signo = 0;
  printf("timers: of signal 0 %s, ", invalid((int)syscall(SYS_timer_create, CLOCK_MONOTONIC, &event, &timer)));
  event.sigev_signo = 65;
  printf("of 65 %s, ", invalid((int)syscall(SYS_timer_create, CLOCK_MONOTONIC, &event, &timer)));
  event.sigev_signo = SIGUSR1;
  event.sigev_notify = 4;  // SIGEV_THREAD_ID
  event.sigev_notify_thread_id = 999999;
  printf("of a thread that isn't %s, ", invalid((int)syscall(SYS_timer_create, CLOCK_MONOTONIC, &event, &timer)));
  struct itimerval value = {{0, 0}, {10, 0}}, left;
  setitimer(ITIMER_REAL, &value, 0);
  syscall(SYS_setitimer, ITIMER_REAL, 0, 0);
  getitimer(ITIMER_REAL, &left);
  printf("setitimer of none leaves %ld\n", (long)left.it_value.tv_sec);
}

static int word;
static void *waiter(void *unused) {
  (void)unused;
  syscall(SYS_futex, &word, FUTEX_WAIT_PRIVATE, 0, 0, 0, 0);
  return 0;
}

static void futexWake(void) {
  pthread_t thread;
  pthread_create(&thread, 0, waiter, 0);
  usleep(200000);
  long woken = syscall(SYS_futex, &word, FUTEX_WAKE_PRIVATE, 0, 0, 0, 0);
  printf("futexwake: of 0 woke %ld\n", woken);
  if (woken == 0) syscall(SYS_futex, &word, FUTEX_WAKE_PRIVATE, 1, 0, 0, 0);
  pthread_join(thread, 0);
}

static void wait4Fault(void) {
  pid_t child = fork();
  if (child == 0) _exit(3);
  usleep(100000);
  long result = syscall(SYS_wait4, -1, (int *)1, 0, 0);
  printf("wait4fault: %ld %s, ", result, result < 0 ? strerror(errno) : "");
  result = syscall(SYS_wait4, -1, 0, WNOHANG, 0);
  printf("again %ld %s\n", result, result < 0 ? strerror(errno) : "");
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part("ringlink", ringLink);
  part("ringtimeout", ringTimeout);
  part("ringshort", ringShort);
  part("tracedwait", tracedWait);
  part("ppoll", ppollReady);
  part("timedrestart", timedRestart);
  part("nocldstop", noCldStop);
  part("contdiscard", contDiscard);
  part("order", order);
  part("dflstop", dflStop);
  part("chldmerge", chldMerge);
  part("timers", timers);
  part("futexwake", futexWake);
  part("wait4fault", wait4Fault);
  printf("done\n");
  return 0;
}
