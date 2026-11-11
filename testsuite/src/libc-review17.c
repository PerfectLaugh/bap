// What Linux does with processes, signals and events that a fifth review found the machine didn't, each in a process of its own:
//   uring: a link ends with the call that submits it, ASYNC_CANCEL of the head of a link cancels what is linked to it, and a ring
//     whose CQ is smaller than its SQ is EINVAL.
//   orphan: a process group with no parent outside it in its session doesn't stop of SIGTSTP, SIGTTIN or SIGTTOU, which are discarded,
//     and a read of its terminal from the background is EIO.
//   stopped: a signal that kills a process that is stopped waits for SIGCONT, and kills it then.
//   wait: wait4 takes neither WNOWAIT nor a flag that there isn't, and waitid no flag that there isn't: EINVAL.
//   sockets: listen of a socket that isn't bound, and accept4 of a flag that there isn't, are EINVAL.
//   timers: what a timer goes on with is nothing once it is disarmed, and timer_create takes only the clocks that have timers.
//   sched: the errors of sched_setscheduler and sched_setparam, in the order that Linux has them.
//   order: of kill, tgkill, tkill, rt_sigqueueinfo, rt_sigaction and rt_sigpending, which error comes first.
//   sigtimedwait: of an info that can't be written, EFAULT, and the signal is gone.
//   resethand: SA_RESETHAND makes the handler SIG_DFL and leaves the flags and the mask.
//   pgid: what setpgid and setsid may not do.
// It runs as user 1000.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <linux/io_uring.h>
#include <sched.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static const char *error(long result) { return result < 0 ? strerror(errno) : "ok"; }

static void part(const char *name, void (*body)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(10);
    printf("%s: ", name);
    body();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (!WIFEXITED(status) || WEXITSTATUS(status) != 0) printf("%s ended with %x\n", name, status);
}

static int ring;
static unsigned *sqHead, *sqTail, *sqMask, *sqArray, *cqHead, *cqTail, *cqMask;
static struct io_uring_sqe *sqes;
static struct io_uring_cqe *cqes;

static void setup(void) {
  struct io_uring_params params;
  memset(&params, 0, sizeof params);
  ring = syscall(SYS_io_uring_setup, 8, &params);
  char *sq = mmap(0, params.sq_off.array + params.sq_entries * 4, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQ_RING);
  char *cq = mmap(0, params.cq_off.cqes + params.cq_entries * sizeof(struct io_uring_cqe), PROT_READ | PROT_WRITE, MAP_SHARED, ring,
                  IORING_OFF_CQ_RING);
  sqes = mmap(0, params.sq_entries * 64, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQES);
  sqHead = (void *)(sq + params.sq_off.head);
  sqTail = (void *)(sq + params.sq_off.tail);
  sqMask = (void *)(sq + params.sq_off.ring_mask);
  sqArray = (void *)(sq + params.sq_off.array);
  cqHead = (void *)(cq + params.cq_off.head);
  cqTail = (void *)(cq + params.cq_off.tail);
  cqMask = (void *)(cq + params.cq_off.ring_mask);
  cqes = (void *)(cq + params.cq_off.cqes);
}

static struct io_uring_sqe *entry(void) {
  unsigned tail = *sqTail;
  unsigned index = tail & *sqMask;
  sqArray[index] = index;
  memset(&sqes[index], 0, 64);
  *sqTail = tail + 1;
  return &sqes[index];
}

static void drain(void) {
  while (*cqHead != *cqTail) {
    struct io_uring_cqe *completion = &cqes[*cqHead & *cqMask];
    printf("%llu:%d ", (unsigned long long)completion->user_data, completion->res);
    (*cqHead)++;
  }
}

static long enter(unsigned submit, unsigned wait) {
  return syscall(SYS_io_uring_enter, ring, submit, wait, wait ? IORING_ENTER_GETEVENTS : 0, 0, 0);
}

static void uring(void) {
  setup();
  int ends[2];
  pipe(ends);
  char buffer[16];
  struct io_uring_sqe *sqe = entry();
  sqe->opcode = IORING_OP_READ;
  sqe->fd = ends[0];
  sqe->addr = (uintptr_t)buffer;
  sqe->len = sizeof buffer;
  sqe->off = -1;
  sqe->flags = IOSQE_IO_LINK;
  sqe->user_data = 1;
  enter(1, 0);
  sqe = entry();
  sqe->opcode = IORING_OP_NOP;
  sqe->user_data = 2;
  enter(1, 0);
  printf("a link of one call, then another: ");
  drain();
  write(ends[1], "x", 1);
  enter(0, 1);
  drain();
  printf("\nuring: cancelled at its head: ");
  sqe = entry();
  sqe->opcode = IORING_OP_READ;
  sqe->fd = ends[0];
  sqe->addr = (uintptr_t)buffer;
  sqe->len = sizeof buffer;
  sqe->off = -1;
  sqe->flags = IOSQE_IO_LINK;
  sqe->user_data = 3;
  sqe = entry();
  sqe->opcode = IORING_OP_NOP;
  sqe->user_data = 4;
  enter(2, 0);
  sqe = entry();
  sqe->opcode = IORING_OP_ASYNC_CANCEL;
  sqe->addr = 3;
  sqe->user_data = 5;
  enter(1, 3);
  drain();
  struct io_uring_params params;
  memset(&params, 0, sizeof params);
  params.flags = IORING_SETUP_CQSIZE;
  params.cq_entries = 2;
  printf("\nuring: a CQ smaller than the SQ %s\n", error(syscall(SYS_io_uring_setup, 8, &params)));
}

static void orphan(void) {
  pid_t child = fork();
  if (child == 0) {
    setsid();
    kill(getpid(), SIGTSTP);
    printf("after SIGTSTP, ");
    kill(getpid(), SIGTTIN);
    printf("SIGTTIN, ");
    kill(getpid(), SIGTTOU);
    printf("SIGTTOU, ");
    _exit(3);
  }
  int status;
  waitpid(child, &status, WUNTRACED);
  printf("it %s\n", WIFSTOPPED(status) ? "stopped" : WIFEXITED(status) ? "exited" : "was killed");
  if (WIFSTOPPED(status)) {
    kill(child, SIGKILL);
    waitpid(child, &status, 0);
  }
  // A read of the terminal from the background of a group that is orphaned is EIO: a session of its own of a pseudo-terminal, whose
  // leader stays, and a group of a process whose parent left, so that it has none in its session.
  int ends[2];
  pipe(ends);
  pid_t leader = fork();
  if (leader == 0) {
    setsid();
    int master = posix_openpt(O_RDWR | O_NOCTTY);
    grantpt(master);
    unlockpt(master);
    int slave = open(ptsname(master), O_RDWR);
    pid_t middle = fork();
    if (middle == 0) {
      setpgid(0, 0);
      pid_t self = getpid();
      if (fork() == 0) {
        while (getppid() == self) sched_yield();
        char byte;
        long result = read(slave, &byte, 1);
        dprintf(ends[1], "%s", result < 0 && errno == EIO ? "EIO" : "something else");
        _exit(0);
      }
      _exit(0);
    }
    waitpid(middle, 0, 0);
    char said[32] = {0};
    read(ends[0], said, sizeof said - 1);
    printf("orphan: a read of the terminal from the background of a group that is orphaned: %s\n", said);
    _exit(0);
  }
  waitpid(leader, 0, 0);
}

static void stopped(void) {
  int ends[2];
  pipe(ends);
  pid_t child = fork();
  if (child == 0) {
    char byte;
    read(ends[0], &byte, 1);
    _exit(7);
  }
  kill(child, SIGSTOP);
  int status;
  waitpid(child, &status, WUNTRACED);
  kill(child, SIGTERM);
  siginfo_t info;
  memset(&info, 0, sizeof info);
  // A while, for what would kill it to have.
  struct timespec pause = {0, 20000000};
  nanosleep(&pause, 0);
  waitid(P_PID, child, &info, WEXITED | WNOHANG);
  printf("SIGTERM while stopped: it %s, ", info.si_pid == child ? "ended" : "waits");
  kill(child, SIGCONT);
  waitpid(child, &status, 0);
  printf("after SIGCONT %s %d\n", WIFSIGNALED(status) ? "killed by" : "exited", WIFSIGNALED(status) ? WTERMSIG(status) : WEXITSTATUS(status));
}

static void waits(void) {
  pid_t child = fork();
  if (child == 0) _exit(4);
  struct timespec pause = {0, 20000000};
  nanosleep(&pause, 0);
  int status;
  siginfo_t info;
  printf("wait4 WNOWAIT %s, ", error(syscall(SYS_wait4, child, &status, WNOWAIT, 0)));
  printf("of 0x100 %s, ", error(syscall(SYS_wait4, child, &status, 0x100, 0)));
  printf("waitid of 0x100 %s, ", error(syscall(SYS_waitid, P_PID, child, &info, WEXITED | 0x100, 0)));
  printf("waitid of no event %s, ", error(syscall(SYS_waitid, P_PID, child, &info, WNOHANG, 0)));
  long reaped = syscall(SYS_wait4, child, &status, 0, 0);
  printf("then %s %d\n", reaped == child ? "reaped" : "not", WEXITSTATUS(status));
}

static void sockets(void) {
  int unbound = socket(AF_UNIX, SOCK_STREAM, 0);
  printf("listen unbound %s, ", error(listen(unbound, 1)));
  int listener = socket(AF_UNIX, SOCK_STREAM, 0);
  struct sockaddr_un address;
  memset(&address, 0, sizeof address);
  address.sun_family = AF_UNIX;
  strcpy(address.sun_path + 1, "bap-review17");
  socklen_t size = offsetof(struct sockaddr_un, sun_path) + 13;
  bind(listener, (void *)&address, size);
  listen(listener, 1);
  fcntl(listener, F_SETFL, O_NONBLOCK);
  printf("accept4 of 0x1 %s, ", error(accept4(listener, 0, 0, 0x1)));
  printf("nonblocking %s, ", error(accept4(listener, 0, 0, SOCK_NONBLOCK)));
  int client = socket(AF_UNIX, SOCK_STREAM, 0);
  connect(client, (void *)&address, size);
  printf("connect again %s, ", error(connect(client, (void *)&address, size)));
  printf("listen connected %s\n", error(listen(client, 1)));
}

static void timers(void) {
  timer_t timer;
  struct sigevent event;
  memset(&event, 0, sizeof event);
  event.sigev_notify = SIGEV_NONE;
  timer_create(CLOCK_MONOTONIC, &event, &timer);
  struct itimerspec setting = {{1, 0}, {0, 0}}, now;
  timer_settime(timer, 0, &setting, 0);
  timer_gettime(timer, &now);
  printf("disarmed with an interval: %ld %ld, ", (long)now.it_interval.tv_sec, (long)now.it_value.tv_sec);
  struct itimerspec armed = {{1, 0}, {5, 0}}, old;
  timer_settime(timer, 0, &armed, 0);
  timer_settime(timer, 0, &setting, &old);
  printf("the old %ld, ", (long)old.it_interval.tv_sec);
  timer_gettime(timer, &now);
  printf("then %ld\n", (long)now.it_interval.tv_sec);
  printf("timers: clocks");
  for (int clock = 0; clock < 13; clock++) {
    timer_t made;
    long result = syscall(SYS_timer_create, clock, &event, &made);
    printf(" %d %s", clock, result < 0 ? strerror(errno) : "ok");
    if (result == 0) syscall(SYS_timer_delete, made);
  }
  struct itimerval interval = {{1, 0}, {0, 0}}, read;
  setitimer(ITIMER_REAL, &interval, 0);
  getitimer(ITIMER_REAL, &read);
  printf("\ntimers: setitimer disarmed with an interval %ld\n", (long)read.it_interval.tv_sec);
}

static void sched(void) {
  struct sched_param param = {0};
  printf("setscheduler of -1 %s, ", error(syscall(SYS_sched_setscheduler, -1, SCHED_OTHER, &param)));
  printf("of no param %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_OTHER, 0)));
  printf("of a param that isn't there %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_OTHER, 8)));
  printf("of no process %s, ", error(syscall(SYS_sched_setscheduler, 999999, 77, &param)));
  printf("of a policy that isn't %s\n", error(syscall(SYS_sched_setscheduler, 0, 77, &param)));
  param.sched_priority = 5;
  printf("sched: SCHED_OTHER of 5 %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_OTHER, &param)));
  param.sched_priority = 50;
  printf("SCHED_FIFO of 50 %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_FIFO, &param)));
  param.sched_priority = 0;
  printf("SCHED_FIFO of 0 %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_FIFO, &param)));
  printf("setparam of -1 %s, ", error(syscall(SYS_sched_setparam, -1, &param)));
  printf("of no process %s, ", error(syscall(SYS_sched_setparam, 999999, &param)));
  param.sched_priority = 5;
  printf("of 5 %s\n", error(syscall(SYS_sched_setparam, 0, &param)));
  printf("sched: getparam of -1 %s, ", error(syscall(SYS_sched_getparam, -1, &param)));
  printf("of no process %s, ", error(syscall(SYS_sched_getparam, 999999, &param)));
  printf("getscheduler of -1 %s, ", error(syscall(SYS_sched_getscheduler, -1)));
  printf("of no process %s\n", error(syscall(SYS_sched_getscheduler, 999999)));
}

static void handler(int signal) { (void)signal; }

static void order(void) {
  sigset_t blocked;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGUSR1);
  sigprocmask(SIG_BLOCK, &blocked, 0);
  printf("kill of 99 to no one %s, ", error(kill(999999, 99)));
  printf("of 0 to no one %s, ", error(kill(999999, 0)));
  printf("tgkill of 0 %s, ", error(syscall(SYS_tgkill, 0, getpid(), 0)));
  printf("of 99 to no thread %s, ", error(syscall(SYS_tgkill, getpid(), 999999, 99)));
  printf("of 0 to no thread %s, ", error(syscall(SYS_tgkill, getpid(), 999999, 0)));
  printf("tkill of -1 %s, ", error(syscall(SYS_tkill, -1, 0)));
  printf("of 99 %s\n", error(syscall(SYS_tkill, getpid(), 99)));
  siginfo_t info;
  memset(&info, 0, sizeof info);
  info.si_code = SI_QUEUE;
  printf("order: rt_sigqueueinfo of 99 to no one %s, ", error(syscall(SYS_rt_sigqueueinfo, 999999, 99, &info)));
  printf("of 0 to no one %s, ", error(syscall(SYS_rt_sigqueueinfo, 999999, 0, &info)));
  printf("of an info that isn't there %s, ", error(syscall(SYS_rt_sigqueueinfo, 999999, 99, 8)));
  info.si_code = 0;
  printf("as the kernel to itself %s\n", error(syscall(SYS_rt_sigqueueinfo, getpid(), SIGUSR1, &info)));
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  printf("order: rt_sigaction of SIGKILL %s, ", error(syscall(SYS_rt_sigaction, SIGKILL, &action, 0, 8)));
  printf("of 99 of a size that isn't %s, ", error(syscall(SYS_rt_sigaction, 99, &action, 0, 4)));
  printf("of SIGKILL with nothing %s, ", error(syscall(SYS_rt_sigaction, SIGKILL, 0, 0, 8)));
  printf("of an action that isn't there %s, ", error(syscall(SYS_rt_sigaction, SIGUSR1, 8, 0, 8)));
  printf("rt_sigpending of 4 %s, ", error(syscall(SYS_rt_sigpending, &action, 4)));
  printf("to where nothing is %s\n", error(syscall(SYS_rt_sigpending, 8, 8)));
}

static void timedWait(void) {
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigprocmask(SIG_BLOCK, &set, 0);
  raise(SIGUSR1);
  struct timespec none = {0, 0};
  printf("of an info that isn't there %s, ", error(syscall(SYS_rt_sigtimedwait, &set, 8, &none, 8)));
  sigset_t pending;
  sigpending(&pending);
  printf("pending after %d\n", sigismember(&pending, SIGUSR1));
}

static void resetHand(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = handler;
  action.sa_flags = SA_RESETHAND | SA_RESTART | SA_NODEFER;
  sigaddset(&action.sa_mask, SIGUSR2);
  sigaction(SIGUSR1, &action, 0);
  raise(SIGUSR1);
  struct sigaction now;
  sigaction(SIGUSR1, 0, &now);
  printf("handler %s, flags %#x, SIGUSR2 in the mask %d\n", now.sa_handler == SIG_DFL ? "SIG_DFL" : "kept",
         now.sa_flags & (SA_RESETHAND | SA_RESTART | SA_NODEFER), sigismember(&now.sa_mask, SIGUSR2));
}

static void groups(void) {
  printf("setpgid of -1 %s, ", error(setpgid(0, -1)));
  printf("of no one %s, ", error(setpgid(999999, 0)));
  printf("of init %s, ", error(setpgid(1, 0)));
  printf("to a group that isn't there %s, ", error(setpgid(0, 999999)));
  setpgid(0, 0);
  printf("setsid of a leader %s, ", error(setsid()));
  int up[2], down[2];
  pipe(up);
  pipe(down);
  pid_t child = fork();
  if (child == 0) {
    setsid();
    char byte;
    write(up[1], "x", 1);
    read(down[0], &byte, 1);
    _exit(0);
  }
  char byte;
  read(up[0], &byte, 1);
  printf("of a child of another session %s, ", error(setpgid(child, 0)));
  printf("into its group %s\n", error(setpgid(0, child)));
  write(down[1], "x", 1);
  waitpid(child, 0, 0);
  int ready[2];
  pipe(ready);
  child = fork();
  if (child == 0) {
    close(ready[0]);
    fcntl(ready[1], F_SETFD, FD_CLOEXEC);
    execl("/proc/self/exe", "review17", "wait", (char *)0);
    _exit(1);
  }
  close(ready[1]);
  read(ready[0], &byte, 1);
  printf("pgid: of a child that ran a program %s\n", error(setpgid(child, child)));
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

int main(int count, char **arguments) {
  setvbuf(stdout, 0, _IONBF, 0);
  // What a child that ran a program does: waits to be killed.
  if (count > 1) {
    pause();
    return 0;
  }
  // As a user, who has no capabilities.
  setgid(1000);
  setuid(1000);
  part("uring", uring);
  part("orphan", orphan);
  part("stopped", stopped);
  part("wait", waits);
  part("sockets", sockets);
  part("timers", timers);
  part("sched", sched);
  part("order", order);
  part("sigtimedwait", timedWait);
  part("resethand", resetHand);
  part("pgid", groups);
  printf("done\n");
  return 0;
}
