// What Linux does that a second review found the machine didn't, each in a process of its own, with an alarm that ends what would hang:
//   traced: a signal that a tracer lets through has what it was sent with: SI_QUEUE and the value of sigqueue.
//   shutdown: of a listening socket is 0, and an accept that waits there then fails with EINVAL.
//   rcvtimeo: a recv of a socket with SO_RCVTIMEO fails with EAGAIN when the time is up.
//   waitall: a recv of MSG_WAITALL waits for all that it asks for.
//   auxv: /proc/self/auxv has AT_RANDOM and AT_EXECFN, as the stack has.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/ptrace.h>
#include <sys/socket.h>
#include <sys/time.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

static void part(const char *name, void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(3);
    run();
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  if (WIFSIGNALED(status)) printf("%s: ended by signal %d\n", name, WTERMSIG(status));
}

static volatile int code = -1, value = -1;
static void informed(int signal, siginfo_t *info, void *context) {
  (void)signal;
  (void)context;
  code = info->si_code;
  value = info->si_value.sival_int;
}

static void traced(void) {
  pid_t child = fork();
  if (child == 0) {
    struct sigaction action;
    memset(&action, 0, sizeof action);
    action.sa_sigaction = informed;
    action.sa_flags = SA_SIGINFO;
    sigaction(SIGUSR1, &action, 0);
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    union sigval sent;
    sent.sival_int = 42;
    sigqueue(getpid(), SIGUSR1, sent);
    printf("a signal a tracer lets through: code %d value %d\n", code, value);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  ptrace(PTRACE_CONT, child, 0, WIFSTOPPED(status) ? WSTOPSIG(status) : 0);
  waitpid(child, &status, 0);
}

static int listener;
static void *acceptor(void *unused) {
  (void)unused;
  int result = accept(listener, 0, 0);
  printf("accept after shutdown: %d %s\n", result, result < 0 && errno == EINVAL ? "EINVAL" : "");
  return 0;
}

static void shutdownListener(void) {
  listener = socket(AF_UNIX, SOCK_STREAM, 0);
  struct sockaddr_un address = {AF_UNIX, "\0review3"};
  bind(listener, (struct sockaddr *)&address, sizeof address);
  listen(listener, 1);
  pthread_t thread;
  pthread_create(&thread, 0, acceptor, 0);
  usleep(100000);
  int result = shutdown(listener, SHUT_RDWR);
  printf("shutdown of a listener: %d\n", result);
  pthread_join(thread, 0);
}

static void receiveTimeout(void) {
  int pair[2];
  socketpair(AF_UNIX, SOCK_STREAM, 0, pair);
  struct timeval limit = {0, 200000};
  setsockopt(pair[0], SOL_SOCKET, SO_RCVTIMEO, &limit, sizeof limit);
  struct timeval got = {0, 0};
  socklen_t size = sizeof got;
  getsockopt(pair[0], SOL_SOCKET, SO_RCVTIMEO, &got, &size);
  char buffer[4];
  int result = recv(pair[0], buffer, sizeof buffer, 0);
  printf("SO_RCVTIMEO of %ld us, recv: %d %s\n", (long)got.tv_usec, result, result < 0 && errno == EAGAIN ? "EAGAIN" : "");
}

static void waitAll(void) {
  int pair[2];
  socketpair(AF_UNIX, SOCK_STREAM, 0, pair);
  if (fork() == 0) {
    write(pair[1], "abcd", 4);
    usleep(100000);
    write(pair[1], "efgh", 4);
    _exit(0);
  }
  char buffer[8];
  printf("recv of MSG_WAITALL of 8: %zd\n", recv(pair[0], buffer, sizeof buffer, MSG_WAITALL));
}

static void auxv(void) {
  unsigned long entries[128];
  int fd = open("/proc/self/auxv", O_RDONLY);
  long size = read(fd, entries, sizeof entries);
  int random = 0, execfn = 0;
  for (long index = 0; index + 1 < size / (long)sizeof(unsigned long); index += 2) {
    if (entries[index] == 25) random = 1;
    if (entries[index] == 31) execfn = 1;
  }
  printf("/proc/self/auxv has AT_RANDOM %d and AT_EXECFN %d\n", random, execfn);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part("traced", traced);
  part("shutdown", shutdownListener);
  part("rcvtimeo", receiveTimeout);
  part("waitall", waitAll);
  part("auxv", auxv);
  printf("done\n");
  return 0;
}
