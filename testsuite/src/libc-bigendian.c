// What a big-endian machine has of a sigset of more than one word and of union semun as Linux has them (testLinuxRaises):
//   signalfd: its mask is of words, the low one first, of the size of the kernel's sigset_t, and another size is EINVAL.
//   semctl: SETVAL takes the int of union semun, which is the high half of the word on a 64-bit machine.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/ipc.h>
#include <sys/sem.h>
#include <sys/signalfd.h>
#include <sys/syscall.h>
#include <unistd.h>

union semun {
  int val;
  void *buf;
};

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  sigset_t set;
  sigemptyset(&set);
  sigaddset(&set, SIGUSR1);
  sigprocmask(SIG_BLOCK, &set, 0);
  long wrong = syscall(SYS_signalfd4, -1, &set, 4, 0);
  printf("signalfd of a mask of 4 bytes: %s\n", wrong < 0 && errno == EINVAL ? "EINVAL" : "made");
  int fd = signalfd(-1, &set, 0);
  raise(SIGUSR1);
  struct signalfd_siginfo info;
  memset(&info, 0, sizeof info);
  ssize_t size = read(fd, &info, sizeof info);
  printf("signalfd of SIGUSR1: read %zd, of SIGUSR1 %d\n", size, info.ssi_signo == SIGUSR1);
  int id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600);
  union semun argument;
  argument.val = 1;
  int result = semctl(id, 0, SETVAL, argument);
  printf("semctl SETVAL of 1: %d, GETVAL %d\n", result, semctl(id, 0, GETVAL));
  semctl(id, 0, IPC_RMID);
  return 0;
}
