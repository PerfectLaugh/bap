// SysV IPC counts what there is: a segment that a child had attached as it exited is attached once, and goes when its parent detaches
// it after IPC_RMID; GETNCNT and GETZCNT count the processes that wait in semop for a semaphore to grow or to be 0, and not once they no
// longer wait, as they get it or are killed.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <time.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int digit = 0;
    do { digits[digit++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (digit) line[n++] = digits[--digit];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d) {
  long result = syscall(number, a, b, c, d);
  return result < 0 ? -errno : result;
}

#define IPC_PRIVATE_ 0
#define IPC_CREAT_ 01000
#define IPC_RMID_ 0
#define IPC_STAT_ 2
#define GETVAL_ 12
#define GETNCNT_ 14
#define GETZCNT_ 15
#define SETVAL_ 16

struct sembuf_ { unsigned short num; short op; short flg; };

static long shmctl_(long id, long command, void *buffer) { return call(SYS_shmctl, id, command, (long)buffer, 0); }
static long semctl_(long id, long number, long command, long value) { return call(SYS_semctl, id, number, command, value); }
static long semop_(long id, struct sembuf_ *operation) { return call(SYS_semop, id, (long)operation, 1, 0); }

// How many have the segment attached, of struct shmid64_ds, or why there is none.
static long attached(long id) {
  unsigned char bytes[256];
  long result = shmctl_(id, IPC_STAT_, bytes);
  if (result < 0) return result;
  long value = 0;
  for (int index = 7; index >= 0; index--) value = value * 256 + bytes[88 + index];
  return value;
}

// What GETNCNT or GETZCNT says once it is what is wanted, or after a second.
static long counted(long set, long number, long command, long wanted) {
  long count = 0;
  for (int tries = 0; tries < 200; tries++) {
    count = semctl_(set, number, command, 0);
    if (count == wanted) break;
    struct timespec pause = {0, 5000000};
    nanosleep(&pause, 0);
  }
  return count;
}

// A child that waits in semop for the operation, and exits once it is done.
static int waiter(long set, unsigned short number, short op) {
  int child = fork();
  if (child == 0) {
    struct sembuf_ operation = {number, op, 0};
    _exit(semop_(set, &operation) == 0 ? 0 : 1);
  }
  return child;
}

static long reaped(int child) {
  int status = 0;
  waitpid(child, &status, 0);
  return status;
}

int main(void) {
  // A segment that a child had attached as it exited.
  long id = call(SYS_shmget, IPC_PRIVATE_, 4096, IPC_CREAT_ | 0600, 0);
  say("shmget", 1, id >= 0, 0);
  char *shared = (char *)call(SYS_shmat, id, 0, 0, 0);
  say("attached", 1, attached(id), 0);
  int child = fork();
  if (child == 0) _exit(shared[0]);
  say("child exited", 2, reaped(child), attached(id));
  say("rmid", 2, shmctl_(id, IPC_RMID_, 0), attached(id));
  say("shmdt", 2, call(SYS_shmdt, (long)shared, 0, 0, 0), attached(id) == -EINVAL || attached(id) == -EIDRM);

  // Waiting for a semaphore to grow, and for one to be 0.
  long set = call(SYS_semget, IPC_PRIVATE_, 2, IPC_CREAT_ | 0600, 0);
  say("semget", 1, set >= 0, 0);
  child = waiter(set, 0, -1);
  say("ncnt", 2, counted(set, 0, GETNCNT_, 1), semctl_(set, 0, GETZCNT_, 0));
  struct sembuf_ give = {0, 1, 0};
  say("given", 2, semop_(set, &give), semctl_(set, 0, GETNCNT_, 0));
  say("taker", 2, reaped(child), semctl_(set, 0, GETVAL_, 0));
  semctl_(set, 1, SETVAL_, 1);
  child = waiter(set, 1, 0);
  say("zcnt", 2, counted(set, 1, GETZCNT_, 1), semctl_(set, 1, GETNCNT_, 0));
  say("zeroed", 2, semctl_(set, 1, SETVAL_, 0), semctl_(set, 1, GETZCNT_, 0));
  say("zero waiter", 1, reaped(child), 0);

  // One that is killed as it waits waits no longer.
  child = waiter(set, 0, -1);
  say("waits", 1, counted(set, 0, GETNCNT_, 1), 0);
  kill(child, SIGKILL);
  say("killed", 2, reaped(child) == SIGKILL, semctl_(set, 0, GETNCNT_, 0));
  say("no such", 2, semctl_(set, 2, GETNCNT_, 0), semctl_(set, 2, GETZCNT_, 0));
  say("sem rmid", 1, semctl_(set, 0, IPC_RMID_, 0), 0);
  return 0;
}
