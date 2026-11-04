// What waits on a SysV object that is taken away hears EIDRM, and a send that waits for room goes on when IPC_SET makes some.
#define _GNU_SOURCE
#include <errno.h>
#include <time.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long a, long b) {
  char line[96];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[2] = {a, b};
  for (int index = 0; index < 2; index++) {
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

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

#define IPC_64_ (sizeof(long) == 8 ? 0 : 0x100)
#define WIDE (sizeof(long) == 8)

static void pause_(void) {
  struct timespec pause = {0, 20000000};
  nanosleep(&pause, 0);
}

struct message { long type; char text[16]; };

int main(void) {
  long set = call(SYS_semget, 0, 1, 01000 | 0600, 0, 0);
  int child = fork();
  if (child == 0) {
    short take[3] = {0, -1, 0};
    say("semop of a removed set", call(SYS_semop, set, (long)take, 1, 0, 0), 0);
    _exit(0);
  }
  pause_();
  call(SYS_semctl, set, 0, 0 | IPC_64_, 0, 0);
  waitpid(child, 0, 0);

  long queue = call(SYS_msgget, 0, 01000 | 0600, 0, 0, 0);
  child = fork();
  if (child == 0) {
    struct message got;
    say("msgrcv of a removed queue", call(SYS_msgrcv, queue, (long)&got, 16, 0, 0), 0);
    _exit(0);
  }
  pause_();
  call(SYS_msgctl, queue, 0 | IPC_64_, 0, 0, 0);
  waitpid(child, 0, 0);

  // A queue of 8 bytes, full, and a send that waits until it holds 16.
  queue = call(SYS_msgget, 0, 01000 | 0600, 0, 0, 0);
  unsigned char state[256];
  call(SYS_msgctl, queue, 2 | IPC_64_, (long)state, 0, 0);
  int at = (WIDE ? 48 : 36) + (WIDE ? 40 : 32);
  *(unsigned long *)(state + at) = 8;
  say("smaller", call(SYS_msgctl, queue, 1 | IPC_64_, (long)state, 0, 0), 0);
  struct message full = {1, "12345678"};
  call(SYS_msgsnd, queue, (long)&full, 8, 0, 0);
  child = fork();
  if (child == 0) {
    struct message more = {2, "more"};
    say("sent when there was room", call(SYS_msgsnd, queue, (long)&more, 4, 0, 0), 0);
    _exit(0);
  }
  pause_();
  *(unsigned long *)(state + at) = 16;
  say("larger", call(SYS_msgctl, queue, 1 | IPC_64_, (long)state, 0, 0), 0);
  waitpid(child, 0, 0);
  call(SYS_msgctl, queue, 0 | IPC_64_, 0, 0, 0);
  return 0;
}
