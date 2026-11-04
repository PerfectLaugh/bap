// SysV IPC: a segment that a child shares and that lasts after IPC_RMID until it is detached, keys, semaphores that are changed all
// together or not at all, that wait for a child, that time out and that SEM_UNDO takes back, and message queues of types, that a
// receive waits on. It says what it found, the same on each target, by the calls of each or by ipc where that is what there is.
#define _GNU_SOURCE
#include <errno.h>
#include <time.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, int count, long a, long b, long c) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
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

static void sayText(const char *label, const char *text, long size) {
  char line[160];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  for (long index = 0; index < size; index++) line[n++] = text[index];
  line[n++] = '\n';
  write(1, line, n);
}

static long call(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

#define IPC_PRIVATE_ 0
#define IPC_CREAT_ 01000
#define IPC_EXCL_ 02000
#define IPC_NOWAIT_ 04000
#define IPC_RMID_ 0
#define IPC_STAT_ 2
#define SEM_UNDO_ 0x1000
#define GETPID_ 11
#define GETVAL_ 12
#define GETALL_ 13
#define SETVAL_ 16
#define MSG_NOERROR_ 010000
#define MSG_EXCEPT_ 020000
#define SHM_RDONLY_ 010000
#define WIDE (sizeof(long) == 8)
#define IPC_64_ (WIDE ? 0 : 0x100)

struct sembuf_ { unsigned short num; short op; short flg; };

#ifdef SYS_semop
static long shmget_(long key, long size, long flags) { return call(SYS_shmget, key, size, flags, 0, 0, 0); }
static long shmat_(long id, long address, long flags) { return call(SYS_shmat, id, address, flags, 0, 0, 0); }
static long shmdt_(long address) { return call(SYS_shmdt, address, 0, 0, 0, 0, 0); }
static long shmctl_(long id, long command, void *buffer) { return call(SYS_shmctl, id, command | IPC_64_, (long)buffer, 0, 0, 0); }
static long semget_(long key, long count, long flags) { return call(SYS_semget, key, count, flags, 0, 0, 0); }
static long semop_(long id, struct sembuf_ *operations, long count) { return call(SYS_semop, id, (long)operations, count, 0, 0, 0); }
static long semtimedop_(long id, struct sembuf_ *operations, long count, struct timespec *timeout) {
#ifdef SYS_semtimedop_time64
  long long wide[2] = {timeout->tv_sec, timeout->tv_nsec};
  return call(SYS_semtimedop_time64, id, (long)operations, count, (long)wide, 0, 0);
#else
  return call(SYS_semtimedop, id, (long)operations, count, (long)timeout, 0, 0);
#endif
}
static long semctl_(long id, long number, long command, long value) { return call(SYS_semctl, id, number, command | IPC_64_, value, 0, 0); }
static long msgget_(long key, long flags) { return call(SYS_msgget, key, flags, 0, 0, 0, 0); }
static long msgsnd_(long id, void *message, long size, long flags) { return call(SYS_msgsnd, id, (long)message, size, flags, 0, 0); }
static long msgrcv_(long id, void *message, long size, long type, long flags) { return call(SYS_msgrcv, id, (long)message, size, type, flags, 0); }
static long msgctl_(long id, long command, void *buffer) { return call(SYS_msgctl, id, command | IPC_64_, (long)buffer, 0, 0, 0); }
#else
static long shmget_(long key, long size, long flags) { return call(SYS_ipc, 23, key, size, flags, 0, 0); }
static long shmat_(long id, long address, long flags) {
  unsigned long at = 0;
  long result = call(SYS_ipc, 21, id, flags, (long)&at, address, 0);
  return result < 0 ? result : (long)at;
}
static long shmdt_(long address) { return call(SYS_ipc, 22, 0, 0, 0, address, 0); }
static long shmctl_(long id, long command, void *buffer) { return call(SYS_ipc, 24, id, command | IPC_64_, 0, (long)buffer, 0); }
static long semget_(long key, long count, long flags) { return call(SYS_ipc, 2, key, count, flags, 0, 0); }
static long semop_(long id, struct sembuf_ *operations, long count) { return call(SYS_ipc, 1, id, count, 0, (long)operations, 0); }
static long semtimedop_(long id, struct sembuf_ *operations, long count, struct timespec *timeout) {
  return call(SYS_ipc, 4, id, count, 0, (long)operations, (long)timeout);
}
static long semctl_(long id, long number, long command, long value) {
  long argument = value;
  return call(SYS_ipc, 3, id, number, command | IPC_64_, (long)&argument, 0);
}
static long msgget_(long key, long flags) { return call(SYS_ipc, 13, key, flags, 0, 0, 0); }
static long msgsnd_(long id, void *message, long size, long flags) { return call(SYS_ipc, 11, id, size, flags, (long)message, 0); }
static long msgrcv_(long id, void *message, long size, long type, long flags) {
  long kludge[2] = {(long)message, type};
  return call(SYS_ipc, 12, id, size, flags, (long)kludge, 0);
}
static long msgctl_(long id, long command, void *buffer) { return call(SYS_ipc, 14, id, command | IPC_64_, 0, (long)buffer, 0); }
#endif

static long field(const unsigned char *bytes, int offset, int size) {
  long value = 0;
  for (int index = size - 1; index >= 0; index--) value = value * 256 + bytes[offset + index];
  return value;
}

static void pause_(long milliseconds) {
  struct timespec pause = {0, milliseconds * 1000000};
  nanosleep(&pause, 0);
}

// Of struct shmid64_ds: its mode, size, creator, and how many have it attached.
static void segment(const char *label, long id) {
  unsigned char bytes[256];
  long result = shmctl_(id, IPC_STAT_, bytes);
  if (result < 0) { say(label, 1, result, 0, 0); return; }
  int perm = WIDE ? 48 : 36;
  say(label, 3, field(bytes, 20, 2), field(bytes, perm, WIDE ? 8 : 4), field(bytes, WIDE ? 88 : 72, WIDE ? 8 : 4));
  say(label, 1, field(bytes, WIDE ? 80 : 64, 4) == getpid(), 0, 0);
}

struct message { long type; char text[32]; };

static void receive(const char *label, long id, long size, long type, long flags) {
  struct message message;
  long got = msgrcv_(id, &message, size, type, flags);
  if (got < 0) { say(label, 1, got, 0, 0); return; }
  say(label, 2, got, message.type, 0);
  sayText(label, message.text, got);
}

int main(void) {
  // A segment, which a child has attached too.
  long id = shmget_(IPC_PRIVATE_, 10000, IPC_CREAT_ | 0600);
  say("shmget", 1, id >= 0, 0, 0);
  char *shared = (char *)shmat_(id, 0, 0);
  say("shmat", 1, (long)shared > 0, 0, 0);
  for (int index = 0; index < 6; index++) shared[index] = "hello"[index];
  segment("stat", id);
  int child = fork();
  if (child == 0) {
    sayText("child sees", shared, 5);
    for (int index = 0; index < 6; index++) shared[index] = "child"[index];
    shmdt_((long)shared);
    _exit(0);
  }
  waitpid(child, 0, 0);
  sayText("parent sees", shared, 5);
  segment("after the child", id);
  char *readOnly = (char *)shmat_(id, 0, SHM_RDONLY_);
  say("read only", 2, readOnly[0] == 'c', readOnly != shared, 0);
  segment("twice", id);
  say("unaligned", 1, shmat_(id, (long)shared + 1, 0), 0, 0);

  // Keys.
  long keyed = shmget_(0x5eed, 100, IPC_CREAT_ | 0644);
  say("by key", 3, shmget_(0x5eed, 100, 0) == keyed, shmget_(0x5eed, 100, IPC_CREAT_ | IPC_EXCL_), shmget_(0x5eed, 200, 0));
  say("no key", 1, shmget_(0x5eee, 1, 0), 0, 0);
  shmctl_(keyed, IPC_RMID_, 0);
  say("removed key", 1, shmget_(0x5eed, 100, 0), 0, 0);

  // Taken away while attached: it is there until it is detached.
  say("rmid", 1, shmctl_(id, IPC_RMID_, 0), 0, 0);
  segment("going", id);
  say("shmdt", 2, shmdt_((long)shared), shmdt_((long)readOnly), 0);
  segment("gone", id);
  say("shmdt again", 1, shmdt_((long)shared), 0, 0);

  // Semaphores.
  long set = semget_(IPC_PRIVATE_, 2, IPC_CREAT_ | 0600);
  say("semget", 1, set >= 0, 0, 0);
  say("setval", 2, semctl_(set, 0, SETVAL_, 1), semctl_(set, 0, GETVAL_, 0), 0);
  struct sembuf_ take = {0, -1, 0};
  say("take", 2, semop_(set, &take, 1), semctl_(set, 0, GETVAL_, 0), 0);
  struct sembuf_ none = {0, -1, IPC_NOWAIT_};
  say("none left", 1, semop_(set, &none, 1), 0, 0);
  struct sembuf_ both[2] = {{1, 1, 0}, {0, -1, IPC_NOWAIT_}};
  say("all or nothing", 2, semop_(set, both, 2), semctl_(set, 1, GETVAL_, 0), 0);
  struct sembuf_ wrong = {5, 1, 0};
  say("no such", 2, semop_(set, &wrong, 1), semctl_(set, 0, SETVAL_, 40000), 0);
  child = fork();
  if (child == 0) {
    pause_(20);
    say("child gives", 0, 0, 0, 0);
    struct sembuf_ give = {0, 1, 0};
    semop_(set, &give, 1);
    _exit(0);
  }
  say("waited", 1, semop_(set, &take, 1), 0, 0);
  waitpid(child, 0, 0);
  say("by the child", 1, semctl_(set, 0, GETPID_, 0) == child, 0, 0);
  struct timespec soon = {0, 10000000};
  say("timed out", 1, semtimedop_(set, &take, 1, &soon), 0, 0);
  child = fork();
  if (child == 0) {
    struct sembuf_ undone = {1, 5, SEM_UNDO_};
    semop_(set, &undone, 1);
    say("child had", 1, semctl_(set, 1, GETVAL_, 0), 0, 0);
    _exit(0);
  }
  waitpid(child, 0, 0);
  say("undone", 1, semctl_(set, 1, GETVAL_, 0), 0, 0);
  unsigned short values[2] = {9, 9};
  say("getall", 3, semctl_(set, 0, GETALL_, (long)values), values[0], values[1]);
  unsigned char bytes[256];
  semctl_(set, 0, IPC_STAT_, (long)bytes);
#ifdef __x86_64__
  say("nsems", 1, field(bytes, 80, 8), 0, 0);
#else
  say("nsems", 1, field(bytes, WIDE ? 64 : 52, WIDE ? 8 : 4), 0, 0);
#endif
  say("sem rmid", 2, semctl_(set, 0, IPC_RMID_, 0), semctl_(set, 0, GETVAL_, 0), 0);

  // Messages.
  long queue = msgget_(IPC_PRIVATE_, IPC_CREAT_ | 0600);
  say("msgget", 1, queue >= 0, 0, 0);
  struct message two = {2, "two"}, one = {1, "one"}, three = {3, "three"}, four = {4, "four"}, bad = {0, "bad"};
  say("send", 3, msgsnd_(queue, &two, 3, 0), msgsnd_(queue, &one, 3, 0), msgsnd_(queue, &three, 5, 0));
  say("send type 0", 1, msgsnd_(queue, &bad, 3, 0), 0, 0);
  msgctl_(queue, IPC_STAT_, bytes);
  int base = WIDE ? 48 + 24 : 36 + 24;
  say("held", 2, field(bytes, base, WIDE ? 8 : 4), field(bytes, base + (WIDE ? 8 : 4), WIDE ? 8 : 4), 0);
  receive("first", queue, 32, 0, 0);
  receive("lowest up to 2", queue, 32, -2, 0);
  msgsnd_(queue, &four, 4, 0);
  receive("not 3", queue, 32, 3, MSG_EXCEPT_);
  receive("too small", queue, 2, 0, 0);
  receive("cut", queue, 2, 0, MSG_NOERROR_);
  receive("empty", queue, 32, 0, IPC_NOWAIT_);
  child = fork();
  if (child == 0) {
    pause_(20);
    struct message late = {7, "late"};
    say("child sends", 0, 0, 0, 0);
    msgsnd_(queue, &late, 4, 0);
    _exit(0);
  }
  receive("waited", queue, 32, 7, 0);
  waitpid(child, 0, 0);
  say("msg rmid", 2, msgctl_(queue, IPC_RMID_, 0), msgsnd_(queue, &one, 3, 0), 0);
  return 0;
}
