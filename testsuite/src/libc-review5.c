// What Linux does that a third review found the machine didn't, each in a process of its own, as a user other than root, with an alarm
// that ends what would hang (testLinuxRaises):
//   perms: open, creat, mkdir, unlink, rename, link, symlink and truncate are checked against the permissions of the file and its directory.
//   counts: writev of more vectors than UIO_MAXIOV is EINVAL, and a read of /dev/zero and getrandom of more than there is room for give
//     what fits before the end of the memory.
//   shmat: at an address that is mapped is EINVAL, of SHM_REMAP it replaces it.
//   readdir: unlinking what readdir gives, all of it is gone.
//   inotify: a file that is unlinked and still open is deleted when it is closed.
//   startstack: field 28 of /proc/self/stat is just below argv.
//   copyrange: copy_file_range of a file to its end, of more than there is, copies what there is.
//   utime: utimensat of a file of another user.
//   chown: of -1 and -1 changes nothing and is allowed.
//   comm: PR_SET_NAME of a thread names only that thread.
//   tracer: /proc/PID/status of a tracee has its tracer.
//   statx: has the device that stat has.
//   cwd: a working directory that was removed is there while it is the working directory.
//   msgsnd: a queue of 10 bytes takes 10 messages of none.
//   sempid: of a SEM_UNDO undone at exit is of the process that exited.
//   mqnotify: a registration goes when its process exits, and stays when a receiver that waits takes the message.
//   names: names are bytes, not text.
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <mqueue.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/msg.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/random.h>
#include <sys/sem.h>
#include <sys/shm.h>
#include <sys/stat.h>
#include <sys/sysmacros.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static char **arguments;

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

static const char *error(int result) { return result >= 0 ? "ok" : errno == EACCES ? "EACCES" : errno == EPERM ? "EPERM" : strerror(errno); }

static void perms(void) {
  close(creat("r5-none", 0));
  mkdir("r5-dir", 0755);
  close(creat("r5-dir/inside", 0644));
  chmod("r5-dir", 0555);
  printf("perms: open of mode 0 %s, ", error(open("r5-none", O_RDONLY)));
  printf("truncate %s, ", error(truncate("r5-none", 0)));
  printf("creat in 555 %s, ", error(open("r5-dir/new", O_CREAT | O_WRONLY, 0644)));
  printf("mkdir %s, ", error(mkdir("r5-dir/sub", 0755)));
  printf("unlink %s, ", error(unlink("r5-dir/inside")));
  printf("rename %s, ", error(rename("r5-dir/inside", "r5-out")));
  printf("link %s, ", error(link("r5-none", "r5-dir/linked")));
  printf("symlink %s\n", error(symlink("x", "r5-dir/sym")));
  chmod("r5-dir", 0755);
  unlink("r5-dir/inside");
  rmdir("r5-dir");
  unlink("r5-none");
}

static void counts(void) {
  struct iovec vector[1100];
  for (int index = 0; index < 1100; index++) vector[index] = (struct iovec){"", 0};
  ssize_t result = writev(1, vector, 1025);
  printf("counts: writev of 1025 %zd %s, ", result, result < 0 && errno == EINVAL ? "EINVAL" : "");
  result = syscall(SYS_writev, 1, vector, -1L);
  printf("of -1 %zd %s, ", result, result < 0 && errno == EINVAL ? "EINVAL" : "");
  char *memory = mmap(0, 3 * 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  munmap(memory + 2 * 4096, 4096);
  int zero = open("/dev/zero", O_RDONLY);
  result = read(zero, memory, 1UL << 48);
  printf("read of /dev/zero of 2^48 %zd %s, ", result, result < 0 ? strerror(errno) : "");
  printf("of 2^20 %zd, ", read(zero, memory, 1UL << 20));
  printf("getrandom of 2^40 %zd\n", getrandom(memory, 1UL << 40, 0));
}

static void shmatMapped(void) {
  int id = shmget(IPC_PRIVATE, 4096, IPC_CREAT | 0600);
  char *mapped = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  strcpy(mapped, "precious");
  void *result = shmat(id, mapped, 0);
  printf("shmat: where it is mapped %s, it has %s, ", result == (void *)-1 && errno == EINVAL ? "EINVAL" : "attached", mapped);
  result = shmat(id, mapped, SHM_REMAP);
  printf("of SHM_REMAP %s, ", result == mapped ? "attached" : "not");
  result = shmat(id, 0, SHM_REMAP);
  printf("of SHM_REMAP and no address %s\n", result == (void *)-1 && errno == EINVAL ? "EINVAL" : "attached");
  shmctl(id, IPC_RMID, 0);
}

static void readdirUnlink(void) {
  mkdir("r5-many", 0755);
  char name[64];
  for (int index = 0; index < 3000; index++) {
    snprintf(name, sizeof name, "r5-many/file%04d", index);
    close(creat(name, 0644));
  }
  chdir("r5-many");
  DIR *directory = opendir(".");
  struct dirent *entry;
  int removed = 0;
  while ((entry = readdir(directory)))
    if (entry->d_name[0] != '.' && unlink(entry->d_name) == 0) removed++;
  closedir(directory);
  chdir("..");
  printf("readdir: unlinked %d, rmdir %s\n", removed, error(rmdir("r5-many")));
}

static void inotifyOpen(void) {
  int file = open("r5-watched", O_CREAT | O_WRONLY, 0644);
  int notify = inotify_init1(IN_NONBLOCK);
  inotify_add_watch(notify, "r5-watched", IN_ATTRIB | IN_CLOSE_WRITE | IN_DELETE_SELF | IN_IGNORED);
  unlink("r5-watched");
  char buffer[4096];
  printf("inotify: at unlink");
  for (int round = 0; round < 2; round++) {
    ssize_t size = read(notify, buffer, sizeof buffer);
    for (char *at = buffer; size > 0 && at < buffer + size;) {
      struct inotify_event *event = (struct inotify_event *)at;
      printf(" %s", event->mask & IN_ATTRIB ? "ATTRIB" : event->mask & IN_CLOSE_WRITE ? "CLOSE_WRITE"
                    : event->mask & IN_DELETE_SELF ? "DELETE_SELF" : event->mask & IN_IGNORED ? "IGNORED" : "other");
      at += sizeof *event + event->len;
    }
    if (round == 0) {
      close(file);
      printf(", at close");
    }
  }
  printf("\n");
}

static void startStack(void) {
  char text[1024];
  int fd = open("/proc/self/stat", O_RDONLY);
  ssize_t size = read(fd, text, sizeof text - 1);
  text[size > 0 ? size : 0] = 0;
  char *at = strrchr(text, ')') + 2;
  unsigned long field = 0;
  for (int index = 3; index <= 28; index++) {
    if (index == 28) field = strtoul(at, 0, 10);
    at = strchr(at, ' ') + 1;
  }
  unsigned long argv = (unsigned long)arguments;
  printf("startstack: just below argv %d\n", field <= argv && argv - field < 256);
}

static void copyRange(void) {
  int fd = open("r5-copy", O_CREAT | O_RDWR | O_TRUNC, 0644);
  write(fd, "0123456789", 10);
  loff_t from = 0, to = 10;
  printf("copyrange: of 100 from 0 to 10 of 10 bytes %zd\n", copy_file_range(fd, &from, fd, &to, 100, 0));
  unlink("r5-copy");
}

// A directory of another user: one that root gave away before it was root no more, or, where it couldn't, as on a host that isn't
// root, one of the system.
static const char *others(void) {
  struct stat status;
  if (stat("r5-owned", &status) == 0 && status.st_uid != getuid()) return "r5-owned";
  return "/usr";
}

static void utime(void) {
  struct timespec times[2] = {{1, 0}, {1, 0}};
  printf("utime: of another's at 1 %s, ", error(utimensat(AT_FDCWD, others(), times, 0)));
  printf("now %s, ", error(utimensat(AT_FDCWD, others(), 0, 0)));
  struct timespec omit[2] = {{0, UTIME_OMIT}, {0, UTIME_OMIT}};
  printf("of UTIME_OMIT %s\n", error(utimensat(AT_FDCWD, others(), omit, 0)));
}

static void chownNone(void) { printf("chown: of another's to -1 -1 %s\n", error(chown(others(), -1, -1))); }

static void *namer(void *unused) {
  (void)unused;
  prctl(PR_SET_NAME, "worker");
  return 0;
}

static void comm(void) {
  prctl(PR_SET_NAME, "main");
  pthread_t thread;
  pthread_create(&thread, 0, namer, 0);
  pthread_join(thread, 0);
  char name[32] = {0};
  prctl(PR_GET_NAME, name);
  char text[32] = {0};
  int fd = open("/proc/self/comm", O_RDONLY);
  read(fd, text, sizeof text - 1);
  printf("comm: of the main thread %s, /proc/self/comm %s", name, text);
}

static void tracer(void) {
  pid_t child = fork();
  if (child == 0) {
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    _exit(0);
  }
  waitpid(child, 0, 0);
  char path[64], text[4096] = {0};
  snprintf(path, sizeof path, "/proc/%d/status", child);
  int fd = open(path, O_RDONLY);
  read(fd, text, sizeof text - 1);
  char *at = strstr(text, "TracerPid:");
  printf("tracer: TracerPid is the tracer %d\n", at && atoi(at + 10) == getpid());
  kill(child, SIGKILL);
  waitpid(child, 0, 0);
}

static void statxDevice(void) {
  struct stat status;
  struct statx extended;
  stat("/proc/self/exe", &status);
  statx(AT_FDCWD, "/proc/self/exe", 0, STATX_BASIC_STATS, &extended);
  printf("statx: the device of stat %d\n", makedev(extended.stx_dev_major, extended.stx_dev_minor) == status.st_dev);
}

static void removedCwd(void) {
  mkdir("r5-gone", 0755);
  chdir("r5-gone");
  rmdir("../r5-gone");
  for (int index = 0; index < 1000; index++) close(open("/dev/null", O_RDONLY));
  struct stat status;
  printf("cwd: stat of . %s, ", error(stat(".", &status)));
  printf("open of . %s\n", error(open(".", O_RDONLY)));
}

static void messageCount(void) {
  int id = msgget(IPC_PRIVATE, IPC_CREAT | 0600);
  struct msqid_ds data;
  msgctl(id, IPC_STAT, &data);
  data.msg_qbytes = 10;
  msgctl(id, IPC_SET, &data);
  struct { long type; char text[1]; } message = {1, {0}};
  int sent = 0;
  while (sent < 20 && msgsnd(id, &message, 0, IPC_NOWAIT) == 0) sent++;
  printf("msgsnd: of none to 10 bytes %d %s\n", sent, errno == EAGAIN ? "EAGAIN" : "");
  msgctl(id, IPC_RMID, 0);
}

static void semPid(void) {
  int id = semget(IPC_PRIVATE, 1, IPC_CREAT | 0600);
  int done[2], go[2];
  pipe(done);
  pipe(go);
  pid_t child = fork();
  if (child == 0) {
    struct sembuf operation = {0, 1, SEM_UNDO};
    semop(id, &operation, 1);
    write(done[1], "d", 1);
    char got;
    read(go[0], &got, 1);
    _exit(0);
  }
  char got;
  read(done[0], &got, 1);
  // The last to operate is the parent, until the child's undo at its exit.
  struct sembuf operation = {0, 1, 0};
  semop(id, &operation, 1);
  write(go[1], "g", 1);
  waitpid(child, 0, 0);
  printf("sempid: after the undo at exit, of the child %d\n", semctl(id, 0, GETPID) == child);
  semctl(id, 0, IPC_RMID);
}

static volatile int notified;
static void onNotify(int signal) { (void)signal; notified++; }

static void mqNotify(void) {
  struct mq_attr attributes = {0, 4, 16, 0};
  mq_unlink("/r5queue");
  mqd_t queue = mq_open("/r5queue", O_CREAT | O_RDWR, 0600, &attributes);
  if (queue == (mqd_t)-1) {
    printf("mqnotify: no queue\n");
    return;
  }
  struct sigevent event = {0};
  event.sigev_notify = SIGEV_SIGNAL;
  event.sigev_signo = SIGUSR1;
  signal(SIGUSR1, onNotify);
  pid_t child = fork();
  if (child == 0) {
    mq_notify(queue, &event);
    _exit(0);
  }
  waitpid(child, 0, 0);
  printf("mqnotify: after its process exits %s, ", error(mq_notify(queue, &event)));
  child = fork();
  if (child == 0) {
    char buffer[16];
    mq_receive(queue, buffer, sizeof buffer, 0);
    _exit(0);
  }
  usleep(200000);
  mq_send(queue, "x", 1, 0);
  waitpid(child, 0, 0);
  int again = mq_notify(queue, &event);
  printf("a receiver that waits took it: notified %d, registered still %s\n", notified, again < 0 && errno == EBUSY ? "EBUSY" : "no");
  mq_close(queue);
  mq_unlink("/r5queue");
}

static void names(void) {
  mkdir("r5-names", 0755);
  close(creat("r5-names/\xe9", 0644));
  close(creat("r5-names/\xc3\xa9", 0644));
  mkdir("r5-names/\xc3\xa9-dir", 0755);
  int inner = open("r5-names/\xc3\xa9-dir/\xff", O_CREAT | O_WRONLY, 0644);
  DIR *directory = opendir("r5-names");
  struct dirent *entry;
  int count = 0, latin = 0;
  while ((entry = readdir(directory))) {
    if (entry->d_name[0] == '.') continue;
    count++;
    if (strcmp(entry->d_name, "\xe9") == 0) latin = 1;
  }
  closedir(directory);
  printf("names: entries %d, of the byte e9 %d, inside a directory of text %s\n", count, latin, inner >= 0 ? "made" : "not");
  unlink("r5-names/\xc3\xa9-dir/\xff");
  rmdir("r5-names/\xc3\xa9-dir");
  unlink("r5-names/\xe9");
  unlink("r5-names/\xc3\xa9");
  rmdir("r5-names");
}

int main(int count, char **given) {
  (void)count;
  arguments = given;
  setvbuf(stdout, 0, _IONBF, 0);
  part("startstack", startStack);
  part("comm", comm);
  part("tracer", tracer);
  // A directory of its own to work in, as the user that it is then.
  mkdir("r5-work", 0755);
  chown("r5-work", 1000, 1000);
  chdir("r5-work");
  mkdir("r5-owned", 0755);
  chown("r5-owned", 65534, 65534);
  setgid(1000);
  setuid(1000);
  part("perms", perms);
  part("counts", counts);
  part("shmat", shmatMapped);
  part("readdir", readdirUnlink);
  part("inotify", inotifyOpen);
  part("copyrange", copyRange);
  part("utime", utime);
  part("chown", chownNone);
  part("statx", statxDevice);
  part("cwd", removedCwd);
  part("msgsnd", messageCount);
  part("sempid", semPid);
  part("mqnotify", mqNotify);
  part("names", names);
  rmdir("r5-owned");
  chdir("..");
  rmdir("r5-work");
  printf("done\n");
  return 0;
}
