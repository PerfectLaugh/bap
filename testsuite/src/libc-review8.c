// What Linux does that a fourth review found the machine didn't, each in a process of its own, with an alarm that ends what would hang
// (testLinuxRaises):
//   buffers: a buffer that isn't there is EFAULT, of what doesn't happen then, and a read into one that ends early reads what fits of a
//     file and nothing of a pipe.
//   ioctls: FIONREAD, FIONBIO and FIOCLEX of any file.
//   order: of a descriptor that isn't there, EBADF before what its buffer is.
//   names: a name of more than 255 bytes, and a path of 4096 or more, are ENAMETOOLONG.
//   e2big: execve of arguments of more than it takes is E2BIG, to the program that called it.
//   search: stat, readlink, chdir and O_TMPFILE go by the permissions of the directories that they look in.
//   removed: the *at calls of the descriptor of a directory that was removed.
//   utimes: what inotify says of utimensat of both times, of one and of the other.
//   mqattr: mq_setattr of one struct for the new and the old.
//   limits: a resource or a who that there isn't is EINVAL, and so is a priority that a policy doesn't take.
//   exits: what a process that exits held it holds no more: inotify hears the close of what it wrote, and a memfd that it mapped may be
//     sealed.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <mqueue.h>
#include <sched.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#ifndef MFD_ALLOW_SEALING
#define MFD_ALLOW_SEALING 2
#endif
#ifndef F_ADD_SEALS
#define F_ADD_SEALS 1033
#define F_SEAL_WRITE 8
#endif

static char *self;

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

static const char *error(long result) { return result >= 0 ? "ok" : strerror(errno); }

static void buffers(void) {
  int fd = open(self, O_RDONLY);
  long result = syscall(SYS_read, fd, 0, 10);
  printf("buffers: read of a file to NULL %s at %ld, ", error(result), (long)lseek(fd, 0, SEEK_CUR));
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "hello", 5);
  result = syscall(SYS_read, pipes[0], 0, 5);
  int left = -1;
  ioctl(pipes[0], FIONREAD, &left);
  printf("of a pipe %s with %d left, ", error(result), left);
  int before = dup(0);
  close(before);
  result = syscall(SYS_pipe2, 0, 0);
  int after = dup(0);
  printf("pipe2(NULL) %s making nothing %d, ", error(result), after == before);
  printf("stat %s, ", error(syscall(SYS_newfstatat, AT_FDCWD, self, 0, 0)));
  printf("clock_gettime %s, ", error(syscall(SYS_clock_gettime, 0, 0)));
  printf("uname %s, ", error(syscall(SYS_uname, 0)));
  printf("getcwd %s\n", error(syscall(SYS_getcwd, 0, 100)));
  char *memory = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  munmap(memory + 4096, 4096);
  lseek(fd, 0, SEEK_SET);
  result = read(fd, memory + 4086, 100);
  printf("buffers: a read of a file into a buffer that ends early %ld at %ld, ", result, (long)lseek(fd, 0, SEEK_CUR));
  write(pipes[1], "0123456789abcdefghij", 20);
  result = read(pipes[0], memory + 4086, 20);
  ioctl(pipes[0], FIONREAD, &left);
  printf("of a pipe %s with %d left\n", error(result), left);
}

static void ioctls(void) {
  int pipes[2];
  pipe(pipes);
  write(pipes[1], "hello", 5);
  int count = -1;
  long result = ioctl(pipes[0], FIONREAD, &count);
  printf("ioctls: FIONREAD of a pipe %s %d, ", error(result), count);
  int on = 1;
  result = ioctl(pipes[0], FIONBIO, &on);
  printf("FIONBIO %s nonblocking %d, ", error(result), (fcntl(pipes[0], F_GETFL) & O_NONBLOCK) != 0);
  int fd = open(self, O_RDONLY);
  struct stat status;
  fstat(fd, &status);
  lseek(fd, 100, SEEK_SET);
  result = ioctl(fd, FIONREAD, &count);
  printf("FIONREAD of a file %s of what is left %d, ", error(result), count == status.st_size - 100);
  result = ioctl(fd, FIOCLEX);
  printf("FIOCLEX %s %d, ", error(result), fcntl(fd, F_GETFD));
  result = ioctl(fd, FIONCLEX);
  printf("FIONCLEX %s %d\n", error(result), fcntl(fd, F_GETFD));
}

static void order(void) {
  printf("order: read of no descriptor to what isn't there %s\n", error(syscall(SYS_read, -1, (void *)0xffffffffffff0000UL, 10)));
}

static void names(void) {
  char name[300];
  memset(name, 'a', 299);
  name[299] = 0;
  printf("names: of 299 bytes %s, ", error(open(name, O_CREAT | O_WRONLY, 0644)));
  static char path[5000];
  for (int index = 0; index < 4999; index++) path[index] = index % 2 ? '/' : 'b';
  path[4999] = 0;
  printf("a path of 4999 bytes %s\n", error(open(path, O_RDONLY)));
}

static void e2big(void) {
  size_t size = 200 * 1024;
  char *big = malloc(size + 1);
  memset(big, 'x', size);
  big[size] = 0;
  char *arguments[] = {self, "executed", big, 0};
  execve(self, arguments, 0);
  printf("e2big: of an argument of 200 KiB %s, ", errno == E2BIG ? "E2BIG" : strerror(errno));
  char *many[40];
  char *piece = malloc(100001);
  memset(piece, 'y', 100000);
  piece[100000] = 0;
  many[0] = self;
  many[1] = "executed";
  for (int index = 2; index < 39; index++) many[index] = piece;
  many[39] = 0;
  execve(self, many, 0);
  printf("of 3.8 MB of them %s\n", errno == E2BIG ? "E2BIG" : strerror(errno));
}

static void search(void) {
  mkdir("r8-closed", 0755);
  close(creat("r8-closed/file", 0644));
  symlink("file", "r8-closed/link");
  mkdir("r8-closed/inner", 0755);
  chmod("r8-closed", 0600);
  struct stat status;
  printf("search: stat in what may not be searched %s, ", error(stat("r8-closed/file", &status)));
  char target[16];
  printf("readlink %s, ", error(readlink("r8-closed/link", target, sizeof target)));
  printf("chdir %s, ", error(chdir("r8-closed/inner")));
  chmod("r8-closed", 0755);
  mkdir("r8-readonly", 0555);
  printf("O_TMPFILE where it may not write %s\n", error(open("r8-readonly", O_TMPFILE | O_RDWR, 0600)));
  chmod("r8-readonly", 0755);
  rmdir("r8-readonly");
  unlink("r8-closed/link");
  unlink("r8-closed/file");
  rmdir("r8-closed/inner");
  rmdir("r8-closed");
}

static void removed(void) {
  mkdir("r8-gone", 0755);
  int fd = open("r8-gone", O_RDONLY | O_DIRECTORY);
  rmdir("r8-gone");
  printf("removed: openat O_CREAT %s, ", error(openat(fd, "x", O_CREAT | O_WRONLY, 0644)));
  printf("mkdirat %s, ", error(mkdirat(fd, "y", 0755)));
  struct stat status;
  printf("fstatat . %s, ", error(fstatat(fd, ".", &status, 0)));
  printf(".. %s\n", error(fstatat(fd, "..", &status, 0)));
}

static void times(void) {
  close(creat("r8-times", 0644));
  int notify = inotify_init1(IN_NONBLOCK);
  inotify_add_watch(notify, "r8-times", IN_ATTRIB | IN_MODIFY | IN_ACCESS);
  struct timespec both[2] = {{1, 0}, {2, 0}};
  struct timespec modified[2] = {{0, UTIME_OMIT}, {3, 0}};
  struct timespec accessed[2] = {{4, 0}, {0, UTIME_OMIT}};
  struct timespec *given[] = {both, modified, accessed};
  printf("utimes:");
  for (int index = 0; index < 3; index++) {
    utimensat(AT_FDCWD, "r8-times", given[index], 0);
    char buffer[256];
    ssize_t size = read(notify, buffer, sizeof buffer);
    printf(" %#x", size > 0 ? ((struct inotify_event *)buffer)->mask : 0);
  }
  printf("\n");
  unlink("r8-times");
}

static void mqAttributes(void) {
  struct mq_attr attributes = {0, 4, 16, 0};
  mq_unlink("/r8queue");
  mqd_t queue = mq_open("/r8queue", O_CREAT | O_RDWR, 0600, &attributes);
  if (queue == (mqd_t)-1) {
    printf("mqattr: no queue\n");
    return;
  }
  struct mq_attr both = {O_NONBLOCK, 0, 0, 0};
  long result = syscall(SYS_mq_getsetattr, queue, &both, &both);
  struct mq_attr now;
  mq_getattr(queue, &now);
  printf("mqattr: of one struct %s, the old flags %ld, nonblocking now %d\n", error(result), both.mq_flags,
         (now.mq_flags & O_NONBLOCK) != 0);
  mq_close(queue);
  mq_unlink("/r8queue");
}

static void limits(void) {
  struct rlimit limit;
  printf("limits: getrlimit of 16 %s, ", error(syscall(SYS_getrlimit, 16, &limit)));
  printf("setrlimit of 16 %s, ", error(syscall(SYS_setrlimit, 16, &limit)));
  struct rusage usage;
  printf("getrusage of 5 %s, ", error(syscall(SYS_getrusage, 5, &usage)));
  struct sched_param parameter = {5};
  printf("SCHED_OTHER of 5 %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_OTHER, &parameter)));
  printf("of no parameter %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_OTHER, 0)));
  parameter.sched_priority = 0;
  printf("SCHED_FIFO of 0 %s, ", error(syscall(SYS_sched_setscheduler, 0, SCHED_FIFO, &parameter)));
  parameter.sched_priority = 50;
  printf("of 50 by a user %s\n", error(syscall(SYS_sched_setscheduler, 0, SCHED_FIFO, &parameter)));
}

static void exits(void) {
  close(creat("r8-written", 0644));
  int notify = inotify_init1(IN_NONBLOCK);
  inotify_add_watch(notify, "r8-written", IN_CLOSE_WRITE);
  pid_t child = fork();
  if (child == 0) {
    int fd = open("r8-written", O_WRONLY);
    write(fd, "x", 1);
    _exit(0);
  }
  waitpid(child, 0, 0);
  char buffer[256];
  ssize_t size = read(notify, buffer, sizeof buffer);
  printf("exits: inotify hears the close of what exited %d, ", size > 0 && (((struct inotify_event *)buffer)->mask & IN_CLOSE_WRITE));
  unlink("r8-written");
  int memory = (int)syscall(SYS_memfd_create, "r8", MFD_ALLOW_SEALING);
  ftruncate(memory, 4096);
  child = fork();
  if (child == 0) {
    mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, memory, 0);
    _exit(0);
  }
  waitpid(child, 0, 0);
  printf("a memfd that it mapped is sealed %s\n", error(fcntl(memory, F_ADD_SEALS, F_SEAL_WRITE)));
}

int main(int count, char **arguments) {
  self = arguments[0];
  setvbuf(stdout, 0, _IONBF, 0);
  // What an execve that should have failed ran.
  if (count > 1 && strcmp(arguments[1], "executed") == 0) {
    printf("executed\n");
    return 0;
  }
  // A directory of its own to work in, as the user that it is then.
  mkdir("r8-work", 0755);
  chown("r8-work", 1000, 1000);
  chdir("r8-work");
  setgid(1000);
  setuid(1000);
  // Its own path, from where it works.
  if (self[0] != '/') {
    static char path[4096];
    snprintf(path, sizeof path, "../%s", self);
    self = path;
  }
  part("buffers", buffers);
  part("ioctls", ioctls);
  part("order", order);
  part("names", names);
  part("e2big", e2big);
  part("search", search);
  part("removed", removed);
  part("utimes", times);
  part("mqattr", mqAttributes);
  part("limits", limits);
  part("exits", exits);
  chdir("..");
  rmdir("r8-work");
  printf("done\n");
  return 0;
}
