// The smaller of what a third review found, each in a process of its own (testLinuxRaises):
//   emptypath: fstatat of "" with AT_EMPTY_PATH of AT_FDCWD is of the working directory.
//   msgcopy: msgrcv of MSG_COPY past what there is is ENOMSG.
//   rwfappend: pwritev2 of RWF_APPEND writes at the end.
//   scheduler: sched_setscheduler keeps the policy that sched_getscheduler says.
//   dontunmap: mremap of MREMAP_DONTUNMAP of a mapping of a file.
//   trusted: an attribute of trusted. is root's.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sched.h>
#include <stdio.h>
#include <string.h>
#include <sys/ipc.h>
#include <sys/mman.h>
#include <sys/msg.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <unistd.h>

#ifndef MREMAP_DONTUNMAP
#define MREMAP_DONTUNMAP 4
#endif
#ifndef MSG_COPY
#define MSG_COPY 040000
#endif
#ifndef RWF_APPEND
#define RWF_APPEND 0x10
#endif

static void part(void (*run)(void)) {
  pid_t child = fork();
  if (child == 0) {
    alarm(5);
    run();
    _exit(0);
  }
  waitpid(child, 0, 0);
}

static const char *error(long result) { return result >= 0 ? "ok" : strerror(errno); }

static void emptyPath(void) {
  struct stat here, dot;
  long result = fstatat(AT_FDCWD, "", &here, AT_EMPTY_PATH);
  stat(".", &dot);
  printf("emptypath: %s, of the working directory %d\n", error(result), result == 0 && here.st_ino == dot.st_ino);
}

static void messageCopy(void) {
  int id = msgget(IPC_PRIVATE, IPC_CREAT | 0600);
  struct { long type; char text[4]; } message = {1, "abc"};
  msgsnd(id, &message, 4, 0);
  long result = msgrcv(id, &message, 4, 5, MSG_COPY | IPC_NOWAIT);
  printf("msgcopy: past what there is %s, ", result < 0 && errno == ENOMSG ? "ENOMSG" : error(result));
  result = msgrcv(id, &message, 4, -1, MSG_COPY | IPC_NOWAIT);
  printf("of -1 %s\n", result < 0 && errno == ENOMSG ? "ENOMSG" : error(result));
  msgctl(id, IPC_RMID, 0);
}

static void rwfAppend(void) {
  int fd = open("r7-file", O_CREAT | O_RDWR | O_TRUNC, 0644);
  write(fd, "abcd", 4);
  struct iovec vector = {"xy", 2};
  long result = pwritev2(fd, &vector, 1, 0, RWF_APPEND);
  char buffer[8] = {0};
  pread(fd, buffer, sizeof buffer - 1, 0);
  printf("rwfappend: %s, the file has %s\n", error(result), buffer);
  unlink("r7-file");
}

static void scheduler(void) {
  struct sched_param parameter = {0};
  // Of the calls themselves, as musl's functions of them say ENOSYS.
  long result = syscall(SYS_sched_setscheduler, 0, SCHED_BATCH, &parameter);
  printf("scheduler: of SCHED_BATCH %s, it is %ld\n", error(result), syscall(SYS_sched_getscheduler, 0));
}

static void dontUnmap(void) {
  int fd = open("r7-map", O_CREAT | O_RDWR | O_TRUNC, 0644);
  ftruncate(fd, 4096);
  char *mapped = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE, fd, 0);
  void *moved = mremap(mapped, 4096, 4096, MREMAP_MAYMOVE | MREMAP_DONTUNMAP);
  printf("dontunmap: of a file %s\n", moved == MAP_FAILED ? strerror(errno) : "moved");
  unlink("r7-map");
}

static void trusted(void) {
  close(open("r7-attr", O_CREAT | O_WRONLY, 0644));
  setgid(1000);
  setuid(1000);
  long result = setxattr("r7-attr", "trusted.x", "1", 1, 0);
  printf("trusted: of another than root %s\n", result < 0 && errno == EPERM ? "EPERM" : error(result));
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  part(emptyPath);
  part(messageCopy);
  part(rwfAppend);
  part(scheduler);
  part(dontUnmap);
  part(trusted);
  unlink("r7-attr");
  printf("done\n");
  return 0;
}
