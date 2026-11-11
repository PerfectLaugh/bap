// What Linux does with files and memory that a fifth review found the machine didn't, each in a process of its own (part), as user 1000
// in a directory of its own:
//   opath: what O_PATH opens may only be named: read, write, mmap, fchmod and ioctl are EBADF, O_TRUNC and O_CREAT are ignored, and it
//     opens a file that may not be read or written, and a link itself.
//   seals: O_TRUNC of a memfd whose size is sealed is EPERM.
//   partial: write, pwrite, writev, pwritev, pread and preadv of a buffer that ends early do what fits and say so.
//   devzero: mmap of /dev/zero is of zeros, private or shared, and of a pipe or a directory ENODEV.
//   pipe0: a write of nothing to a pipe that no one reads is 0, without SIGPIPE.
//   utimes: utimensat of /dev/null, of another user, by what it may and may not, and of flags and times that aren't.
//   madvise: MADV_REMOVE of shared memory, and of private EINVAL, MADV_DONTNEED of a hole ENOMEM, and guards.
//   limits: RLIMIT_FSIZE cuts a write short, then EFBIG or SIGXFSZ, and RLIMIT_AS refuses a mapping past it.
//   small: RWF_NOAPPEND, sendfile and splice to O_APPEND, mmap's and mprotect's errors, O_TMPFILE and O_TRUNC.
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/sendfile.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <unistd.h>

#ifndef MADV_GUARD_INSTALL
#define MADV_GUARD_INSTALL 102
#define MADV_GUARD_REMOVE 103
#endif
#ifndef RWF_NOAPPEND
#define RWF_NOAPPEND 0x20
#endif

static const char *error(long result) { return result < 0 ? strerror(errno) : "ok"; }
static const char *count(long result) {
  static char text[8][32];
  static int at;
  char *here = text[at++ % 8];
  if (result < 0) snprintf(here, 32, "%s", strerror(errno));
  else snprintf(here, 32, "%ld", result);
  return here;
}

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

static void make(const char *path, const char *text, int mode) {
  int fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0600);
  write(fd, text, strlen(text));
  close(fd);
  chmod(path, mode);
}

static void opath(void) {
  make("op-file", "hello", 0);
  int fd = open("op-file", O_PATH | O_RDWR | O_TRUNC);
  printf("open %s, ", error(fd));
  char buffer[8];
  printf("read %s, ", count(read(fd, buffer, 5)));
  printf("write %s, ", count(write(fd, "x", 1)));
  struct stat status;
  printf("fstat %s of %ld, ", error(fstat(fd, &status)), (long)status.st_size);
  void *map = mmap(0, 4096, PROT_READ, MAP_PRIVATE, fd, 0);
  printf("mmap %s, ", map == MAP_FAILED ? strerror(errno) : "ok");
  printf("fchmod %s, ", error(fchmod(fd, 0644)));
  int queued;
  printf("ioctl %s, ", error(ioctl(fd, FIONREAD, &queued)));
  printf("dup %s\n", error(dup(fd)));
  printf("opath: O_CREAT of what isn't there %s, ", error(open("op-new", O_PATH | O_CREAT, 0644)));
  symlink("op-file", "op-link");
  int link = open("op-link", O_PATH | O_NOFOLLOW);
  printf("a link itself %s ", error(link));
  fstat(link, &status);
  printf("is a link %d, ", S_ISLNK(status.st_mode));
  mkdir("op-dir", 0755);
  int directory = open("op-dir", O_PATH);
  printf("fchdir %s, ", error(fchdir(directory)));
  printf("openat of it %s\n", error(openat(directory, "x", O_CREAT | O_WRONLY, 0644)));
}

static void seals(void) {
  int memory = memfd_create("sealed", MFD_ALLOW_SEALING);
  write(memory, "hello", 5);
  fcntl(memory, F_ADD_SEALS, F_SEAL_SHRINK);
  char path[64];
  snprintf(path, sizeof path, "/proc/self/fd/%d", memory);
  printf("O_TRUNC of what may not shrink %s, ", error(open(path, O_RDWR | O_TRUNC)));
  struct stat status;
  fstat(memory, &status);
  printf("size %ld, ", (long)status.st_size);
  int other = memfd_create("written", MFD_ALLOW_SEALING);
  write(other, "hello", 5);
  fcntl(other, F_ADD_SEALS, F_SEAL_WRITE);
  snprintf(path, sizeof path, "/proc/self/fd/%d", other);
  printf("of what may not be written %s\n", error(open(path, O_RDWR | O_TRUNC)));
}

static void partial(void) {
  char *pages = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  memset(pages, 'a', 4096);
  mprotect(pages + 4096, 4096, PROT_NONE);
  char *edge = pages + 4096 - 10;
  int fd = open("pa-file", O_CREAT | O_RDWR | O_TRUNC, 0644);
  printf("write %s, ", count(write(fd, edge, 20)));
  printf("pwrite %s, ", count(pwrite(fd, edge, 20, 100)));
  struct iovec pieces[2] = {{pages, 5}, {pages + 4096, 5}};
  printf("writev %s, ", count(writev(fd, pieces, 2)));
  struct iovec split[2] = {{pages, 5}, {edge, 20}};
  printf("of one that ends early %s, ", count(writev(fd, split, 2)));
  printf("pwritev %s\n", count(pwritev(fd, split, 2, 200)));
  char filler[300];
  memset(filler, 'b', sizeof filler);
  pwrite(fd, filler, sizeof filler, 0);
  printf("partial: pread %s, ", count(pread(fd, edge, 20, 0)));
  printf("preadv %s, ", count(preadv(fd, split, 2, 0)));
  lseek(fd, 0, SEEK_SET);
  printf("readv %s, ", count(readv(fd, split, 2)));
  int ends[2];
  pipe(ends);
  printf("a pipe %s\n", count(write(ends[1], edge, 20)));
}

static void devzero(void) {
  int zero = open("/dev/zero", O_RDWR);
  char *private_ = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_PRIVATE, zero, 0);
  printf("private %s ", private_ == MAP_FAILED ? strerror(errno) : "ok");
  if (private_ != MAP_FAILED) {
    printf("of %d, ", private_[100]);
    private_[100] = 7;
  }
  char *shared = mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, zero, 0);
  printf("shared %s ", shared == MAP_FAILED ? strerror(errno) : "ok");
  if (shared != MAP_FAILED) {
    if (fork() == 0) {
      shared[5] = 9;
      _exit(0);
    }
    wait(0);
    printf("that a child wrote %d, ", shared[5]);
  }
  int ends[2];
  pipe(ends);
  void *map = mmap(0, 4096, PROT_READ, MAP_PRIVATE, ends[0], 0);
  printf("a pipe %s, ", map == MAP_FAILED ? strerror(errno) : "ok");
  mkdir("dz-dir", 0755);
  int directory = open("dz-dir", O_RDONLY | O_DIRECTORY);
  map = mmap(0, 4096, PROT_READ, MAP_PRIVATE, directory, 0);
  printf("a directory %s\n", map == MAP_FAILED ? strerror(errno) : "ok");
}

static void pipe0(void) {
  sigset_t mask;
  sigemptyset(&mask);
  sigaddset(&mask, SIGPIPE);
  sigprocmask(SIG_BLOCK, &mask, 0);
  int ends[2];
  pipe(ends);
  printf("of nothing %s, ", count(write(ends[1], "", 0)));
  close(ends[0]);
  printf("with no reader %s, ", count(write(ends[1], "", 0)));
  sigset_t pending;
  sigpending(&pending);
  printf("SIGPIPE %d, ", sigismember(&pending, SIGPIPE));
  printf("of something %s, ", count(write(ends[1], "x", 1)));
  sigpending(&pending);
  printf("SIGPIPE %d\n", sigismember(&pending, SIGPIPE));
}

static void times(void) {
  struct timespec now[2] = {{0, UTIME_NOW}, {0, UTIME_NOW}}, mixed[2] = {{0, UTIME_NOW}, {0, UTIME_OMIT}},
                  set[2] = {{1, 0}, {1, 0}}, omit[2] = {{0, UTIME_OMIT}, {0, UTIME_OMIT}}, bad[2] = {{0, 1000000000}, {0, 0}};
  printf("of another's that it may write: none %s, ", error(utimensat(AT_FDCWD, "/dev/null", 0, 0)));
  printf("both now %s, ", error(utimensat(AT_FDCWD, "/dev/null", now, 0)));
  printf("now and omit %s, ", error(utimensat(AT_FDCWD, "/dev/null", mixed, 0)));
  printf("set %s, ", error(utimensat(AT_FDCWD, "/dev/null", set, 0)));
  printf("omit %s\n", error(utimensat(AT_FDCWD, "/dev/null", omit, 0)));
  printf("utimes: flags %s, ", error(utimensat(AT_FDCWD, "/dev/null", 0, 0x1234)));
  printf("AT_EMPTY_PATH %s, ", error(utimensat(AT_FDCWD, "", 0, AT_EMPTY_PATH)));
  printf("a name of nothing %s, ", error(utimensat(AT_FDCWD, "", 0, 0)));
  printf("nanoseconds %s\n", error(utimensat(AT_FDCWD, "/dev/null", bad, 0)));
}

static sigjmp_buf back;
static void caught(int signal) { siglongjmp(back, signal); }

static void advice(void) {
  char *shared = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
  shared[10] = 5;
  printf("REMOVE of shared %s of %d, ", error(madvise(shared, 4096, MADV_REMOVE)), shared[10]);
  char *private_ = mmap(0, 4096 * 3, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  private_[10] = 5;
  printf("of private %s of %d, ", error(madvise(private_, 4096, MADV_REMOVE)), private_[10]);
  munmap(private_ + 4096, 4096);
  printf("DONTNEED of a hole %s of %d, ", error(madvise(private_, 4096 * 3, MADV_DONTNEED)), private_[10]);
  char *guarded = mmap(0, 4096 * 2, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  guarded[4096] = 3;
  printf("GUARD_INSTALL %s, ", error(madvise(guarded + 4096, 4096, MADV_GUARD_INSTALL)));
  signal(SIGSEGV, caught);
  volatile char seen = 0;
  int signal_ = sigsetjmp(back, 1);
  if (signal_ == 0) seen = guarded[4096];
  printf("reading it %s, ", signal_ == SIGSEGV ? "SIGSEGV" : "read");
  printf("GUARD_REMOVE %s, ", error(madvise(guarded + 4096, 4096, MADV_GUARD_REMOVE)));
  signal_ = sigsetjmp(back, 1);
  if (signal_ == 0) seen = guarded[4096];
  printf("then %s %d\n", signal_ == SIGSEGV ? "SIGSEGV" : "read", seen);
}

static void limits(void) {
  // What it says waits until it may write again, as what is written of it is limited too.
  char said[512];
  int at = 0;
  signal(SIGXFSZ, SIG_IGN);
  struct rlimit limit = {100, RLIM_INFINITY};
  setrlimit(RLIMIT_FSIZE, &limit);
  int fd = open("li-file", O_CREAT | O_RDWR | O_TRUNC, 0644);
  char data[150];
  memset(data, 'c', sizeof data);
  at += snprintf(said + at, sizeof said - at, "FSIZE of 100: 150 %s, ", count(write(fd, data, 150)));
  at += snprintf(said + at, sizeof said - at, "then %s, ", count(write(fd, data, 1)));
  at += snprintf(said + at, sizeof said - at, "pwrite below %s, ", count(pwrite(fd, data, 10, 0)));
  at += snprintf(said + at, sizeof said - at, "ftruncate past %s, ", error(ftruncate(fd, 200)));
  pid_t child = fork();
  if (child == 0) {
    signal(SIGXFSZ, SIG_DFL);
    write(fd, data, 1);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  at += snprintf(said + at, sizeof said - at, "of SIGXFSZ %s\n", WIFSIGNALED(status) && WTERMSIG(status) == SIGXFSZ ? "killed" : "lived");
  limit.rlim_cur = RLIM_INFINITY;
  setrlimit(RLIMIT_FSIZE, &limit);
  printf("%s", said);
  struct rlimit space = {64 << 20, 64 << 20};
  setrlimit(RLIMIT_AS, &space);
  void *map = mmap(0, 1 << 30, PROT_NONE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  printf("limits: AS of 64 MiB: 1 GiB %s, ", map == MAP_FAILED ? strerror(errno) : "ok");
  map = mmap(0, 1 << 20, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  printf("1 MiB %s\n", map == MAP_FAILED ? strerror(errno) : "ok");
}

static void small(void) {
  int fd = open("sm-file", O_CREAT | O_RDWR | O_TRUNC | O_APPEND, 0644);
  write(fd, "hello", 5);
  struct iovec piece = {"J", 1};
  printf("RWF_NOAPPEND %s, ", count(syscall(SYS_pwritev2, fd, &piece, 1, 0, 0, RWF_NOAPPEND)));
  char text[8] = {0};
  pread(fd, text, 5, 0);
  printf("of %s, ", text);
  int source = open("sm-source", O_CREAT | O_RDWR | O_TRUNC, 0644);
  write(source, "abc", 3);
  off_t at = 0;
  printf("sendfile to O_APPEND %s, ", count(sendfile(fd, source, &at, 3)));
  int ends[2];
  pipe(ends);
  write(ends[1], "abc", 3);
  printf("splice %s\n", count(splice(ends[0], 0, fd, 0, 3, 0)));
  printf("small: mmap of 0 %s, ", error((long)mmap(0, 0, PROT_READ, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0)));
  printf("of no kind %s, ", error((long)mmap(0, 4096, PROT_READ, MAP_ANONYMOUS, -1, 0)));
  printf("of an offset %s, ", error((long)mmap(0, 4096, PROT_READ, MAP_PRIVATE, source, 100)));
  int reading = open("sm-source", O_RDONLY);
  printf("shared writable of O_RDONLY %s, ", error((long)mmap(0, 4096, PROT_READ | PROT_WRITE, MAP_SHARED, reading, 0)));
  int writing = open("sm-source", O_WRONLY);
  printf("of O_WRONLY %s, ", error((long)mmap(0, 4096, PROT_READ, MAP_PRIVATE, writing, 0)));
  char *map = mmap(0, 4096, PROT_READ, MAP_SHARED, reading, 0);
  printf("mprotect writable of it %s, ", error(syscall(SYS_mprotect, map, 4096, PROT_READ | PROT_WRITE)));
  printf("unaligned %s, ", error(syscall(SYS_mprotect, map + 1, 4096, PROT_READ)));
  munmap(map, 4096);
  printf("of nothing %s\n", error(mprotect(map, 4096, PROT_READ)));
  printf("small: O_TMPFILE read-only %s, ", error(open(".", O_TMPFILE | O_RDONLY, 0600)));
  printf("of a file %s, ", error(open("sm-source", O_TMPFILE | O_RDWR, 0600)));
  int temporary = open(".", O_TMPFILE | O_RDWR | O_EXCL, 0600);
  char path[64];
  snprintf(path, sizeof path, "/proc/self/fd/%d", temporary);
  printf("linked of O_EXCL %s, ", error(linkat(AT_FDCWD, path, AT_FDCWD, "sm-linked", AT_SYMLINK_FOLLOW)));
  temporary = open(".", O_TMPFILE | O_RDWR, 0600);
  snprintf(path, sizeof path, "/proc/self/fd/%d", temporary);
  printf("of none %s, ", error(linkat(AT_FDCWD, path, AT_FDCWD, "sm-linked", AT_SYMLINK_FOLLOW)));
  printf("O_DIRECTORY|O_CREAT %s, ", error(open("sm-new", O_DIRECTORY | O_CREAT | O_RDWR, 0644)));
  chmod("sm-source", 0444);
  printf("O_RDONLY|O_TRUNC of what may not be written %s, ", error(open("sm-source", O_RDONLY | O_TRUNC)));
  chmod("sm-source", 0644);
  int truncated = open("sm-source", O_RDONLY | O_TRUNC);
  struct stat status;
  fstat(truncated, &status);
  printf("of what may %s of %ld\n", error(truncated), (long)status.st_size);
}

// Takes away a directory and what is in it.
static void removeAll(const char *path) {
  DIR *directory = opendir(path);
  if (!directory) {
    unlink(path);
    return;
  }
  struct dirent *entry;
  while ((entry = readdir(directory))) {
    if (strcmp(entry->d_name, ".") == 0 || strcmp(entry->d_name, "..") == 0) continue;
    char inner[512];
    snprintf(inner, sizeof inner, "%s/%s", path, entry->d_name);
    struct stat status;
    if (lstat(inner, &status) == 0 && S_ISDIR(status.st_mode)) removeAll(inner);
    else unlink(inner);
  }
  closedir(directory);
  rmdir(path);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("r16-work", 0755);
  chown("r16-work", 1000, 1000);
  chdir("r16-work");
  setgid(1000);
  setuid(1000);
  part("opath", opath);
  part("seals", seals);
  part("partial", partial);
  part("devzero", devzero);
  part("pipe0", pipe0);
  part("utimes", times);
  part("madvise", advice);
  part("limits", limits);
  part("small", small);
  chdir("..");
  removeAll("r16-work");
  printf("done\n");
  return 0;
}
