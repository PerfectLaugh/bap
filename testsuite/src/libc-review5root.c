// What Linux does of root that a third review found the machine didn't, each in a process of its own (testLinuxRaises). Run natively
// as root of a namespace of its own: unshare -rm.
//   chroot: what is above the root is the root, of .. and of a link to a path from the root.
//   mount: .. of the root of what is mounted is the directory that it is mounted in.
//   nofile: RLIMIT_NOFILE above nr_open is EPERM.
//   nice: setpriority of a process of another user is EPERM. Natively, with no other user, it is of root, which may; as with suid,
//     what it prints there isn't what it is about.
//   suid: a program that is setuid root runs as root, and AT_SECURE says so. Natively a namespace has no other user, so that what this
//     prints of it there is of root throughout, as it is where it is right.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>
#include <sys/mount.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

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

static const char *contents(const char *path) {
  static char buffer[64];
  int fd = open(path, O_RDONLY);
  if (fd < 0) return strerror(errno);
  ssize_t size = read(fd, buffer, sizeof buffer - 1);
  buffer[size > 0 ? size : 0] = 0;
  close(fd);
  return buffer;
}

static void jail(void) {
  mkdir("r5-jail", 0755);
  mkdir("r5-jail/etc", 0755);
  int fd = open("r5-jail/etc/f", O_CREAT | O_WRONLY | O_TRUNC, 0644);
  write(fd, "inside", 6);
  close(fd);
  symlink("/etc/f", "r5-jail/absolute");
  if (chroot("r5-jail") != 0) {
    printf("chroot: %s\n", strerror(errno));
    return;
  }
  chdir("/");
  printf("chroot: ../etc/f %s, ", contents("../etc/f"));
  printf("/../../etc/f %s, ", contents("/../../etc/f"));
  printf("a link to /etc/f %s\n", contents("absolute"));
}

static void mounted(void) {
  mkdir("r5-mount", 0755);
  mkdir("r5-mount/t", 0755);
  if (mount("none", "r5-mount/t", "tmpfs", 0, 0) != 0) {
    printf("mount: %s\n", strerror(errno));
    return;
  }
  struct stat above, dots;
  stat("r5-mount", &above);
  stat("r5-mount/t/..", &dots);
  printf("mount: .. of its root is where it is mounted %d, ", above.st_ino == dots.st_ino && above.st_dev == dots.st_dev);
  chdir("r5-mount/t");
  chdir("..");
  char where[4096];
  getcwd(where, sizeof where);
  printf("and chdir there is to %s\n", strrchr(where, '/') + 1);
  chdir("..");
  umount("r5-mount/t");
}

static void nofile(void) {
  struct rlimit limit = {RLIM_INFINITY, RLIM_INFINITY};
  int result = setrlimit(RLIMIT_NOFILE, &limit);
  printf("nofile: of RLIM_INFINITY %d %s\n", result, result < 0 && errno == EPERM ? "EPERM" : "");
}

static void niceOther(void) {
  pid_t child = fork();
  if (child == 0) {
    setgid(1000);
    setuid(1000);
    int result = setpriority(PRIO_PROCESS, getppid(), 5);
    printf("nice: of a process of another user %s\n", result < 0 && errno == EPERM ? "EPERM" : "set");
    _exit(0);
  }
  waitpid(child, 0, 0);
}

static void setuidRoot(void) {
  char self[4096];
  ssize_t size = readlink("/proc/self/exe", self, sizeof self - 1);
  self[size > 0 ? size : 0] = 0;
  int from = open(self, O_RDONLY), to = open("r5-suid", O_CREAT | O_WRONLY | O_TRUNC, 0755);
  char buffer[65536];
  while ((size = read(from, buffer, sizeof buffer)) > 0) write(to, buffer, size);
  close(to);
  chown("r5-suid", 0, 0);
  chmod("r5-suid", 04755);
  pid_t child = fork();
  if (child == 0) {
    setgid(1000);
    setuid(1000);
    execl("./r5-suid", "r5-suid", "suid", (char *)0);
    _exit(1);
  }
  waitpid(child, 0, 0);
  unlink("r5-suid");
}

int main(int count, char **arguments) {
  setvbuf(stdout, 0, _IONBF, 0);
  if (count > 1 && strcmp(arguments[1], "suid") == 0) {
    printf("suid: runs as euid %u, AT_SECURE %lu\n", geteuid(), getauxval(AT_SECURE));
    return 0;
  }
  part("chroot", jail);
  part("mount", mounted);
  part("nofile", nofile);
  part("nice", niceOther);
  part("suid", setuidRoot);
  printf("done\n");
  return 0;
}
