// What Linux does of root that a fourth review found the machine didn't, each in a process of its own (testLinuxRaises). Run natively as
// root of a namespace of its own: unshare -rm.
//   rootname: rename of / is EBUSY, and of a chroot, so are rmdir and rename of its /.
//   umount: of where a process that exited was, it is; of what a bind of what is in it shows, that stays; of what has a file open or
//     something mounted in it, EBUSY.
//   exdev: rename and link from one mount to another are EXDEV.
//   noexec: execve of what is on a mount of MS_NOEXEC is EACCES.
//   chrootlink: .. after a link of an absolute path, in a chroot, is of where the link led.
//   prlimit: of a process of another user, EPERM. Natively, with no other user, it is of root, which may; as with suid in
//     libc-review5root, what it prints there isn't what it is about.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

static char self[4096];

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

static void rootName(void) {
  printf("rootname: rename of / %s, ", error(rename("/", "/r8x")));
  mkdir("r8-jail", 0755);
  if (chroot("r8-jail") != 0) {
    printf("chroot %s\n", strerror(errno));
    return;
  }
  chdir("/");
  printf("in a chroot, rmdir of / %s, ", error(rmdir("/")));
  printf("rename of / %s\n", error(rename("/", "/z")));
}

static void umounts(void) {
  mkdir("r8-m", 0755);
  mount("none", "r8-m", "tmpfs", 0, 0);
  pid_t child = fork();
  if (child == 0) {
    chdir("r8-m");
    _exit(0);
  }
  waitpid(child, 0, 0);
  printf("umount: of where what exited was %s, ", error(umount("r8-m")));
  mount("none", "r8-m", "tmpfs", 0, 0);
  mkdir("r8-m/d", 0755);
  close(creat("r8-m/d/g", 0644));
  mkdir("r8-x", 0755);
  mount("r8-m/d", "r8-x", 0, MS_BIND, 0);
  umount("r8-m");
  struct stat status;
  printf("of what a bind shows, it stays %s, ", error(stat("r8-x/g", &status)));
  umount("r8-x");
  mount("none", "r8-m", "tmpfs", 0, 0);
  int fd = open("r8-m/f", O_CREAT | O_RDWR, 0644);
  printf("of a file open %s, ", error(umount("r8-m")));
  close(fd);
  mkdir("r8-m/s", 0755);
  mount("none", "r8-m/s", "tmpfs", 0, 0);
  printf("of something mounted in it %s\n", error(umount("r8-m")));
  umount("r8-m/s");
  umount("r8-m");
}

static void exdev(void) {
  mkdir("r8-e", 0755);
  mount("none", "r8-e", "tmpfs", 0, 0);
  close(creat("r8-outside", 0644));
  printf("exdev: rename into another mount %s, ", error(rename("r8-outside", "r8-e/inside")));
  printf("link %s\n", error(link("r8-outside", "r8-e/linked")));
  unlink("r8-outside");
  umount("r8-e");
}

static void noexec(void) {
  mkdir("r8-n", 0755);
  mount("none", "r8-n", "tmpfs", MS_NOEXEC, 0);
  int from = open(self, O_RDONLY), to = open("r8-n/copy", O_CREAT | O_WRONLY, 0755);
  char buffer[65536];
  ssize_t size;
  while ((size = read(from, buffer, sizeof buffer)) > 0) write(to, buffer, size);
  close(to);
  char *arguments[] = {"r8-n/copy", "executed", 0};
  execve("r8-n/copy", arguments, 0);
  printf("noexec: execve of what is on it %s\n", errno == EACCES ? "EACCES" : strerror(errno));
}

static void chrootLink(void) {
  mkdir("r8-cl", 0755);
  mkdir("r8-cl/a", 0755);
  mkdir("r8-cl/a/b", 0755);
  close(creat("r8-cl/a/m", 0644));
  symlink("/a/b", "r8-cl/l");
  if (chroot("r8-cl") != 0) return;
  chdir("/");
  printf("chrootlink: /l/../m is of where the link led %s\n", error(open("/l/../m", O_RDONLY)));
}

static void prlimitOther(void) {
  pid_t parent = getpid();
  pid_t child = fork();
  if (child == 0) {
    setgid(1000);
    setuid(1000);
    struct rlimit limit = {1, 1};
    long result = syscall(SYS_prlimit64, parent, RLIMIT_NOFILE, &limit, 0);
    printf("prlimit: of a process of another user %s\n", result < 0 && errno == EPERM ? "EPERM" : "set");
    _exit(0);
  }
  waitpid(child, 0, 0);
}

int main(int count, char **arguments) {
  setvbuf(stdout, 0, _IONBF, 0);
  if (count > 1 && strcmp(arguments[1], "executed") == 0) {
    printf("executed\n");
    return 0;
  }
  ssize_t size = readlink("/proc/self/exe", self, sizeof self - 1);
  self[size > 0 ? size : 0] = 0;
  part("rootname", rootName);
  part("umount", umounts);
  part("exdev", exdev);
  part("noexec", noexec);
  part("chrootlink", chrootLink);
  part("prlimit", prlimitOther);
  printf("done\n");
  return 0;
}
