// What Linux does with mounts and permissions that a fifth review found the machine didn't, as root, each in a process of its own, in a
// tmpfs of its own that it mounts where it runs:
//   erofs: chmod, chown, utimensat, setxattr, truncate, open to write and mkdir of what is on a read-only mount are EROFS.
//   bind: MS_BIND takes no flags but MS_REC, so that a bind that asks to be read-only isn't until a remount of MS_BIND makes it so, of
//     where it is mounted and not of what it binds; and a bind is a mount of its own, so that rename and link across it are EXDEV.
//   noexec: access of X_OK, and execve, of what is on a mount of MS_NOEXEC are EACCES.
//   order: without capabilities, chroot, mount and umount2 look the path up first, ENOENT and ENOTDIR, then whether they may, EPERM,
//     and umount2 its flags before all.
//   setuid: chown of -1 and -1 of a setuid file of another user is EPERM, which its owner may, and then it isn't setuid.
// The host has no other user to be, so that `setuid` is as the kernel's source has it: chown_common asks notify_change to kill setuid,
// and setattr_prepare lets only the owner change the mode.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <string.h>
#include <sys/mount.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <unistd.h>

static const char *error(long result) { return result < 0 ? strerror(errno) : "ok"; }

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

static void make(const char *path, int mode) {
  int fd = open(path, O_CREAT | O_TRUNC | O_WRONLY, 0600);
  write(fd, "hello", 5);
  close(fd);
  chmod(path, mode);
}

static void readOnly(void) {
  mkdir("ro", 0755);
  mount("none", "ro", "tmpfs", 0, 0);
  make("ro/file", 0644);
  printf("remount %s, ", error(mount(0, "ro", 0, MS_REMOUNT | MS_RDONLY, 0)));
  printf("chmod %s, ", error(chmod("ro/file", 0600)));
  printf("chown %s, ", error(chown("ro/file", 0, 0)));
  printf("utimensat %s, ", error(utimensat(AT_FDCWD, "ro/file", 0, 0)));
  printf("setxattr %s\n", error(setxattr("ro/file", "user.name", "x", 1, 0)));
  printf("erofs: removexattr %s, ", error(removexattr("ro/file", "user.name")));
  printf("truncate %s, ", error(truncate("ro/file", 0)));
  printf("open to write %s, ", error(open("ro/file", O_WRONLY)));
  printf("mkdir %s\n", error(mkdir("ro/dir", 0755)));
  umount("ro");
}

static void bind(void) {
  mkdir("source", 0755);
  make("source/file", 0644);
  mkdir("target", 0755);
  printf("bind read-only %s, ", error(mount("source", "target", 0, MS_BIND | MS_RDONLY, 0)));
  int written = open("target/file", O_WRONLY);
  printf("written %s, ", error(written));
  close(written);
  printf("remount %s, ", error(mount(0, "target", 0, MS_REMOUNT | MS_BIND | MS_RDONLY, 0)));
  printf("written %s, ", error(open("target/file", O_WRONLY)));
  printf("of the source %s\n", error(open("source/file", O_WRONLY)));
  printf("bind: rename across %s, ", error(rename("target/file", "source/moved")));
  printf("link across %s, ", error(link("source/file", "target/linked")));
  umount("target");
  mkdir("other", 0755);
  mount("source", "other", 0, MS_BIND, 0);
  printf("rename into a writable bind %s, ", error(rename("source/file", "other/moved")));
  printf("within it %s\n", error(rename("other/file", "other/moved")));
  umount("other");
}

static void noexec(void) {
  mkdir("nx", 0755);
  mount("none", "nx", "tmpfs", MS_NOEXEC, 0);
  make("nx/program", 0755);
  printf("X_OK %s, ", error(access("nx/program", X_OK)));
  printf("R_OK %s, ", error(access("nx/program", R_OK)));
  char *arguments[] = {"program", 0};
  printf("execve %s\n", error(execve("nx/program", arguments, 0)));
  umount("nx");
}

static void order(void) {
  make("plain", 0644);
  // No capabilities, as a user has none.
  struct {
    unsigned version;
    int pid;
  } header = {0x20080522, 0};
  struct {
    unsigned effective, permitted, inheritable;
  } data[2] = {{0, 0, 0}, {0, 0, 0}};
  syscall(SYS_capset, &header, data);
  printf("chroot of nothing %s, ", error(chroot("missing")));
  printf("of a file %s, ", error(chroot("plain")));
  printf("of a directory %s, ", error(chroot(".")));
  printf("mount on nothing %s, ", error(mount("none", "missing", "tmpfs", 0, 0)));
  printf("on a directory %s\n", error(mount("none", ".", "tmpfs", 0, 0)));
  printf("order: umount2 of a flag %s, ", error(umount2("missing", 0x100)));
  printf("of nothing %s, ", error(umount2("missing", 0)));
  printf("of a directory %s\n", error(umount2(".", 0)));
}

static void setuidFile(void) {
  make("setuid", 04755);
  chown("setuid", 0, 0);
  chmod("setuid", 04755);
  pid_t child = fork();
  if (child == 0) {
    setuid(1000);
    printf("another's %s, ", error(chown("setuid", -1, -1)));
    _exit(0);
  }
  waitpid(child, 0, 0);
  struct stat status;
  stat("setuid", &status);
  printf("still %o, ", status.st_mode & 07777);
  printf("its owner's %s, ", error(chown("setuid", -1, -1)));
  stat("setuid", &status);
  printf("then %o\n", status.st_mode & 07777);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("r16root", 0755);
  mount("none", "r16root", "tmpfs", 0, 0);
  chdir("r16root");
  part("erofs", readOnly);
  part("bind", bind);
  part("noexec", noexec);
  part("order", order);
  part("setuid", setuidFile);
  chdir("..");
  umount("r16root");
  rmdir("r16root");
  printf("done\n");
  return 0;
}
