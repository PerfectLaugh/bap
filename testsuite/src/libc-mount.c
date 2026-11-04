// Mounts and roots: a tmpfs that hides what was under it until it is unmounted, a bind mount that shares what it mounts, what goes
// wrong, a mount that a working directory keeps, chroot in a child, and pivot_root. It runs as root, natively in a user namespace of
// its own (unshare -rm), and says what it found, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <sys/mount.h>
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

static void sayText(const char *label, const char *text) {
  unsigned long n = 0;
  while (label[n]) n++;
  write(1, label, n);
  write(1, " ", 1);
  n = 0;
  while (text[n]) n++;
  write(1, text, n);
  write(1, "\n", 1);
}

static long call(long number, long a, long b, long c, long d, long e) {
  long result = syscall(number, a, b, c, d, e, 0L);
  return result < 0 ? -errno : result;
}

static long mountOf(const char *source, const char *target, const char *type, unsigned long flags) {
  return call(SYS_mount, (long)source, (long)target, (long)type, (long)flags, 0);
}

static long unmount(const char *target, int flags) { return call(SYS_umount2, (long)target, flags, 0, 0, 0); }
static long makeDirectory(const char *path) { return call(SYS_mkdirat, AT_FDCWD, (long)path, 0755, 0, 0); }
static long removeDirectory(const char *path) { return call(SYS_unlinkat, AT_FDCWD, (long)path, AT_REMOVEDIR, 0, 0); }
static long removeFile(const char *path) { return call(SYS_unlinkat, AT_FDCWD, (long)path, 0, 0, 0); }

static void put(const char *path, const char *text) {
  int fd = open(path, O_WRONLY | O_CREAT | O_TRUNC, 0644);
  unsigned long n = 0;
  while (text[n]) n++;
  write(fd, text, n);
  close(fd);
}

// What a file holds, or the error of opening it.
static void show(const char *label, const char *path) {
  int fd = open(path, O_RDONLY);
  if (fd < 0) { say(label, 1, -errno, 0, 0); return; }
  char buffer[64];
  long got = read(fd, buffer, sizeof buffer - 1);
  close(fd);
  buffer[got < 0 ? 0 : got] = 0;
  sayText(label, buffer);
}

static void cwd(const char *label) {
  char buffer[256];
  long got = call(SYS_getcwd, (long)buffer, sizeof buffer, 0, 0, 0);
  if (got < 0) say(label, 1, got, 0, 0);
  else sayText(label, buffer);
}

// The names of a directory, in order.
static void names(const char *label, const char *path) {
  int fd = open(path, O_RDONLY | O_DIRECTORY);
  if (fd < 0) { say(label, 1, -errno, 0, 0); return; }
  char buffer[2048] __attribute__((aligned(8)));
  char *found[32];
  int count = 0;
  long got;
  while ((got = call(SYS_getdents64, fd, (long)buffer, sizeof buffer, 0, 0)) > 0) {
    for (long at = 0; at < got;) {
      unsigned short length = *(unsigned short *)(buffer + at + 16);
      char *name = buffer + at + 19;
      if (count < 32 && !(name[0] == '.' && (name[1] == 0 || (name[1] == '.' && name[2] == 0)))) {
        unsigned long size = 0;
        while (name[size]) size++;
        static char kept[32][64];
        for (unsigned long index = 0; index <= size && index < 63; index++) kept[count][index] = name[index];
        found[count] = kept[count];
        count++;
      }
      at += length;
    }
  }
  close(fd);
  for (int i = 0; i < count; i++)
    for (int j = i + 1; j < count; j++) {
      int k = 0;
      while (found[i][k] && found[i][k] == found[j][k]) k++;
      if ((unsigned char)found[i][k] > (unsigned char)found[j][k]) { char *t = found[i]; found[i] = found[j]; found[j] = t; }
    }
  char line[512];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  for (int i = 0; i < count; i++) {
    line[n++] = ' ';
    for (int k = 0; found[i][k]; k++) line[n++] = found[i][k];
  }
  line[n++] = '\n';
  write(1, line, n);
}

// Whether a line of /proc/self/mountinfo has both.
static int mountedAt(const char *target, const char *type) {
  int fd = open("/proc/self/mountinfo", O_RDONLY);
  static char text[65536];
  long size = 0, got;
  while ((got = read(fd, text + size, sizeof text - 1 - size)) > 0) size += got;
  close(fd);
  text[size] = 0;
  for (char *line = text; *line;) {
    char *end = line;
    while (*end && *end != '\n') end++;
    int hasTarget = 0, hasType = 0;
    for (char *at = line; at < end; at++) {
      int k = 0;
      while (target[k] && at + k < end && at[k] == target[k]) k++;
      if (!target[k] && at > line && at[-1] == ' ' && at + k < end && at[k] == ' ') hasTarget = 1;
      k = 0;
      while (type[k] && at + k < end && at[k] == type[k]) k++;
      if (!type[k] && at[-1] == ' ') hasType = 1;
    }
    if (hasTarget && hasType) return 1;
    line = *end ? end + 1 : end;
  }
  return 0;
}

static long modeOf(const char *path) {
  struct { unsigned mask, blksize; unsigned long long attributes; unsigned nlink, uid, gid; unsigned short mode, pad;
           unsigned long long ino; char rest[200]; } value;
  long result = call(SYS_statx, AT_FDCWD, (long)path, 0, 0x7ff, (long)&value);
  return result < 0 ? result : value.mode;
}

static unsigned long long inodeOf(const char *path) {
  struct { unsigned mask, blksize; unsigned long long attributes; unsigned nlink, uid, gid; unsigned short mode, pad;
           unsigned long long ino; char rest[200]; } value;
  call(SYS_statx, AT_FDCWD, (long)path, 0, 0x7ff, (long)&value);
  return value.ino;
}

static void inJail(void) {
  say("chroot", 1, call(SYS_chroot, (long)"/tmp/mount-jail", 0, 0, 0, 0), 0, 0);
  say("chdir", 1, call(SYS_chdir, (long)"/", 0, 0, 0, 0), 0, 0);
  cwd("jail cwd");
  show("jail file", "/etc/name");
  show("above the root", "/../../etc/name");
  show("outside", "/tmp/mount-jail/etc/name");
  names("jail", "/");
}

static void pivoted(void) {
  say("chdir", 1, call(SYS_chdir, (long)"/", 0, 0, 0, 0), 0, 0);
  say("new root", 1, mountOf("none", "/tmp/mount-new", "tmpfs", 0), 0, 0);
  makeDirectory("/tmp/mount-new/old");
  put("/tmp/mount-new/here", "pivoted");
  say("pivot_root", 1, call(SYS_pivot_root, (long)"/tmp/mount-new", (long)"/tmp/mount-new/old", 0, 0, 0), 0, 0);
  cwd("pivot cwd");
  show("pivot file", "/here");
  show("old root", "/old/tmp/mount-jail/etc/name");
  say("detach old", 1, unmount("/old", MNT_DETACH), 0, 0);
  show("old gone", "/old/tmp/mount-jail/etc/name");
  names("pivot", "/");
}

static void inChild(void (*body)(void)) {
  int child = fork();
  if (child == 0) { body(); _exit(0); }
  waitpid(child, 0, 0);
}

int main(void) {
  makeDirectory("/tmp");
  makeDirectory("/tmp/mount-point");
  put("/tmp/mount-point/under", "under");

  // A tmpfs over what is there.
  say("tmpfs", 1, mountOf("none", "/tmp/mount-point", "tmpfs", 0), 0, 0);
  say("mode", 1, modeOf("/tmp/mount-point"), 0, 0);
  show("hidden", "/tmp/mount-point/under");
  put("/tmp/mount-point/inside", "inside");
  names("on tmpfs", "/tmp/mount-point");
  say("mountinfo", 1, mountedAt("/tmp/mount-point", "tmpfs"), 0, 0);
  say("umount", 1, unmount("/tmp/mount-point", 0), 0, 0);
  show("back", "/tmp/mount-point/under");
  show("gone", "/tmp/mount-point/inside");
  say("mountinfo after", 1, mountedAt("/tmp/mount-point", "tmpfs"), 0, 0);
  say("umount again", 1, unmount("/tmp/mount-point", 0), 0, 0);

  // A bind mount, which is what it mounts.
  makeDirectory("/tmp/mount-source");
  put("/tmp/mount-source/f", "bound");
  say("bind", 1, mountOf("/tmp/mount-source", "/tmp/mount-point", 0, MS_BIND), 0, 0);
  show("through bind", "/tmp/mount-point/f");
  put("/tmp/mount-point/g", "shared");
  show("in the source", "/tmp/mount-source/g");
  say("same inode", 1, inodeOf("/tmp/mount-point/f") == inodeOf("/tmp/mount-source/f"), 0, 0);
  say("unbind", 1, unmount("/tmp/mount-point", 0), 0, 0);
  names("unbound", "/tmp/mount-point");

  // Wrong ones.
  say("no such type", 1, mountOf("none", "/tmp/mount-point", "nosuchfs", 0), 0, 0);
  say("no such place", 1, mountOf("none", "/tmp/mount-none", "tmpfs", 0), 0, 0);
  say("remount nothing", 1, mountOf(0, "/tmp/mount-point", 0, MS_REMOUNT), 0, 0);
  say("private nothing", 1, mountOf(0, "/tmp/mount-point", 0, MS_PRIVATE), 0, 0);
  say("bad flags", 1, unmount("/tmp/mount-point", 0x100), 0, 0);
  say("on a file", 1, mountOf("none", "/tmp/mount-point/under", "tmpfs", 0), 0, 0);

  // A mount that a working directory is in.
  mountOf("none", "/tmp/mount-point", "tmpfs", 0);
  call(SYS_chdir, (long)"/tmp/mount-point", 0, 0, 0, 0);
  cwd("cwd on tmpfs");
  say("remount", 2, mountOf(0, "/tmp/mount-point", 0, MS_REMOUNT | MS_RDONLY), mountedAt("/tmp/mount-point", "ro"), 0);
  say("read-only", 2, open("/tmp/mount-point/new", O_WRONLY | O_CREAT, 0644) < 0 ? -errno : 0, makeDirectory("/tmp/mount-point/d"), 0);
  say("writable again", 2, mountOf(0, "/tmp/mount-point", 0, MS_REMOUNT), makeDirectory("/tmp/mount-point/d"), 0);
  say("busy", 1, unmount("/tmp/mount-point", 0), 0, 0);
  call(SYS_chdir, (long)"/", 0, 0, 0, 0);
  say("not busy", 1, unmount("/tmp/mount-point", 0), 0, 0);

  // chroot, in a child.
  makeDirectory("/tmp/mount-jail");
  makeDirectory("/tmp/mount-jail/etc");
  put("/tmp/mount-jail/etc/name", "jailed");
  inChild(inJail);
  cwd("parent cwd");
  say("chroot a file", 1, call(SYS_chroot, (long)"/tmp/mount-point/under", 0, 0, 0, 0), 0, 0);

  // pivot_root, in a child, which has a mount namespace of its own natively.
  makeDirectory("/tmp/mount-new");
  inChild(pivoted);

  removeFile("/tmp/mount-jail/etc/name");
  removeDirectory("/tmp/mount-jail/etc");
  removeDirectory("/tmp/mount-jail");
  removeFile("/tmp/mount-source/f");
  removeFile("/tmp/mount-source/g");
  removeDirectory("/tmp/mount-source");
  removeFile("/tmp/mount-point/under");
  removeDirectory("/tmp/mount-point");
  removeDirectory("/tmp/mount-new");
  return 0;
}
