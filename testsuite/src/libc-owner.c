// Who owns what a process makes, as Linux has it: the user and the group of its filesystem, which are its effective ones, of a file, a
// directory, a symbolic link, a socket bound to a path, an O_TMPFILE file, a memfd, a pipe and a socket; but in a directory with
// S_ISGID, the group of the directory, which a directory made in it has too, with S_ISGID. What umask leaves of the mode is the mode.
// It makes a directory where it runs, and takes that away at the end. As root it gives what it made to nobody and is nobody, in a group
// besides, so that it says the same as anyone else, who chooses a group that it is in besides its own, if it is in one that it may
// give. It says what each owner is, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <unistd.h>

long syscall(long, ...);

static void say(const char *label, long value) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  if (value < 0) { line[n++] = '-'; value = -value; }
  char digits[24];
  int d = 0;
  do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
  while (d) line[n++] = digits[--d];
  line[n++] = '\n';
  write(1, line, n);
}

static long result(long value) { return value < 0 ? -errno : value; }

// statx, whose layout every target has: of a path, of a link itself, or of a descriptor with an empty path.
struct timestamp { long long sec; unsigned nsec; int pad; };
struct statx_ { unsigned mask, blksize; unsigned long long attributes; unsigned nlink, uid, gid; unsigned short mode, pad;
                unsigned long long ino, size, blocks, attributesMask; struct timestamp atime, btime, ctime, mtime; char rest[128]; };

static struct statx_ statOf(int directory, const char *path) {
  struct statx_ out = {0};
  syscall(SYS_statx, directory, path, *path ? AT_SYMLINK_NOFOLLOW : AT_EMPTY_PATH, 0x7ff, &out);
  return out;
}

// Whether what is there is of the effective user and group, and its permissions.
static void owner(const char *label, int directory, const char *path) {
  struct statx_ found = statOf(directory, path);
  char line[96];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  const char *uid = " uid";
  for (size_t i = 0; uid[i]; i++) line[n++] = uid[i];
  line[n] = 0;
  say(line, found.uid == (unsigned)syscall(SYS_geteuid));
  line[n - 3] = 'g';
  say(line, found.gid == (unsigned)syscall(SYS_getegid));
}

static void ownerOf(const char *label, int fd) { owner(label, fd, ""); }

static void ownerAt(const char *label, const char *path) { owner(label, AT_FDCWD, path); }

static long modeOf(const char *path) { return statOf(AT_FDCWD, path).mode & 07777; }

static long gidOf(const char *path) { return statOf(AT_FDCWD, path).gid; }

int main(void) {
  syscall(SYS_umask, 022);
  say("mkdir", result(syscall(SYS_mkdirat, AT_FDCWD, "owner", 0777)));
  int fd = syscall(SYS_openat, AT_FDCWD, "owner/first", O_CREAT | O_WRONLY, 0666);
  close(fd);
  ownerAt("first", "owner/first");
  say("first mode", modeOf("owner/first"));
  say("directory mode", modeOf("owner"));

  // A directory with S_ISGID, of a group that the process is in and that isn't its own if it can be.
  say("mkdir setgid", result(syscall(SYS_mkdirat, AT_FDCWD, "owner/setgid", 0777)));
  long root = syscall(SYS_geteuid) == 0;
  unsigned group = (unsigned)syscall(SYS_getegid);
  if (root) group = 100;
  else {
    unsigned groups[64];
    long count = syscall(SYS_getgroups, 64, groups);
    for (long index = 0; index < count; index++)
      if (groups[index] != group && groups[index] != 65534) { group = groups[index]; break; }
  }
  say("chown setgid", result(syscall(SYS_fchownat, AT_FDCWD, "owner/setgid", -1, group, 0)));
  say("chmod setgid", result(syscall(SYS_fchmodat, AT_FDCWD, "owner/setgid", 02777)));
  if (root) {
    syscall(SYS_fchownat, AT_FDCWD, "owner", 65534, 65534, 0);
    syscall(SYS_fchownat, AT_FDCWD, "owner/first", 65534, 65534, 0);
    unsigned besides[] = {100};
    syscall(SYS_setgroups, 1, besides);
    syscall(SYS_setresgid, 65534, 65534, 65534);
    syscall(SYS_setresuid, 65534, 65534, 65534);
  }
  say("not root", syscall(SYS_geteuid) != 0);

  fd = syscall(SYS_openat, AT_FDCWD, "owner/file", O_CREAT | O_WRONLY, 0666);
  close(fd);
  ownerAt("file", "owner/file");
  say("file mode", modeOf("owner/file"));
  say("mkdir directory", result(syscall(SYS_mkdirat, AT_FDCWD, "owner/directory", 0777)));
  ownerAt("directory", "owner/directory");
  say("subdirectory mode", modeOf("owner/directory"));
  say("symlink", result(syscall(SYS_symlinkat, "file", AT_FDCWD, "owner/link")));
  ownerAt("link", "owner/link");
  fd = syscall(SYS_openat, AT_FDCWD, "owner", O_TMPFILE | O_RDWR, 0600);
  ownerOf("tmpfile", fd);
  close(fd);
  fd = syscall(SYS_memfd_create, "owner", 0);
  ownerOf("memfd", fd);
  close(fd);
  int ends[2];
  syscall(SYS_pipe2, ends, 0);
  ownerOf("pipe read", ends[0]);
  ownerOf("pipe write", ends[1]);
  close(ends[0]);
  close(ends[1]);
  fd = syscall(SYS_socket, 1, 1, 0);
  ownerOf("socket", fd);
  struct { unsigned short family; char path[108]; } address = {1, "owner/socket"};
  say("bind", result(syscall(SYS_bind, fd, &address, sizeof address)));
  ownerAt("bound", "owner/socket");
  close(fd);
  syscall(SYS_socketpair, 1, 1, 0, ends);
  ownerOf("socketpair", ends[0]);
  close(ends[0]);
  close(ends[1]);

  // In the directory with S_ISGID, what is made is of its group, and a directory has S_ISGID too.
  long shared = gidOf("owner/setgid");
  fd = syscall(SYS_openat, AT_FDCWD, "owner/setgid/file", O_CREAT | O_WRONLY, 0666);
  close(fd);
  say("setgid file group", gidOf("owner/setgid/file") == shared);
  say("setgid file uid", statOf(AT_FDCWD, "owner/setgid/file").uid == (unsigned)syscall(SYS_geteuid));
  say("setgid file mode", modeOf("owner/setgid/file"));
  say("mkdir in setgid", result(syscall(SYS_mkdirat, AT_FDCWD, "owner/setgid/directory", 0777)));
  say("setgid directory group", gidOf("owner/setgid/directory") == shared);
  say("setgid directory mode", modeOf("owner/setgid/directory"));
  say("symlink in setgid", result(syscall(SYS_symlinkat, "file", AT_FDCWD, "owner/setgid/link")));
  say("setgid link group", gidOf("owner/setgid/link") == shared);
  fd = syscall(SYS_openat, AT_FDCWD, "owner/setgid", O_TMPFILE | O_RDWR, 0600);
  say("setgid tmpfile group", statOf(fd, "").gid == shared);
  close(fd);

  const char *files[] = {"owner/setgid/link", "owner/setgid/file", "owner/socket", "owner/link", "owner/file", "owner/first"};
  for (int index = 0; index < 6; index++) syscall(SYS_unlinkat, AT_FDCWD, files[index], 0);
  const char *directories[] = {"owner/setgid/directory", "owner/setgid", "owner/directory", "owner"};
  long removed = 0;
  for (int index = 0; index < 4; index++) removed += syscall(SYS_unlinkat, AT_FDCWD, directories[index], AT_REMOVEDIR) == 0;
  say("removed", removed);
  return 0;
}
