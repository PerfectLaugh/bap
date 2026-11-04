// inotify: what a directory hears of what is made, written, read, closed, changed, moved and deleted in it, what a file hears of
// itself, in which order the two hear of the same thing, what is said once for being said twice, watches of one shot, what goes
// wrong, and a read that waits for what a child makes. It says what it heard, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <time.h>
#include <sys/inotify.h>
#include <sys/ioctl.h>
#include <sys/stat.h>
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

static long call(long number, long a, long b, long c) {
  long result = syscall(number, a, b, c, 0L, 0L, 0L);
  return result < 0 ? -errno : result;
}

static long addWatch(int fd, const char *path, unsigned mask) { return call(SYS_inotify_add_watch, fd, (long)path, mask); }

static unsigned lastCookie;

// Each event that there is to read: its watch, its mask, whether its cookie is that of the one before, and its name.
static void heard(const char *label, int fd) {
  char buffer[4096] __attribute__((aligned(8)));
  long got = read(fd, buffer, sizeof buffer);
  if (got < 0) { say(label, 1, -errno, 0, 0); return; }
  for (long at = 0; at < got;) {
    struct inotify_event *event = (struct inotify_event *)(buffer + at);
    char line[160];
    unsigned long n = 0;
    while (label[n]) { line[n] = label[n]; n++; }
    line[n++] = ':';
    write(1, line, n);
    say("", 3, event->wd, (long)event->mask, event->cookie == 0 ? 0 : event->cookie == lastCookie ? 2 : 1);
    if (event->cookie) lastCookie = event->cookie;
    if (event->len) {
      unsigned long size = 0;
      while (event->name[size]) size++;
      write(1, "  name ", 7);
      write(1, event->name, size);
      write(1, "\n", 1);
    }
    at += sizeof(struct inotify_event) + event->len;
  }
}

int main(void) {
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp", 0777, 0, 0, 0);
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp/notify", 0777, 0, 0, 0);
  int fd = (int)call(SYS_inotify_init1, IN_NONBLOCK | IN_CLOEXEC, 0, 0);
  say("init", 2, fd >= 0, fcntl(fd, F_GETFD), 0);
  say("watch", 1, addWatch(fd, "/tmp/notify", IN_ALL_EVENTS), 0, 0);
  heard("nothing yet", fd);

  // A file made, written, closed, read.
  int file = open("/tmp/notify/a", O_WRONLY | O_CREAT | O_TRUNC, 0644);
  write(file, "one", 3);
  write(file, "two", 3);
  close(file);
  heard("made", fd);
  file = open("/tmp/notify/a", O_RDONLY);
  char bytes[8];
  read(file, bytes, sizeof bytes);
  close(file);
  heard("read", fd);
  syscall(SYS_fchmodat, AT_FDCWD, "/tmp/notify/a", 0600, 0, 0, 0);
  heard("chmod", fd);

  // Moved, and a directory made and removed.
  syscall(SYS_renameat2, AT_FDCWD, "/tmp/notify/a", AT_FDCWD, "/tmp/notify/b", 0, 0);
  heard("moved", fd);
  syscall(SYS_mkdirat, AT_FDCWD, "/tmp/notify/sub", 0777, 0, 0, 0);
  syscall(SYS_unlinkat, AT_FDCWD, "/tmp/notify/sub", AT_REMOVEDIR, 0, 0, 0);
  heard("directory", fd);

  // A watch of the file too, which hears after the directory, and then hears that it was deleted.
  say("file watch", 1, addWatch(fd, "/tmp/notify/b", IN_OPEN | IN_MODIFY | IN_ATTRIB | IN_CLOSE_WRITE | IN_DELETE_SELF), 0, 0);
  say("same again", 1, addWatch(fd, "/tmp/notify/b", IN_OPEN | IN_MODIFY | IN_ATTRIB | IN_CLOSE_WRITE | IN_DELETE_SELF), 0, 0);
  file = open("/tmp/notify/b", O_WRONLY | O_APPEND);
  write(file, "three", 5);
  close(file);
  heard("both", fd);
  syscall(SYS_unlinkat, AT_FDCWD, "/tmp/notify/b", 0, 0, 0, 0);
  heard("deleted", fd);

  // What is waiting, a buffer too small for it, one shot, and taking a watch away.
  file = open("/tmp/notify/c", O_WRONLY | O_CREAT, 0644);
  int waiting = -1;
  ioctl(fd, FIONREAD, &waiting);
  say("waiting", 1, waiting, 0, 0);
  char small[8];
  say("too small", 1, read(fd, small, sizeof small) < 0 ? -errno : 0, 0, 0);
  heard("c", fd);
  say("one shot", 1, addWatch(fd, "/tmp/notify/c", IN_MODIFY | IN_ONESHOT), 0, 0);
  write(file, "x", 1);
  write(file, "y", 1);
  close(file);
  heard("shot", fd);
  say("rm_watch", 2, call(SYS_inotify_rm_watch, fd, 1, 0), call(SYS_inotify_rm_watch, fd, 1, 0), 0);
  heard("removed", fd);
  heard("empty", fd);

  // Wrong ones.
  say("no events", 1, addWatch(fd, "/tmp/notify", 0), 0, 0);
  say("only a directory", 1, addWatch(fd, "/tmp/notify/c", IN_MODIFY | IN_ONLYDIR), 0, 0);
  say("missing", 1, addWatch(fd, "/tmp/notify/none", IN_MODIFY), 0, 0);
  say("watch twice", 2, addWatch(fd, "/tmp/notify/c", IN_MODIFY), addWatch(fd, "/tmp/notify/c", IN_MODIFY | IN_MASK_CREATE), 0);
  say("not inotify", 1, addWatch(1, "/tmp/notify", IN_MODIFY), 0, 0);
  say("bad flags", 1, call(SYS_inotify_init1, 0x1234, 0, 0), 0, 0);

  // A file that is watched moves.
  say("move watch", 1, addWatch(fd, "/tmp/notify/c", IN_MOVE_SELF | IN_MASK_ADD), 0, 0);
  syscall(SYS_renameat2, AT_FDCWD, "/tmp/notify/c", AT_FDCWD, "/tmp/notify/d", 0, 0);
  heard("move self", fd);

  // A read that waits for what a child makes.
  int blocking = (int)call(SYS_inotify_init1, 0, 0, 0);
  addWatch(blocking, "/tmp/notify", IN_CREATE);
  int child = fork();
  if (child == 0) {
    struct timespec pause = {0, 20000000};
    nanosleep(&pause, 0);
    close(open("/tmp/notify/late", O_WRONLY | O_CREAT, 0644));
    _exit(0);
  }
  heard("waited", blocking);
  waitpid(child, 0, 0);
  syscall(SYS_unlinkat, AT_FDCWD, "/tmp/notify/d", 0, 0, 0, 0);
  syscall(SYS_unlinkat, AT_FDCWD, "/tmp/notify/late", 0, 0, 0, 0);
  syscall(SYS_unlinkat, AT_FDCWD, "/tmp/notify", AT_REMOVEDIR, 0, 0, 0);
  return 0;
}
