// Pseudo-terminals: what /dev/ptmx makes, and its line discipline of canonical lines, editing, echo and what goes out, raw mode, an end
// of file, the size of the window, a controlling terminal whose ^C reaches its foreground, a read of the background, a hangup of either
// end as a read, poll and epoll see it, and raw reads of VMIN and VTIME. It says what it found, the same on each target with the termios of x86, ARM, AArch64 and RISC-V. The libc of the tests has no ioctl,
// setsid or setpgid, so they are called by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <string.h>
#include <poll.h>
#include <sys/epoll.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

#define TCGETS 0x5401
#define TCSETS 0x5402
#define TIOCGWINSZ 0x5413
#define TIOCSWINSZ 0x5414
#define TIOCGPGRP 0x540F
#define TIOCGSID 0x5429
#define TIOCGPTN 0x80045430
#define TIOCSPTLCK 0x40045431

struct termios_ { unsigned iflag, oflag, cflag, lflag; unsigned char line, cc[19]; };
struct winsize_ { unsigned short rows, cols, x, y; };

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
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

// What was read, with what can't be seen as `\` and its number.
static void text(const char *label, const char *bytes, long count) {
  char line[256];
  unsigned long n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  for (long index = 0; index < count && n < 240; index++) {
    unsigned char byte = (unsigned char)bytes[index];
    if (byte >= 32 && byte < 127) line[n++] = (char)byte;
    else { line[n++] = '\\'; line[n++] = (char)('0' + byte / 64); line[n++] = (char)('0' + byte / 8 % 8); line[n++] = (char)('0' + byte % 8); }
  }
  line[n++] = '\n';
  write(1, line, n);
}

static long control(int fd, unsigned long request, void *argument) {
  long result = syscall(SYS_ioctl, fd, request, argument);
  return result < 0 ? -errno : result;
}

// What poll says of a descriptor, without waiting.
static long polled(int fd, short events) {
  struct pollfd entry = { fd, events, 0 };
  struct timespec now = { 0, 0 };
  long found = syscall(SYS_ppoll, &entry, 1, &now, 0, 8);
  return found < 0 ? -errno : entry.revents;
}

// Raw mode, without echo, of these VMIN and VTIME.
static void raw(int slave, int min, int time) {
  struct termios_ tio;
  control(slave, TCGETS, &tio);
  tio.lflag &= ~(0x2u | 0x8u);
  tio.cc[6] = (unsigned char)min;
  tio.cc[5] = (unsigned char)time;
  control(slave, TCSETS, &tio);
}

static int openSlave(int master, int flags) {
  int unlock = 0;
  unsigned index = 0;
  control(master, TIOCSPTLCK, &unlock);
  control(master, TIOCGPTN, &index);
  char path[32] = "/dev/pts/";
  int n = 9;
  char digits[12];
  int d = 0;
  do { digits[d++] = (char)('0' + index % 10); index /= 10; } while (index);
  while (d) path[n++] = digits[--d];
  path[n] = 0;
  return open(path, O_RDWR | flags);
}

int main(void) {
  int master = open("/dev/ptmx", O_RDWR | O_NOCTTY);
  int slave = openSlave(master, O_NOCTTY);
  say("ptmx", 2, master >= 0, slave >= 0, 0);
  struct termios_ tio;
  int fds[2];
  pipe(fds);
  say("a terminal and a pipe", 2, control(slave, TCGETS, &tio), control(fds[0], TCGETS, &tio), 0);
  char buffer[64];

  // A line, as it is edited, with what the master sees of it.
  write(master, "ab\177c\rd\n", 7);
  long got = read(slave, buffer, sizeof buffer);
  text("a line", buffer, got);
  got = read(slave, buffer, sizeof buffer);
  text("and the next", buffer, got);
  got = read(master, buffer, sizeof buffer);
  text("its echo", buffer, got);
  write(slave, "out\n", 4);
  got = read(master, buffer, sizeof buffer);
  text("what goes out", buffer, got);
  write(master, "\004", 1);
  say("an end of file", 1, read(slave, buffer, sizeof buffer), 0, 0);

  // Raw: what there is, without echo.
  control(slave, TCGETS, &tio);
  tio.lflag &= ~(0x2u | 0x8u);
  tio.cc[6] = 1;
  tio.cc[5] = 0;
  control(slave, TCSETS, &tio);
  write(master, "xyz", 3);
  got = read(slave, buffer, 2);
  text("raw", buffer, got);
  got = read(slave, buffer, sizeof buffer);
  text("and the rest", buffer, got);
  fcntl(master, F_SETFL, O_NONBLOCK);
  say("no echo", 1, read(master, buffer, sizeof buffer) == -1 && errno == EAGAIN, 0, 0);
  fcntl(master, F_SETFL, 0);
  tio.lflag |= 0x2u | 0x8u;
  control(slave, TCSETS, &tio);

  struct winsize_ size = { 30, 100, 0, 0 }, read_;
  control(master, TIOCSWINSZ, &size);
  control(slave, TIOCGWINSZ, &read_);
  say("the window", 2, read_.rows, read_.cols, 0);
  close(slave);

  // A session whose controlling terminal it is, of which ^C ends the foreground.
  int ready[2];
  pipe(ready);
  pid_t child = fork();
  if (child == 0) {
    syscall(SYS_setsid);
    int own = openSlave(master, 0);
    int pgrp = 0, sid = 0;
    control(own, TIOCGPGRP, &pgrp);
    control(own, TIOCGSID, &sid);
    int tty = open("/dev/tty", O_RDWR);
    char verdict = (pgrp == getpid() && sid == getpid() && tty >= 0) ? 'y' : 'n';
    // A process of the background that reads it, which ignores SIGTTIN: EIO.
    pid_t back = fork();
    if (back == 0) {
      syscall(SYS_setpgid, 0, 0);
      signal(SIGTTIN, SIG_IGN);
      char byte;
      _exit(read(own, &byte, 1) == -1 && errno == EIO ? 0 : 1);
    }
    int status = 0;
    waitpid(back, &status, 0);
    char background = WIFEXITED(status) && WEXITSTATUS(status) == 0 ? 'y' : 'n';
    write(ready[1], &verdict, 1);
    write(ready[1], &background, 1);
    for (;;) read(own, buffer, sizeof buffer);
  }
  char answers[2];
  read(ready[0], answers, 2);
  text("its controlling terminal", answers, 2);
  write(master, "\003", 1);
  int status = 0;
  waitpid(child, &status, 0);
  say("^C ends it", 2, WIFSIGNALED(status), WIFSIGNALED(status) ? WTERMSIG(status) : 0, 0);
  got = read(master, buffer, sizeof buffer);
  text("and is seen", buffer, got);

  // Once nothing has the master, the slave has nothing more.
  slave = openSlave(master, O_NOCTTY);
  close(master);
  long after = read(slave, buffer, sizeof buffer);
  say("a hangup", 2, after, after < 0 ? errno : 0, 0);
  say("and poll sees it", 1, polled(slave, POLLIN | POLLOUT), 0, 0);
  close(slave);

  // Once nothing has the slave, after it was, the master hangs up, as poll and epoll see.
  master = open("/dev/ptmx", O_RDWR | O_NOCTTY);
  slave = openSlave(master, O_NOCTTY);
  say("a master", 1, polled(master, POLLIN | POLLOUT), 0, 0);
  close(slave);
  say("of no slave", 1, polled(master, POLLIN | POLLOUT), 0, 0);
  int epoll = (int)syscall(SYS_epoll_create1, 0);
  struct epoll_event event = { EPOLLIN | EPOLLOUT, { 0 } }, events[2];
  syscall(SYS_epoll_ctl, epoll, EPOLL_CTL_ADD, master, &event);
  long count = syscall(SYS_epoll_pwait, epoll, events, 2, 0, 0, 8);
  say("and epoll", 2, count, count > 0 ? (long)events[0].events : 0, 0);
  after = read(master, buffer, sizeof buffer);
  say("and a read", 2, after, after < 0 ? errno : 0, 0);
  close(epoll);
  close(master);

  // VMIN: a read waits for as many bytes, or as it asks for, but of O_NONBLOCK, and poll says so.
  master = open("/dev/ptmx", O_RDWR | O_NOCTTY);
  slave = openSlave(master, O_NOCTTY);
  raw(slave, 4, 0);
  write(master, "ab", 2);
  say("VMIN 4 of 2", 1, polled(slave, POLLIN), 0, 0);
  write(master, "cd", 2);
  say("and of 4", 1, polled(slave, POLLIN), 0, 0);
  got = read(slave, buffer, sizeof buffer);
  text("which a read takes", buffer, got);
  write(master, "ef", 2);
  pid_t writer = fork();
  if (writer == 0) {
    struct timespec pause = { 0, 50000000 };
    nanosleep(&pause, 0);
    write(master, "gh", 2);
    _exit(0);
  }
  got = read(slave, buffer, sizeof buffer);
  text("a read that waits", buffer, got);
  waitpid(writer, &status, 0);
  write(master, "ij", 2);
  got = read(slave, buffer, 2);
  text("a read of fewer", buffer, got);
  write(master, "k", 1);
  fcntl(slave, F_SETFL, O_NONBLOCK);
  got = read(slave, buffer, sizeof buffer);
  text("of O_NONBLOCK", buffer, got);
  after = read(slave, buffer, sizeof buffer);
  say("and of nothing", 2, after, after < 0 ? errno : 0, 0);
  fcntl(slave, F_SETFL, 0);

  // VMIN of 0: nothing is ready to poll, and a read of VTIME waits that long for a byte, or after one that came, as of VMIN.
  raw(slave, 0, 0);
  say("VMIN 0", 2, polled(slave, POLLIN), read(slave, buffer, sizeof buffer), 0);
  raw(slave, 0, 1);
  say("and VTIME 1", 2, polled(slave, POLLIN), read(slave, buffer, sizeof buffer), 0);
  write(master, "l", 1);
  got = read(slave, buffer, sizeof buffer);
  text("of a byte", buffer, got);
  raw(slave, 2, 1);
  write(master, "m", 1);
  say("VMIN 2 and VTIME 1 of 1", 1, polled(slave, POLLIN), 0, 0);
  got = read(slave, buffer, sizeof buffer);
  text("which a read takes", buffer, got);
  close(slave);
  close(master);
  return 0;
}
