// Descriptors in flight with SCM_RIGHTS: an open file that only a message waiting in a socket has is open yet, until the message is
// received and the descriptor closed, or the socket that has the message is closed with it unread. The calls are made by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

long syscall(long, ...);

static long sys(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

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

// What poll has of a descriptor now, or the error.
static long polled(int fd, int events) {
  struct pollfd entry = { fd, (short)events, 0 };
  struct timespec zero = { 0, 0 };
  long result = sys(SYS_ppoll, (long)&entry, 1, (long)&zero, 0, 8, 0);
  return result < 0 ? result : entry.revents;
}

static long handOver(int over, int fd) {
  char byte = 'f';
  struct iovec io = { &byte, 1 };
  union { char bytes[CMSG_SPACE(sizeof(int))]; struct cmsghdr align; } control;
  memset(&control, 0, sizeof control);
  struct msghdr message;
  memset(&message, 0, sizeof message);
  message.msg_iov = &io;
  message.msg_iovlen = 1;
  message.msg_control = control.bytes;
  message.msg_controllen = sizeof control.bytes;
  struct cmsghdr *header = CMSG_FIRSTHDR(&message);
  header->cmsg_level = SOL_SOCKET;
  header->cmsg_type = SCM_RIGHTS;
  header->cmsg_len = CMSG_LEN(sizeof(int));
  memcpy(CMSG_DATA(header), &fd, sizeof fd);
  return sys(SYS_sendmsg, over, (long)&message, 0, 0, 0, 0);
}

static int takeOver(int from) {
  char byte;
  struct iovec io = { &byte, 1 };
  union { char bytes[CMSG_SPACE(sizeof(int))]; struct cmsghdr align; } control;
  memset(&control, 0, sizeof control);
  struct msghdr message;
  memset(&message, 0, sizeof message);
  message.msg_iov = &io;
  message.msg_iovlen = 1;
  message.msg_control = control.bytes;
  message.msg_controllen = sizeof control.bytes;
  if (sys(SYS_recvmsg, from, (long)&message, 0, 0, 0, 0) != 1) return -1;
  struct cmsghdr *header = CMSG_FIRSTHDR(&message);
  if (!header || header->cmsg_type != SCM_RIGHTS) return -1;
  int fd;
  memcpy(&fd, CMSG_DATA(header), sizeof fd);
  return fd;
}

int main(void) {
  signal(SIGPIPE, SIG_IGN);
  char buffer[8];
  int pipes[2], pair[2];

  // The write end of a pipe in flight, closed by the sender: the read end has a writer yet.
  pipe2(pipes, O_NONBLOCK);
  sys(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, (long)pair, 0, 0);
  say("hand over write end", handOver(pair[0], pipes[1]));
  close(pipes[1]);
  say("read end polls, writer in flight", polled(pipes[0], POLLIN));
  say("read end reads, writer in flight", sys(SYS_read, pipes[0], (long)buffer, sizeof buffer, 0, 0, 0));
  int writer = takeOver(pair[1]);
  say("received", writer >= 0);
  say("write through received", sys(SYS_write, writer, (long)"w", 1, 0, 0, 0));
  say("read end reads it", sys(SYS_read, pipes[0], (long)buffer, sizeof buffer, 0, 0, 0));
  close(writer);
  say("read end polls, writer closed", polled(pipes[0], POLLIN));
  say("read end reads, writer closed", sys(SYS_read, pipes[0], (long)buffer, sizeof buffer, 0, 0, 0));
  close(pipes[0]);

  // A connected socket in flight, closed by the sender: its peer has the other end yet.
  int connected[2];
  sys(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, (long)connected, 0, 0);
  say("hand over socket", handOver(pair[0], connected[1]));
  close(connected[1]);
  say("peer writes, other end in flight", sys(SYS_write, connected[0], (long)"x", 1, 0, 0, 0));
  say("peer polls, other end in flight", polled(connected[0], POLLIN | POLLOUT));
  int other = takeOver(pair[1]);
  say("received socket reads", sys(SYS_read, other, (long)buffer, sizeof buffer, 0, 0, 0));
  close(other);
  say("peer writes, other end closed", sys(SYS_write, connected[0], (long)"x", 1, 0, 0, 0));
  close(connected[0]);

  // The socket that has the message closed with it unread: the write end in flight is closed with it.
  pipe2(pipes, O_NONBLOCK);
  say("hand over write end again", handOver(pair[0], pipes[1]));
  close(pipes[1]);
  say("read end polls, writer in flight", polled(pipes[0], POLLIN));
  close(pair[1]);
  say("read end polls, receiver closed", polled(pipes[0], POLLIN));
  say("read end reads, receiver closed", sys(SYS_read, pipes[0], (long)buffer, sizeof buffer, 0, 0, 0));
  close(pipes[0]);
  close(pair[0]);
  return 0;
}
