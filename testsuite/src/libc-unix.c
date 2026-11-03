// Sockets of the Unix domain: pairs, a listener and its connections across processes, datagrams with names of their own, packets,
// descriptors handed over, and what goes wrong. The libc of the tests has no sockets, so the calls are made by number.
#define _GNU_SOURCE
#include <errno.h>
#include <signal.h>
#include <stddef.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>
#include <fcntl.h>

long syscall(long, ...);

static long sys(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

#ifdef SYS_accept
#define ACCEPT(fd) sys(SYS_accept, fd, 0, 0, 0, 0, 0)
#else
#define ACCEPT(fd) sys(SYS_accept4, fd, 0, 0, 0, 0, 0)
#endif

static void say(const char *label, int count, long a, long b, long c) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  long values[3] = {a, b, c};
  for (int index = 0; index < count; index++) {
    long value = values[index];
    line[n++] = ' ';
    if (value < 0) { line[n++] = '-'; value = -value; }
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + value % 10); value /= 10; } while (value);
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static void text(const char *label, const char *bytes, long size) {
  char line[128];
  size_t n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  for (long index = 0; index < size; index++) line[n++] = bytes[index] ? bytes[index] : '@';
  line[n++] = '\n';
  write(1, line, n);
}

static socklen_t named(struct sockaddr_un *address, const char *name, size_t size) {
  memset(address, 0, sizeof *address);
  address->sun_family = AF_UNIX;
  memcpy(address->sun_path, name, size);
  return offsetof(struct sockaddr_un, sun_path) + size;
}

int main(void) {
  char buffer[64];
  unlink("bap.sock");
  unlink("sender.sock");

  // A pair of streams: both ways, and the end when the other closes.
  int pair[2];
  say("pair", 1, sys(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, (long)pair, 0, 0), 0, 0);
  write(pair[0], "ping", 4);
  write(pair[0], "pong", 4);
  long got = read(pair[1], buffer, sizeof buffer);
  text("stream", buffer, got);
  write(pair[1], "back", 4);
  got = read(pair[0], buffer, 2);
  text("part", buffer, got);
  got = read(pair[0], buffer, sizeof buffer);
  text("rest", buffer, got);
  close(pair[0]);
  say("end", 1, read(pair[1], buffer, sizeof buffer), 0, 0);
  say("closed peer", 1, sys(SYS_sendto, pair[1], (long)"x", 1, MSG_NOSIGNAL, 0, 0), 0, 0);
  close(pair[1]);

  // Nothing to read yet, without waiting, and a shutdown that ends it.
  say("pair", 1, sys(SYS_socketpair, AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK, 0, (long)pair, 0, 0), 0, 0);
  say("again", 1, read(pair[0], buffer, sizeof buffer) < 0 ? -errno : 0, 0, 0);
  say("shutdown", 1, sys(SYS_shutdown, pair[1], SHUT_WR, 0, 0, 0, 0), 0, 0);
  say("shut end", 1, read(pair[0], buffer, sizeof buffer), 0, 0);
  close(pair[0]);
  close(pair[1]);

  // A listener at a path, and a child that connects to it.
  struct sockaddr_un address;
  socklen_t length = named(&address, "bap.sock", 9);
  int listener = sys(SYS_socket, AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, 0, 0, 0);
  say("bind", 1, sys(SYS_bind, listener, (long)&address, length, 0, 0, 0), 0, 0);
  say("bind again", 1, sys(SYS_bind, sys(SYS_socket, AF_UNIX, SOCK_STREAM, 0, 0, 0, 0), (long)&address, length, 0, 0, 0), 0, 0);
  int early = sys(SYS_socket, AF_UNIX, SOCK_STREAM, 0, 0, 0, 0);
  say("refused", 1, sys(SYS_connect, early, (long)&address, length, 0, 0, 0), 0, 0);
  say("listen", 1, sys(SYS_listen, listener, 4, 0, 0, 0, 0), 0, 0);
  int type = 0;
  socklen_t size = sizeof type;
  sys(SYS_getsockopt, listener, SOL_SOCKET, SO_TYPE, (long)&type, (long)&size, 0);
  int accepting = 0;
  sys(SYS_getsockopt, listener, SOL_SOCKET, SO_ACCEPTCONN, (long)&accepting, (long)&size, 0);
  say("options", 3, type == SOCK_STREAM, accepting, size);
  pid_t child = fork();
  if (child == 0) {
    int client = sys(SYS_socket, AF_UNIX, SOCK_STREAM, 0, 0, 0, 0);
    if (sys(SYS_connect, client, (long)&address, length, 0, 0, 0) != 0) _exit(3);
    write(client, "hello", 5);
    char answer[16];
    long n = read(client, answer, sizeof answer);
    _exit(n == 6 && memcmp(answer, "hello!", 6) == 0 ? 0 : 4);
  }
  int connection = ACCEPT(listener);
  got = read(connection, buffer, sizeof buffer);
  text("accepted", buffer, got);
  struct sockaddr_un name;
  socklen_t nameLength = sizeof name;
  sys(SYS_getsockname, connection, (long)&name, (long)&nameLength, 0, 0, 0);
  text("its name", name.sun_path, nameLength - offsetof(struct sockaddr_un, sun_path));
  nameLength = sizeof name;
  say("unnamed peer", 2, sys(SYS_getpeername, connection, (long)&name, (long)&nameLength, 0, 0, 0), nameLength, 0);
  struct ucred credentials;
  size = sizeof credentials;
  sys(SYS_getsockopt, connection, SOL_SOCKET, SO_PEERCRED, (long)&credentials, (long)&size, 0);
  say("peer process", 1, credentials.pid == child, 0, 0);
  write(connection, "hello!", 6);
  int status = 0;
  waitpid(child, &status, 0);
  say("child", 1, WEXITSTATUS(status), 0, 0);
  say("gone", 1, read(connection, buffer, sizeof buffer), 0, 0);
  close(connection);
  close(listener);
  say("missing", 1, sys(SYS_connect, early, (long)&address, named(&address, "none.sock", 10), 0, 0, 0), 0, 0);

  // Datagrams to a name of its own, from one that has a path.
  int server = sys(SYS_socket, AF_UNIX, SOCK_DGRAM, 0, 0, 0, 0);
  struct sockaddr_un abstract;
  socklen_t abstractLength = named(&abstract, "\0bap-datagrams", 14);
  say("abstract", 1, sys(SYS_bind, server, (long)&abstract, abstractLength, 0, 0, 0), 0, 0);
  int sender = sys(SYS_socket, AF_UNIX, SOCK_DGRAM, 0, 0, 0, 0);
  struct sockaddr_un from;
  socklen_t fromLength = named(&from, "sender.sock", 12);
  sys(SYS_bind, sender, (long)&from, fromLength, 0, 0, 0);
  sys(SYS_sendto, sender, (long)"one", 3, 0, (long)&abstract, abstractLength);
  sys(SYS_sendto, sender, (long)"three", 5, 0, (long)&abstract, abstractLength);
  struct sockaddr_un who;
  socklen_t whoLength = sizeof who;
  got = sys(SYS_recvfrom, server, (long)buffer, sizeof buffer, 0, (long)&who, (long)&whoLength);
  text("datagram", buffer, got);
  text("from", who.sun_path, whoLength - offsetof(struct sockaddr_un, sun_path));
  got = sys(SYS_recvfrom, server, (long)buffer, 2, MSG_TRUNC, 0, 0);
  say("truncated", 1, got, 0, 0);
  say("connect", 1, sys(SYS_connect, sender, (long)&abstract, abstractLength, 0, 0, 0), 0, 0);
  write(sender, "four", 4);
  got = read(server, buffer, sizeof buffer);
  text("connected", buffer, got);
  close(server);
  close(sender);

  // Packets keep their bounds.
  say("packets", 1, sys(SYS_socketpair, AF_UNIX, SOCK_SEQPACKET, 0, (long)pair, 0, 0), 0, 0);
  write(pair[0], "first", 5);
  write(pair[0], "second", 6);
  got = read(pair[1], buffer, sizeof buffer);
  text("packet", buffer, got);
  struct iovec piece = {buffer, 3};
  struct msghdr message = {0};
  message.msg_iov = &piece;
  message.msg_iovlen = 1;
  got = sys(SYS_recvmsg, pair[1], (long)&message, 0, 0, 0, 0);
  say("short", 2, got, (message.msg_flags & MSG_TRUNC) != 0, 0);
  close(pair[0]);
  close(pair[1]);

  // A descriptor handed over: the child writes to a pipe that it was given.
  int pipes[2];
  pipe(pipes);
  sys(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, (long)pair, 0, 0);
  child = fork();
  if (child == 0) {
    close(pipes[1]);
    char byte;
    struct iovec one = {&byte, 1};
    char control[CMSG_SPACE(sizeof(int))];
    struct msghdr received = {0};
    received.msg_iov = &one;
    received.msg_iovlen = 1;
    received.msg_control = control;
    received.msg_controllen = sizeof control;
    if (sys(SYS_recvmsg, pair[1], (long)&received, 0, 0, 0, 0) != 1) _exit(5);
    struct cmsghdr *header = CMSG_FIRSTHDR(&received);
    if (!header || header->cmsg_type != SCM_RIGHTS) _exit(6);
    int given;
    memcpy(&given, CMSG_DATA(header), sizeof given);
    write(given, "through", 7);
    _exit(0);
  }
  char byte = 'r';
  struct iovec one = {&byte, 1};
  union { char bytes[CMSG_SPACE(sizeof(int))]; struct cmsghdr align; } control;
  memset(&control, 0, sizeof control);
  struct msghdr handing = {0};
  handing.msg_iov = &one;
  handing.msg_iovlen = 1;
  handing.msg_control = control.bytes;
  handing.msg_controllen = sizeof control.bytes;
  struct cmsghdr *header = CMSG_FIRSTHDR(&handing);
  header->cmsg_level = SOL_SOCKET;
  header->cmsg_type = SCM_RIGHTS;
  header->cmsg_len = CMSG_LEN(sizeof(int));
  memcpy(CMSG_DATA(header), &pipes[1], sizeof(int));
  say("handed", 1, sys(SYS_sendmsg, pair[0], (long)&handing, 0, 0, 0, 0), 0, 0);
  close(pipes[1]);
  waitpid(child, &status, 0);
  say("child", 1, WEXITSTATUS(status), 0, 0);
  got = read(pipes[0], buffer, sizeof buffer);
  text("piped", buffer, got);

  // What isn't a socket, and what isn't of this domain.
  say("not a socket", 1, sys(SYS_listen, pipes[0], 1, 0, 0, 0, 0), 0, 0);
  unlink("bap.sock");
  unlink("sender.sock");
  return 0;
}
