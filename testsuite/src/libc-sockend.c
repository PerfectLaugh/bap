// How a connection ends and whom it is with: a listener closed with a connection that it never accepted, an end closed with what it
// hadn't read, what poll says then and of a socket that isn't connected, datagrams to a socket that is connected to another, and who
// the other end is. The libc of the tests has no sockets, so the calls are made by number.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <stddef.h>
#include <string.h>
#include <time.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

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

// The order of the network, which the libc of the tests leaves out.
static unsigned swap32(unsigned value) {
  unsigned short probe = 1;
  return *(unsigned char *)&probe ? __builtin_bswap32(value) : value;
}

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

static socklen_t named(struct sockaddr_un *address, const char *path) {
  memset(address, 0, sizeof *address);
  address->sun_family = AF_UNIX;
  size_t size = strlen(path);
  memcpy(address->sun_path, path, size);
  return offsetof(struct sockaddr_un, sun_path) + size + 1;
}

// What poll says of a descriptor that is asked whether it can be read or written, without waiting.
static long ready(int fd) {
  struct pollfd one = { fd, POLLIN | POLLOUT, 0 };
  struct timespec none = { 0, 0 };
  long count = sys(SYS_ppoll, (long)&one, 1, (long)&none, 0, 8, 0);
  return count < 0 ? count : one.revents;
}

static long readOne(int fd) {
  char byte;
  return sys(SYS_read, fd, (long)&byte, 1, 0, 0, 0);
}

// A byte that doesn't raise SIGPIPE when the other end is gone.
static long sendOne(int fd) {
  return sys(SYS_sendto, fd, (long)"x", 1, MSG_NOSIGNAL, 0, 0);
}

static int unixSocket(int type) { return (int)sys(SYS_socket, AF_UNIX, type, 0, 0, 0, 0); }

// The end of a reset connection: poll, a read that tells it, then the end of it, and a write.
static void reset(const char *label, int fd) {
  say(label, 3, ready(fd), readOne(fd), readOne(fd));
  say("  and a write", 1, sendOne(fd), 0, 0);
}

static void listenerClosed(int type, const char *path) {
  struct sockaddr_un address;
  socklen_t size = named(&address, path);
  int listener = unixSocket(type);
  sys(SYS_bind, listener, (long)&address, size, 0, 0, 0);
  sys(SYS_listen, listener, 4, 0, 0, 0, 0);
  int client = unixSocket(type);
  say("connect", 1, sys(SYS_connect, client, (long)&address, size, 0, 0, 0), 0, 0);
  say("  sends before it is accepted", 1, sendOne(client), 0, 0);
  close(listener);
  reset("  the listener closed", client);
  close(client);
  sys(SYS_unlinkat, AT_FDCWD, (long)path, 0, 0, 0, 0);
}

static void closedUnread(int type) {
  int pair[2];
  sys(SYS_socketpair, AF_UNIX, type, 0, (long)pair, 0, 0);
  sendOne(pair[0]);
  close(pair[1]);
  // Enough else let go of that what nothing holds may go.
  for (int index = 0; index < 300; index++) close((int)sys(SYS_dup, pair[0], 0, 0, 0, 0, 0));
  reset("the other end closed with what it hadn't read", pair[0]);
  close(pair[0]);
  sys(SYS_socketpair, AF_UNIX, type, 0, (long)pair, 0, 0);
  sendOne(pair[0]);
  readOne(pair[1]);
  close(pair[1]);
  say("and with nothing", 3, ready(pair[0]), readOne(pair[0]), sendOne(pair[0]));
  close(pair[0]);
}

static void tcp(void) {
  struct sockaddr_in address = { AF_INET, 0, { swap32(0x7f000001) } };
  socklen_t size = sizeof address;
  int listener = (int)sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
  sys(SYS_bind, listener, (long)&address, size, 0, 0, 0);
  sys(SYS_listen, listener, 4, 0, 0, 0, 0);
  sys(SYS_getsockname, listener, (long)&address, (long)&size, 0, 0, 0);
  int client = (int)sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
  say("tcp connect", 1, sys(SYS_connect, client, (long)&address, size, 0, 0, 0), 0, 0);
  int accepted = (int)ACCEPT(listener);
  sendOne(client);
  struct timespec moment = { 0, 20000000 };
  nanosleep(&moment, 0);
  close(accepted);
  nanosleep(&moment, 0);
  reset("  the other end closed with what it hadn't read", client);
  close(client);
  client = (int)sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
  say("tcp connect", 1, sys(SYS_connect, client, (long)&address, size, 0, 0, 0), 0, 0);
  close(listener);
  nanosleep(&moment, 0);
  reset("  the listener closed", client);
  close(client);
}

static void datagrams(void) {
  struct sockaddr_un one, other, third;
  socklen_t oneSize = named(&one, "sockend.d/one");
  socklen_t otherSize = named(&other, "sockend.d/other");
  socklen_t thirdSize = named(&third, "sockend.d/third");
  int a = unixSocket(SOCK_DGRAM), b = unixSocket(SOCK_DGRAM), c = unixSocket(SOCK_DGRAM);
  sys(SYS_bind, a, (long)&one, oneSize, 0, 0, 0);
  sys(SYS_bind, b, (long)&other, otherSize, 0, 0, 0);
  sys(SYS_bind, c, (long)&third, thirdSize, 0, 0, 0);
  sys(SYS_connect, a, (long)&other, otherSize, 0, 0, 0);
  say("a datagram to one connected to another", 1, sys(SYS_sendto, c, (long)"x", 1, 0, (long)&one, oneSize), 0, 0);
  say("and from that other", 1, sys(SYS_sendto, b, (long)"y", 1, 0, (long)&one, oneSize), 0, 0);
  char byte = 0;
  long first = sys(SYS_recvfrom, a, (long)&byte, 1, MSG_DONTWAIT, 0, 0);
  say("what it has", 3, first, byte, sys(SYS_recvfrom, a, (long)&byte, 1, MSG_DONTWAIT, 0, 0));
  close(a);
  close(b);
  close(c);
  sys(SYS_unlinkat, AT_FDCWD, (long)"sockend.d/one", 0, 0, 0, 0);
  sys(SYS_unlinkat, AT_FDCWD, (long)"sockend.d/other", 0, 0, 0, 0);
  sys(SYS_unlinkat, AT_FDCWD, (long)"sockend.d/third", 0, 0, 0, 0);
}

static void udp(void) {
  int a = (int)sys(SYS_socket, AF_INET, SOCK_DGRAM, 0, 0, 0, 0);
  int b = (int)sys(SYS_socket, AF_INET, SOCK_DGRAM, 0, 0, 0, 0);
  int c = (int)sys(SYS_socket, AF_INET, SOCK_DGRAM, 0, 0, 0, 0);
  struct sockaddr_in at[3];
  int fds[3] = {a, b, c};
  for (int index = 0; index < 3; index++) {
    struct sockaddr_in address = { AF_INET, 0, { swap32(0x7f000001) } };
    socklen_t size = sizeof address;
    sys(SYS_bind, fds[index], (long)&address, size, 0, 0, 0);
    sys(SYS_getsockname, fds[index], (long)&at[index], (long)&size, 0, 0, 0);
  }
  sys(SYS_connect, a, (long)&at[1], sizeof at[1], 0, 0, 0);
  say("udp from another than it is connected to", 1, sys(SYS_sendto, c, (long)"x", 1, 0, (long)&at[0], sizeof at[0]), 0, 0);
  say("and from that one", 1, sys(SYS_sendto, b, (long)"y", 1, 0, (long)&at[0], sizeof at[0]), 0, 0);
  struct timespec moment = { 0, 20000000 };
  nanosleep(&moment, 0);
  char byte = 0;
  long first = sys(SYS_recvfrom, a, (long)&byte, 1, MSG_DONTWAIT, 0, 0);
  say("what it has", 3, first, byte, sys(SYS_recvfrom, a, (long)&byte, 1, MSG_DONTWAIT, 0, 0));
  close(a);
  close(b);
  close(c);
}

// Whether SO_PEERCRED says this process, as it is now.
static void credentials(const char *label, int fd, long pid) {
  struct ucred cred;
  socklen_t size = sizeof cred;
  long result = sys(SYS_getsockopt, fd, SOL_SOCKET, SO_PEERCRED, (long)&cred, (long)&size, 0);
  say(label, 3, result, cred.pid == pid, cred.uid == sys(SYS_geteuid, 0, 0, 0, 0, 0, 0) && cred.gid == sys(SYS_getegid, 0, 0, 0, 0, 0, 0));
}

static void peers(void) {
  int pair[2];
  sys(SYS_socketpair, AF_UNIX, SOCK_STREAM, 0, (long)pair, 0, 0);
  credentials("the other of a pair", pair[0], getpid());
  close(pair[0]);
  close(pair[1]);
  int lone = unixSocket(SOCK_STREAM);
  struct ucred cred;
  socklen_t size = sizeof cred;
  long result = sys(SYS_getsockopt, lone, SOL_SOCKET, SO_PEERCRED, (long)&cred, (long)&size, 0);
  say("of one that isn't connected", 3, result, cred.pid, (long)(int)cred.uid);
  close(lone);
  struct sockaddr_un address;
  socklen_t addressSize = named(&address, "sockend.d/peers");
  int listener = unixSocket(SOCK_STREAM);
  sys(SYS_bind, listener, (long)&address, addressSize, 0, 0, 0);
  sys(SYS_listen, listener, 4, 0, 0, 0, 0);
  long parent = getpid();
  int child = fork();
  if (child == 0) {
    close(listener);
    int client = unixSocket(SOCK_STREAM);
    sys(SYS_connect, client, (long)&address, addressSize, 0, 0, 0);
    credentials("the listener, to the one that connects", client, parent);
    sendOne(client);
    readOne(client);
    _exit(0);
  }
  int accepted = (int)ACCEPT(listener);
  readOne(accepted);
  credentials("the one that connected, to the listener", accepted, child);
  close(accepted);
  waitpid(child, 0, 0);
  close(listener);
  sys(SYS_unlinkat, AT_FDCWD, (long)"sockend.d/peers", 0, 0, 0, 0);
}

int main(void) {
  sys(SYS_mkdirat, AT_FDCWD, (long)"sockend.d", 0700, 0, 0, 0);
  int lone = unixSocket(SOCK_STREAM);
  say("unconnected stream", 1, ready(lone), 0, 0);
  close(lone);
  listenerClosed(SOCK_STREAM, "sockend.d/stream");
  listenerClosed(SOCK_SEQPACKET, "sockend.d/packets");
  closedUnread(SOCK_STREAM);
  closedUnread(SOCK_SEQPACKET);
  tcp();
  datagrams();
  udp();
  peers();
  sys(SYS_unlinkat, AT_FDCWD, (long)"sockend.d", AT_REMOVEDIR, 0, 0, 0);
  return 0;
}
