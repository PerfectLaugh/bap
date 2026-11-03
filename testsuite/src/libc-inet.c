// Sockets of the Internet on the loopback: TCP between processes, UDP with who sent it, IPv6, and what goes wrong. The ports are
// the system's, so what is said of them is only whether they are what they should be. The libc of the tests has no sockets, so the
// calls are made by number.
#define _GNU_SOURCE
#include <errno.h>
#include <stddef.h>
#include <string.h>
#include <netinet/in.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <sys/wait.h>
#include <unistd.h>

long syscall(long, ...);

// The order of the network, which the libc of the tests leaves out.
#undef htons
#undef htonl
#undef ntohs
#undef ntohl
static unsigned short swap16(unsigned short value) {
  unsigned short probe = 1;
  return *(unsigned char *)&probe ? (unsigned short)(value << 8 | value >> 8) : value;
}
static unsigned swap32(unsigned value) {
  unsigned short probe = 1;
  return *(unsigned char *)&probe ? __builtin_bswap32(value) : value;
}
#define htons swap16
#define ntohs swap16
#define htonl swap32
#define ntohl swap32

static const struct in6_addr loopback6 = {{{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1}}};
#define in6addr_loopback loopback6

static long sys(long number, long a, long b, long c, long d, long e, long f) {
  long result = syscall(number, a, b, c, d, e, f);
  return result < 0 ? -errno : result;
}

#ifdef SYS_accept
#define ACCEPT(fd, address, length) sys(SYS_accept, fd, (long)(address), (long)(length), 0, 0, 0)
#else
#define ACCEPT(fd, address, length) sys(SYS_accept4, fd, (long)(address), (long)(length), 0, 0, 0)
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
  for (long index = 0; index < size && index < 100; index++) line[n++] = bytes[index];
  line[n++] = '\n';
  write(1, line, n);
}

static struct sockaddr_in at(unsigned address, unsigned short port) {
  struct sockaddr_in name;
  memset(&name, 0, sizeof name);
  name.sin_family = AF_INET;
  name.sin_port = htons(port);
  name.sin_addr.s_addr = htonl(address);
  return name;
}

static unsigned short portOf(int fd) {
  struct sockaddr_in name;
  socklen_t length = sizeof name;
  sys(SYS_getsockname, fd, (long)&name, (long)&length, 0, 0, 0);
  return ntohs(name.sin_port);
}

int main(void) {
  char buffer[64];
  int status = 0;

  // TCP: a listener on the loopback, and a child that connects to it.
  int listener = sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
  int one = 1;
  say("reuse", 1, sys(SYS_setsockopt, listener, SOL_SOCKET, SO_REUSEADDR, (long)&one, sizeof one, 0), 0, 0);
  struct sockaddr_in local = at(INADDR_LOOPBACK, 0);
  say("bind", 1, sys(SYS_bind, listener, (long)&local, sizeof local, 0, 0, 0), 0, 0);
  unsigned short port = portOf(listener);
  say("port", 1, port != 0, 0, 0);
  struct sockaddr_in same = at(INADDR_LOOPBACK, port);
  say("in use", 1, sys(SYS_bind, sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0), (long)&same, sizeof same, 0, 0, 0), 0, 0);
  say("listen", 1, sys(SYS_listen, listener, 8, 0, 0, 0, 0), 0, 0);
  int type = 0, protocol = 0, domain = 0;
  socklen_t size = sizeof type;
  sys(SYS_getsockopt, listener, SOL_SOCKET, SO_TYPE, (long)&type, (long)&size, 0);
  sys(SYS_getsockopt, listener, SOL_SOCKET, SO_PROTOCOL, (long)&protocol, (long)&size, 0);
  sys(SYS_getsockopt, listener, SOL_SOCKET, SO_DOMAIN, (long)&domain, (long)&size, 0);
  say("options", 3, type == SOCK_STREAM, protocol, domain);
  int nonblocking = sys(SYS_socket, AF_INET, SOCK_STREAM | SOCK_NONBLOCK, 0, 0, 0, 0);
  struct sockaddr_in any = at(INADDR_ANY, 0);
  sys(SYS_bind, nonblocking, (long)&any, sizeof any, 0, 0, 0);
  sys(SYS_listen, nonblocking, 1, 0, 0, 0, 0);
  say("nothing to accept", 1, ACCEPT(nonblocking, 0, 0), 0, 0);
  pid_t child = fork();
  if (child == 0) {
    int client = sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
    struct sockaddr_in server = at(INADDR_LOOPBACK, port);
    if (sys(SYS_connect, client, (long)&server, sizeof server, 0, 0, 0) != 0) _exit(3);
    write(client, "hello over tcp", 14);
    char answer[16];
    long n = read(client, answer, sizeof answer);
    if (n != 3 || memcmp(answer, "ack", 3) != 0) _exit(4);
    sys(SYS_shutdown, client, SHUT_WR, 0, 0, 0, 0);
    n = read(client, answer, sizeof answer);
    _exit(n == 0 ? 0 : 5);
  }
  struct sockaddr_in peer;
  socklen_t peerLength = sizeof peer;
  int connection = ACCEPT(listener, &peer, &peerLength);
  say("peer", 3, peerLength, ntohl(peer.sin_addr.s_addr) == INADDR_LOOPBACK, peer.sin_port != 0 && ntohs(peer.sin_port) != port);
  struct sockaddr_in mine;
  socklen_t mineLength = sizeof mine;
  sys(SYS_getsockname, connection, (long)&mine, (long)&mineLength, 0, 0, 0);
  say("its end", 2, ntohl(mine.sin_addr.s_addr) == INADDR_LOOPBACK, ntohs(mine.sin_port) == port, 0);
  struct sockaddr_in other;
  socklen_t otherLength = sizeof other;
  sys(SYS_getpeername, connection, (long)&other, (long)&otherLength, 0, 0, 0);
  say("same peer", 1, other.sin_port == peer.sin_port, 0, 0);
  long got = read(connection, buffer, sizeof buffer);
  text("tcp", buffer, got);
  write(connection, "ack", 3);
  say("end", 1, read(connection, buffer, sizeof buffer), 0, 0);
  close(connection);
  waitpid(child, &status, 0);
  say("child", 1, WEXITSTATUS(status), 0, 0);
  close(listener);
  int refused = sys(SYS_socket, AF_INET, SOCK_STREAM, 0, 0, 0, 0);
  say("refused", 1, sys(SYS_connect, refused, (long)&same, sizeof same, 0, 0, 0), 0, 0);
  struct sockaddr_in elsewhere = at(0x0a010203, 0);
  say("not here", 1, sys(SYS_bind, refused, (long)&elsewhere, sizeof elsewhere, 0, 0, 0), 0, 0);

  // UDP: who sent it, its bounds, and a socket that is connected.
  int server = sys(SYS_socket, AF_INET, SOCK_DGRAM, 0, 0, 0, 0);
  sys(SYS_bind, server, (long)&local, sizeof local, 0, 0, 0);
  struct sockaddr_in serverName = at(INADDR_LOOPBACK, portOf(server));
  int client = sys(SYS_socket, AF_INET, SOCK_DGRAM, 0, 0, 0, 0);
  say("sent", 1, sys(SYS_sendto, client, (long)"first", 5, 0, (long)&serverName, sizeof serverName), 0, 0);
  sys(SYS_sendto, client, (long)"second one", 10, 0, (long)&serverName, sizeof serverName);
  struct sockaddr_in from;
  socklen_t fromLength = sizeof from;
  got = sys(SYS_recvfrom, server, (long)buffer, sizeof buffer, 0, (long)&from, (long)&fromLength);
  text("udp", buffer, got);
  say("from", 3, fromLength, ntohl(from.sin_addr.s_addr) == INADDR_LOOPBACK, ntohs(from.sin_port) == portOf(client));
  say("truncated", 1, sys(SYS_recvfrom, server, (long)buffer, 3, MSG_TRUNC, 0, 0), 0, 0);
  say("connect", 1, sys(SYS_connect, client, (long)&serverName, sizeof serverName, 0, 0, 0), 0, 0);
  write(client, "connected", 9);
  got = read(server, buffer, sizeof buffer);
  text("udp", buffer, got);
  struct sockaddr_in nobody = at(INADDR_LOOPBACK, port);
  say("to nobody", 1, sys(SYS_sendto, server, (long)"lost", 4, 0, (long)&nobody, sizeof nobody), 0, 0);
  int unbound = sys(SYS_socket, AF_INET, SOCK_DGRAM | SOCK_NONBLOCK, 0, 0, 0, 0);
  sys(SYS_bind, unbound, (long)&local, sizeof local, 0, 0, 0);
  say("nothing yet", 1, sys(SYS_recvfrom, unbound, (long)buffer, sizeof buffer, 0, 0, 0), 0, 0);
  say("no address", 1, sys(SYS_sendto, unbound, (long)"x", 1, 0, 0, 0), 0, 0);

  // IPv6 on its loopback.
  int listener6 = sys(SYS_socket, AF_INET6, SOCK_STREAM, 0, 0, 0, 0);
  struct sockaddr_in6 local6;
  memset(&local6, 0, sizeof local6);
  local6.sin6_family = AF_INET6;
  local6.sin6_addr = in6addr_loopback;
  say("bind6", 1, sys(SYS_bind, listener6, (long)&local6, sizeof local6, 0, 0, 0), 0, 0);
  sys(SYS_listen, listener6, 1, 0, 0, 0, 0);
  socklen_t length6 = sizeof local6;
  sys(SYS_getsockname, listener6, (long)&local6, (long)&length6, 0, 0, 0);
  int client6 = sys(SYS_socket, AF_INET6, SOCK_STREAM, 0, 0, 0, 0);
  say("connect6", 1, sys(SYS_connect, client6, (long)&local6, sizeof local6, 0, 0, 0), 0, 0);
  struct sockaddr_in6 peer6;
  socklen_t peer6Length = sizeof peer6;
  int connection6 = ACCEPT(listener6, &peer6, &peer6Length);
  say("peer6", 2, peer6Length, memcmp(&peer6.sin6_addr, &in6addr_loopback, 16) == 0, 0);
  write(client6, "six", 3);
  got = read(connection6, buffer, sizeof buffer);
  text("tcp6", buffer, got);
  return 0;
}
