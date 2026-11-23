// What Linux does that a review of the file side of the kernel found the machine didn't:
//   times: a directory is written when a name is made in it, removed from it or moved, and read when it is listed; what has a link
//     less, or moved, changed; and a write of nothing writes nothing.
//   rings: an entry of io_uring that can't read or write the memory it is given, or a time that isn't there, is its own EFAULT, and
//     the others go on; more vectors than UIO_MAXIOV is EINVAL, of AIO too; and a flag that there isn't is EINVAL.
//   descriptors: one below 0 is past any limit, EBADF of dup2 and dup3, and a descriptor is 32 bits of its register.
//   poll: an array that isn't all there is EFAULT with nothing written, and more than may be open is EINVAL.
//   locks: F_SETLKW for what waits for a lock of the process that asks is EDEADLK.
//   flags: one that there isn't is EINVAL of unlinkat, linkat, fstatat, statx, pipe2, splice, getrandom, timerfd_settime and TCFLSH.
//   sockets: a read of a stream stops after what came with descriptors; a stream sends nothing of nothing; MSG_WAITALL gives what
//     there is when its time is over; a socket of datagrams whose peer is gone has none; a listener takes its backlog and one more;
//     a name of two bytes asks for one; SO_PASSCRED says who sent; a path is made with the mask; and what is shut both ways hangs up.
//   pipes: one that nothing reads is still ready to write; O_DIRECT writes packets; nothing is sent from a pipe or a socket to a file,
//     nor spliced from a pipe to itself; a vector of a length below 0 is EINVAL; and epoll makes no loops, nor changes what is
//     exclusive.
//   and: a link more or less is said to the watch of the inode alone; a file of /proc is no directory; /proc is of proc; an empty path
//     is what a descriptor is open on, of readlinkat and faccessat2; fdinfo says O_CLOEXEC; a read that would end past 2^63 is
//     EINVAL; security.* takes CAP_SYS_ADMIN; and there are FIFOs, mknod, close_range and whiteouts.
// In a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <linux/aio_abi.h>
#include <linux/io_uring.h>
#include <poll.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/file.h>
#include <sys/inotify.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/sendfile.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/statfs.h>
#include <sys/syscall.h>
#include <sys/timerfd.h>
#include <sys/uio.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <sys/xattr.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

static char buf[8192];

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

/* times */

static const char *kinds[] = {"atime", "mtime", "ctime"};

static long long stamp(const char *path, int which) {
  struct stat s;
  if (lstat(path, &s)) return -1;
  struct timespec t = which == 0 ? s.st_atim : which == 1 ? s.st_mtim : s.st_ctim;
  return t.tv_sec * 1000000000LL + t.tv_nsec;
}

#define CHANGES(which, path, op)                                                                             \
  do {                                                                                                       \
    long long before = stamp(path, which);                                                                   \
    usleep(20000);                                                                                           \
    op;                                                                                                      \
    printf("%s: the %s of %s %s\n", #op, kinds[which], path, stamp(path, which) != before ? "changes" : "stays"); \
  } while (0)

static void list(const char *path) {
  DIR *d = opendir(path);
  readdir(d);
  closedir(d);
}

static void times(void) {
  mkdir("td", 0755);
  int f = open("t", O_CREAT | O_RDWR, 0644);
  CHANGES(1, "td", close(open("td/n", O_CREAT, 0644)));
  CHANGES(1, "td", close(open("td/n", O_CREAT | O_RDWR, 0644)));
  CHANGES(1, "td", rename("td/n", "td/m"));
  CHANGES(1, "td", link("td/m", "td/h"));
  CHANGES(2, "td/m", unlink("td/h"));
  CHANGES(1, "td", link("td/m", "td/h"));
  CHANGES(1, "td", unlink("td/h"));
  CHANGES(1, "td", mkdir("td/s", 0755));
  CHANGES(2, "td", rmdir("td/s"));
  CHANGES(1, "td", symlink("x", "td/l"));
  CHANGES(1, ".", rename("td/m", "out"));
  CHANGES(1, "td", rename("out", "td/m"));
  link("td/m", "td/k");
  CHANGES(2, "td/k", rename("td/m", "td/m2"));
  CHANGES(1, "td", unlink("nope"));
  CHANGES(0, "td", list("td"));
  CHANGES(0, "td", list("td"));
  CHANGES(1, "t", write(f, "", 0));
  CHANGES(1, "t", write(f, "a", 1));
  close(f);
}

/* io_uring and AIO */

static unsigned *sq_tail, *sq_mask, *sq_array, *cq_head, *cq_tail, *cq_mask;
static struct io_uring_sqe *sqes;
static struct io_uring_cqe *cqes;
static int ring;

static void submit(struct io_uring_sqe entry) {
  unsigned tail = *sq_tail;
  sqes[tail & *sq_mask] = entry;
  sq_array[tail & *sq_mask] = tail & *sq_mask;
  *sq_tail = tail + 1;
}

static void enter(const char *what) {
  long result = syscall(SYS_io_uring_enter, ring, 1, 1, IORING_ENTER_GETEVENTS, 0, 0);
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld submitted", what, result);
  while (*cq_head != *cq_tail) {
    struct io_uring_cqe *done = &cqes[*cq_head & *cq_mask];
    printf(", %llu gives %d", (unsigned long long)done->user_data, done->res);
    (*cq_head)++;
  }
  if (result >= 0) printf("\n");
}

static void rings(void) {
  static struct io_uring_params params;
  ring = syscall(SYS_io_uring_setup, 8, &params);
  if (ring < 0) {
    said("io_uring_setup", ring);
    return;
  }
  char *sq = mmap(0, params.sq_off.array + params.sq_entries * 4, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQ_RING);
  char *cq = mmap(0, params.cq_off.cqes + params.cq_entries * 16, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_CQ_RING);
  sqes = mmap(0, params.sq_entries * 64, PROT_READ | PROT_WRITE, MAP_SHARED, ring, IORING_OFF_SQES);
  sq_tail = (void *)(sq + params.sq_off.tail);
  sq_mask = (void *)(sq + params.sq_off.ring_mask);
  sq_array = (void *)(sq + params.sq_off.array);
  cq_head = (void *)(cq + params.cq_off.head);
  cq_tail = (void *)(cq + params.cq_off.tail);
  cq_mask = (void *)(cq + params.cq_off.ring_mask);
  cqes = (void *)(cq + params.cq_off.cqes);
  int f = open("ring", O_CREAT | O_RDWR, 0644);
  write(f, "0123456789", 10);
  struct iovec vector = {buf, 5};
  submit((struct io_uring_sqe){.opcode = IORING_OP_READ, .fd = f, .addr = 1, .len = 4, .off = 0, .user_data = 1});
  enter("a read to where nothing is");
  submit((struct io_uring_sqe){.opcode = IORING_OP_NOP, .user_data = 2});
  enter("nothing, after it");
  submit((struct io_uring_sqe){.opcode = IORING_OP_TIMEOUT, .addr = 1, .len = 1, .user_data = 3});
  enter("a timeout of a time that isn't there");
  submit((struct io_uring_sqe){.opcode = IORING_OP_READV, .fd = f, .addr = (unsigned long)&vector, .len = 0xffffffff, .off = 0, .user_data = 4});
  enter("a read of 2^32 vectors");
  submit((struct io_uring_sqe){.opcode = IORING_OP_READ, .fd = f, .addr = (unsigned long)buf, .len = 4, .off = 2, .user_data = 5});
  enter("a read");
  printf("  of %.4s\n", buf);
  said("io_uring_enter with a flag that there isn't", syscall(SYS_io_uring_enter, ring, 0, 0, 0x1000, 0, 0));
  static struct io_uring_params other;
  other.flags = 0x80000000;
  said("io_uring_setup with a flag that there isn't", syscall(SYS_io_uring_setup, 4, &other));
  aio_context_t context = 0;
  said("io_setup", syscall(SYS_io_setup, 4, &context));
  static struct iovec many[2000];
  struct iocb block = {.aio_lio_opcode = IOCB_CMD_PREADV, .aio_fildes = f, .aio_buf = (unsigned long)many, .aio_nbytes = 2000};
  struct iocb *blocks[1] = {&block};
  said("io_submit of 2000 vectors", syscall(SYS_io_submit, context, 1, blocks));
  close(f);
  close(ring);
}

/* descriptors */

static void descriptors(void) {
  said("dup2 to -1", dup2(1, -1));
  said("close of -1", close(-1));
  said("dup3 to -5", dup3(1, -5, 0));
  said("F_GETFD of -5", fcntl(-5, F_GETFD));
  if (sizeof(long) == 8) said("F_GETFD of 1 and 2^32", syscall(SYS_fcntl, (long)0x100000001LL, F_GETFD));
  else printf("F_GETFD of 1 and 2^32: 0\n");
}

/* poll */

static void polls(void) {
  char *pages = mmap(0, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  munmap(pages + 4096, 4096);
  struct pollfd *fds = (struct pollfd *)(pages + 4096 - 100 * sizeof(struct pollfd));
  for (int i = 0; i < 100; i++) fds[i] = (struct pollfd){-1, 0, 0x7777};
  said("poll of an array that isn't all there", poll(fds, 101, 0));
  printf("  which leaves %x and %x\n", fds[0].revents, fds[99].revents);
  said("poll of more than may be open", poll(fds, -1, 0));
  said("poll of what is there", poll(fds, 100, 0));
  printf("  which leaves %x and %x\n", fds[0].revents, fds[99].revents);
}

/* locks */

static int lock(int fd, int command, int type, long start, long length) {
  struct flock range = {.l_type = type, .l_whence = SEEK_SET, .l_start = start, .l_len = length};
  return fcntl(fd, command, &range);
}

static void locks(void) {
  int f = open("locked", O_CREAT | O_RDWR, 0644), p[2], status = 0;
  char byte;
  write(f, "ab", 2);
  pipe(p);
  lock(f, F_SETLK, F_WRLCK, 0, 1);
  pid_t child = fork();
  if (child == 0) {
    lock(f, F_SETLK, F_WRLCK, 1, 1);
    write(p[1], "x", 1);
    _exit(lock(f, F_SETLKW, F_WRLCK, 0, 1) == 0 ? 0 : errno);
  }
  read(p[0], &byte, 1);
  usleep(50000);
  said("F_SETLKW for what waits for a lock of ours", lock(f, F_SETLKW, F_WRLCK, 1, 1));
  lock(f, F_SETLK, F_UNLCK, 0, 1);
  waitpid(child, &status, 0);
  printf("  and the other has what it waited for: %d\n", WEXITSTATUS(status));
  close(f);
  close(p[0]);
  close(p[1]);
}

/* flags */

static void flags(void) {
  int p[2];
  struct stat st;
  struct statx sx;
  close(open("flagged", O_CREAT, 0644));
  said("unlinkat with a flag that there isn't", unlinkat(AT_FDCWD, "flagged", 0x1000));
  said("  which leaves it", access("flagged", F_OK));
  said("linkat with a flag that there isn't", linkat(AT_FDCWD, "flagged", AT_FDCWD, "flagged2", 0x1));
  said("fstatat with a flag that there isn't", fstatat(AT_FDCWD, "flagged", &st, 0x8000));
  said("statx with both ways of how fresh", syscall(SYS_statx, AT_FDCWD, "flagged", 0x6000, 0x7ff, &sx));
  said("statx with a flag that there isn't", syscall(SYS_statx, AT_FDCWD, "flagged", 0x10000, 0x7ff, &sx));
  said("statx with a mask of what is reserved", syscall(SYS_statx, AT_FDCWD, "flagged", 0, 0x80000000u, &sx));
  said("statx", syscall(SYS_statx, AT_FDCWD, "flagged", 0x2000, 0x7ff, &sx));
  said("pipe2 with a flag that there isn't", pipe2(p, 0x1));
  pipe(p);
  int out = open("flagged", O_WRONLY);
  write(p[1], "abc", 3);
  said("splice with a flag that there isn't", splice(p[0], 0, out, 0, 3, 16));
  said("getrandom with a flag that there isn't", syscall(SYS_getrandom, buf, 1, 8));
  int timer = timerfd_create(CLOCK_MONOTONIC, 0);
  struct itimerspec span = {{0, 0}, {1, 0}};
  said("timerfd_settime with a flag that there isn't", timerfd_settime(timer, 4, &span, 0));
  int master = posix_openpt(O_RDWR | O_NOCTTY);
  said("tcflush of a queue that there isn't", tcflush(master, 9));
  said("tcflush", tcflush(master, TCIOFLUSH));
  close(master);
  close(timer);
  close(out);
  close(p[0]);
  close(p[1]);
}

/* sockets */

static long with_descriptor(int to, const char *bytes, int count, int descriptor) {
  char control[CMSG_SPACE(sizeof(int))];
  struct iovec vector = {(void *)bytes, count};
  struct msghdr message = {.msg_iov = &vector, .msg_iovlen = 1, .msg_control = control, .msg_controllen = sizeof control};
  struct cmsghdr *header = CMSG_FIRSTHDR(&message);
  header->cmsg_level = SOL_SOCKET;
  header->cmsg_type = SCM_RIGHTS;
  header->cmsg_len = CMSG_LEN(sizeof(int));
  memcpy(CMSG_DATA(header), &descriptor, sizeof(int));
  return sendmsg(to, &message, 0);
}

static void received(const char *what, int from) {
  char control[256];
  struct iovec vector = {buf, 10};
  struct msghdr message = {.msg_iov = &vector, .msg_iovlen = 1, .msg_control = control, .msg_controllen = sizeof control};
  long count = recvmsg(from, &message, 0);
  if (count < 0) {
    printf("%s: %s\n", what, strerror(errno));
    return;
  }
  printf("%s: %ld", what, count);
  for (struct cmsghdr *header = CMSG_FIRSTHDR(&message); header; header = CMSG_NXTHDR(&message, header)) {
    if (header->cmsg_type == SCM_RIGHTS) {
      int descriptor;
      memcpy(&descriptor, CMSG_DATA(header), sizeof(int));
      printf(", with a descriptor");
      close(descriptor);
    } else if (header->cmsg_type == SCM_CREDENTIALS) {
      struct ucred who;
      memcpy(&who, CMSG_DATA(header), sizeof who);
      printf(", of type %d and length %d, from %s, user %d, group %d", header->cmsg_type, (int)(header->cmsg_len - CMSG_LEN(0)),
             who.pid == getpid() ? "us" : "another", (int)who.uid, (int)who.gid);
    }
  }
  printf("\n");
}

static void sockets(void) {
  int sv[2];
  struct stat st;
  socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
  said("two bytes with a descriptor", with_descriptor(sv[0], "ab", 2, 1));
  write(sv[0], "cd", 2);
  received("  are read", sv[1]);
  said("  before the two after them", read(sv[1], buf, 10));
  write(sv[0], "ef", 2);
  said("two bytes more with a descriptor", with_descriptor(sv[0], "gh", 2, 1));
  write(sv[0], "ij", 2);
  received("  are read with the two before them", sv[1]);
  said("  before the two after them", read(sv[1], buf, 10));
  said("nothing with a descriptor", with_descriptor(sv[0], "", 0, 1));
  write(sv[0], "e", 1);
  received("  is nothing, before a byte", sv[1]);
  struct timeval span = {0, 20000};
  setsockopt(sv[1], SOL_SOCKET, SO_RCVTIMEO, &span, sizeof span);
  write(sv[0], "abc", 3);
  said("MSG_WAITALL of 10 bytes with 3 there and a time", recv(sv[1], buf, 10, MSG_WAITALL));
  said("  and then", recv(sv[1], buf, 10, MSG_WAITALL));
  close(sv[0]);
  close(sv[1]);

  int a = socket(AF_UNIX, SOCK_DGRAM | SOCK_NONBLOCK, 0), b = socket(AF_UNIX, SOCK_DGRAM | SOCK_NONBLOCK, 0);
  int c = socket(AF_UNIX, SOCK_DGRAM | SOCK_NONBLOCK, 0);
  struct sockaddr_un at_a = {AF_UNIX, "da"}, at_b = {AF_UNIX, "db"};
  umask(022);
  said("bind", bind(a, (void *)&at_a, sizeof at_a));
  stat("da", &st);
  printf("  of mode %o\n", (unsigned)st.st_mode);
  bind(b, (void *)&at_b, sizeof at_b);
  said("connect", connect(b, (void *)&at_a, sizeof at_a));
  said("a datagram from another to what is connected", sendto(c, "z", 1, 0, (void *)&at_b, sizeof at_b));
  close(a);
  said("a datagram to a peer that is gone", send(b, "x", 1, 0));
  said("  and another", send(b, "x", 1, 0));
  said("a datagram from another to what was connected", sendto(c, "z", 1, 0, (void *)&at_b, sizeof at_b));
  said("  which comes", recv(b, buf, 10, 0));
  close(b);
  close(c);

  struct sockaddr_un named;
  memset(&named, 0, sizeof named);
  named.sun_family = AF_UNIX;
  memcpy(named.sun_path, "\0r25", 4);
  int listener = socket(AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK, 0);
  bind(listener, (void *)&named, 2 + 4);
  said("listen with a backlog of 1", listen(listener, 1));
  int clients[3];
  for (int i = 0; i < 3; i++) {
    clients[i] = socket(AF_UNIX, SOCK_STREAM | SOCK_NONBLOCK, 0);
    said("  connect", connect(clients[i], (void *)&named, 2 + 4));
  }
  int accepted = accept(listener, 0, 0);
  said("  and once one is accepted", connect(clients[2], (void *)&named, 2 + 4));
  for (int i = 0; i < 3; i++) close(clients[i]);
  close(accepted);
  close(listener);

  int unnamed = socket(AF_UNIX, SOCK_STREAM, 0);
  struct sockaddr_un got;
  socklen_t length = sizeof got;
  said("bind to a name of two bytes", bind(unnamed, (void *)&named, 2));
  getsockname(unnamed, (void *)&got, &length);
  printf("  which is of %d bytes, the first of them %d\n", (int)length, got.sun_path[0]);
  close(unnamed);

  socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
  int one = 1;
  said("SO_PASSCRED", setsockopt(sv[1], SOL_SOCKET, SO_PASSCRED, &one, sizeof one));
  write(sv[0], "x", 1);
  received("  of a byte", sv[1]);
  close(sv[0]);
  close(sv[1]);

  socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
  shutdown(sv[0], SHUT_WR);
  shutdown(sv[0], SHUT_RD);
  struct pollfd both[2] = {{sv[0], POLLIN | POLLOUT | POLLRDHUP, 0}, {sv[1], POLLIN | POLLOUT | POLLRDHUP, 0}};
  poll(both, 2, 0);
  printf("what is shut both ways is ready of %x, and its other end of %x\n", both[0].revents, both[1].revents);
  close(sv[0]);
  close(sv[1]);
}

/* pipes and epoll */

static int control(int instance, int operation, int descriptor, unsigned events) {
  struct epoll_event event = {events, {.u64 = 7}};
  return epoll_ctl(instance, operation, descriptor, &event);
}

static void pipes(void) {
  int p[2], q[2], sv[2];
  pipe(p);
  close(p[0]);
  struct pollfd writer = {p[1], POLLOUT, 0};
  poll(&writer, 1, 0);
  printf("a pipe that nothing reads is ready of %x\n", writer.revents);
  close(p[1]);

  said("pipe2 with O_DIRECT", pipe2(q, O_DIRECT));
  write(q[1], "abc", 3);
  write(q[1], "defg", 4);
  said("  of a packet of 3, 2 are read", read(q[0], buf, 2));
  said("  and then", read(q[0], buf, 100));
  close(q[0]);
  close(q[1]);

  int out = open("sent", O_CREAT | O_RDWR, 0644);
  pipe(p);
  write(p[1], "hello", 5);
  socketpair(AF_UNIX, SOCK_STREAM, 0, sv);
  write(sv[0], "12345678", 8);
  said("sendfile from a pipe", sendfile(out, p[0], 0, 3));
  said("sendfile from a socket", sendfile(out, sv[1], 0, 4));
  said("splice from a pipe to itself", splice(p[0], 0, p[1], 0, 3, 0));
  said("  which still has", read(p[0], buf, 10));
  said("  and the socket", read(sv[1], buf, 10));
  write(out, "0123456789", 10);
  lseek(out, 0, SEEK_SET);
  struct iovec vectors[3] = {{buf, 2}, {buf + 2, -1}, {buf + 4, 2}};
  said("readv with a length below 0", readv(out, vectors, 3));
  said("  which leaves it at", lseek(out, 0, SEEK_CUR));
  close(out);
  close(sv[0]);
  close(sv[1]);

  int first = epoll_create1(0), second = epoll_create1(0), third = epoll_create1(0);
  said("an epoll in another", control(first, EPOLL_CTL_ADD, second, EPOLLIN));
  said("  and that one in it", control(second, EPOLL_CTL_ADD, first, EPOLLIN));
  said("an exclusive entry", control(third, EPOLL_CTL_ADD, p[1], EPOLLOUT | EPOLLEXCLUSIVE));
  said("  changed", control(third, EPOLL_CTL_MOD, p[1], EPOLLOUT));
  said("an exclusive entry of an epoll", control(third, EPOLL_CTL_ADD, first, EPOLLIN | EPOLLEXCLUSIVE));
  close(first);
  close(second);
  close(third);
  close(p[0]);
  close(p[1]);
}

/* the others */

static void others(void) {
  mkdir("w", 0755);
  close(open("w/b", O_CREAT, 0644));
  int notes = inotify_init1(IN_NONBLOCK);
  inotify_add_watch(notes, "w", IN_ALL_EVENTS);
  link("w/b", "w/c");
  unlink("w/b");
  long count = read(notes, buf, sizeof buf);
  printf("a link and an unlink say");
  for (long at = 0; at < count;) {
    struct inotify_event *event = (void *)(buf + at);
    printf(" %x of %s", event->mask, event->len ? event->name : "itself");
    at += sizeof *event + event->len;
  }
  printf("\n");
  close(notes);

  said("a file of /proc as a directory", open("/proc/self/maps", O_RDONLY | O_DIRECTORY));
  struct statfs fs;
  statfs("/proc", &fs);
  printf("/proc is of %lx\n", (unsigned long)fs.f_type);

  symlink("target", "sl");
  int named = open("sl", O_PATH | O_NOFOLLOW);
  long length = readlinkat(named, "", buf, 100);
  said("readlinkat of no path", length);
  if (length > 0) printf("  which is %.*s\n", (int)length, buf);
  int here = open(".", O_RDONLY);
  said("  and of a directory", readlinkat(here, "", buf, 100));
  said("faccessat2 of no path", syscall(SYS_faccessat2, here, "", F_OK, AT_EMPTY_PATH));
  close(named);
  close(here);

  int closing = open("own", O_CREAT | O_RDONLY | O_CLOEXEC, 0644);
  char path[64];
  snprintf(path, sizeof path, "/proc/self/fdinfo/%d", closing);
  int info = open(path, O_RDONLY);
  count = read(info, buf, sizeof buf - 1);
  buf[count > 0 ? count : 0] = 0;
  char *line = strstr(buf, "flags:");
  printf("fdinfo of what execve closes %s\n", line && (strtoul(line + 6, 0, 8) & O_CLOEXEC) ? "says so" : "doesn't say so");
  close(info);

  said("a seek to the last byte there can be", lseek(closing, 0x7fffffffffffffffLL, SEEK_SET) > 0);
  said("  and a read there", read(closing, buf, 1));
  said("  and of nothing", read(closing, buf, 0));
  close(closing);

  if (fork() == 0) {
    /* Without CAP_SYS_ADMIN. */
    struct { unsigned version; int pid; } header = {0x20080522, 0};
    struct { unsigned effective, permitted, inheritable; } data[2];
    syscall(SYS_capget, &header, data);
    data[0].effective &= ~(1u << 21);
    syscall(SYS_capset, &header, data);
    said("security.* without CAP_SYS_ADMIN", setxattr("own", "security.review", "1", 1, 0));
    said("  and user.*", setxattr("own", "user.review", "1", 1, 0));
    fflush(stdout);
    _exit(0);
  }
  wait(0);
}

/* what wasn't there */

static void made(void) {
  struct stat st;
  int status = 0;
  umask(022);
  said("mkfifo", mkfifo("fifo", 0666));
  stat("fifo", &st);
  printf("  of mode %o\n", (unsigned)st.st_mode);
  said("  and again", mkfifo("fifo", 0666));
  said("mknod of a file", mknod("plain", S_IFREG | 0600, 0));
  stat("plain", &st);
  printf("  of mode %o and %ld bytes\n", (unsigned)st.st_mode, (long)st.st_size);
  said("mknod of a directory", mknod("no", S_IFDIR | 0700, 0));
  said("mknodat of a FIFO", mknodat(AT_FDCWD, "td/fifo", S_IFIFO | 0600, 0));
  said("a FIFO that nothing reads, to write without waiting", open("fifo", O_WRONLY | O_NONBLOCK));
  int reader = open("fifo", O_RDONLY | O_NONBLOCK);
  said("  to read", reader >= 0);
  int writer = open("fifo", O_WRONLY | O_NONBLOCK);
  said("  and then to write", writer >= 0);
  said("  what is written", write(writer, "hi", 2));
  said("  is read", read(reader, buf, 10));
  close(reader);
  close(writer);
  pid_t child = fork();
  if (child == 0) {
    int to = open("fifo", O_WRONLY);
    write(to, "there", 5);
    close(to);
    _exit(to >= 0 ? 0 : 1);
  }
  int from = open("fifo", O_RDONLY);
  long total = 0, count;
  while (total < 5 && (count = read(from, buf + total, 5 - total)) > 0) total += count;
  printf("a FIFO that a child writes gives %.*s\n", (int)total, buf);
  close(from);
  waitpid(child, &status, 0);
  printf("  which ends with %d\n", WEXITSTATUS(status));
  child = fork();
  if (child == 0) {
    int back = open("fifo", O_RDONLY);
    count = read(back, buf, 10);
    _exit(count == 4 ? 0 : 1);
  }
  usleep(20000);
  int to = open("fifo", O_WRONLY);
  said("a FIFO that a child reads takes", write(to, "back", 4));
  close(to);
  waitpid(child, &status, 0);
  printf("  which ends with %d\n", WEXITSTATUS(status));

  for (int fd = 100; fd < 103; fd++) dup2(1, fd);
  said("close_range of a range that ends before it starts", syscall(SYS_close_range, 100, 50, 0));
  said("close_range with a flag that there isn't", syscall(SYS_close_range, 100, ~0U, 8));
  said("close_range with CLOSE_RANGE_CLOEXEC", syscall(SYS_close_range, 101, ~0U, 4));
  said("  which leaves 100 with", fcntl(100, F_GETFD));
  said("  and 102 with", fcntl(102, F_GETFD));
  said("close_range", syscall(SYS_close_range, 101, ~0U, 0));
  said("  which leaves 100", fcntl(100, F_GETFD));
  said("  and 101", fcntl(101, F_GETFD));
  close(100);

  close(open("moved", O_CREAT, 0644));
  said("renameat2 with RENAME_WHITEOUT", syscall(SYS_renameat2, AT_FDCWD, "moved", AT_FDCWD, "there", 4));
  said("  which leaves", stat("moved", &st));
  printf("  of mode %o and device %lx\n", (unsigned)st.st_mode, (unsigned long)st.st_rdev);
  said("  and what moved", access("there", F_OK));
}

static void remove_all(void) {
  const char *files[] = {"t", "own", "td/m2", "td/k", "td/l", "td/fifo", "ring", "locked", "flagged", "da", "db", "sent", "w/c", "sl", "fifo",
                         "plain", "moved", "there"};
  for (unsigned i = 0; i < sizeof files / sizeof *files; i++) unlink(files[i]);
  rmdir("td");
  rmdir("w");
}

/* All of it, or of an argument, the parts that its letters say. */
int main(int argc, char **argv) {
  const char *parts = argc > 1 ? argv[1] : "trdplfseom";
  setvbuf(stdout, 0, _IONBF, 0);
  signal(SIGPIPE, SIG_IGN);
  mkdir("review25.d", 0755);
  if (chdir("review25.d")) return 1;
  umask(022);
  for (const char *part = parts; *part; part++) {
    if (*part == 't') times();
    if (*part == 'r') rings();
    if (*part == 'd') descriptors();
    if (*part == 'p') polls();
    if (*part == 'l') locks();
    if (*part == 'f') flags();
    if (*part == 's') sockets();
    if (*part == 'e') pipes();
    if (*part == 'o') others();
    if (*part == 'm') made();
  }
  remove_all();
  chdir("..");
  said("and all of it is taken away", rmdir("review25.d"));
  return 0;
}
