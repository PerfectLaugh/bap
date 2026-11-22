// What Linux does that a review of the model of ptrace, seccomp, paths and inotify found the machine didn't:
//   stops: a tracee that stops at the start of a system call is after its instruction, as at its end, so that a tracer that takes the
//     instruction off the pc at the end makes the call again; PTRACE_GET_SYSCALL_INFO says the architecture and the stack pointer;
//     a step from the start of a call stops at its end with TRAP_BRKPT, and one of an instruction with TRAP_TRACE; and a signal
//     that there isn't is EIO to go on with.
//   left: a call that a tracee waits in, which it left for a stop of PTRACE_INTERRUPT or of a signal, is seen with its number and
//     with ERESTARTSYS, or ERESTART_RESTARTBLOCK of a sleep, after its instruction; and the signal of PTRACE_DETACH from a stop
//     that isn't of a signal isn't sent.
//   threads: a traced thread that ends, which isn't the leader of its process, is waited for before the leader is; and the SIGSTOP
//     of PTRACE_ATTACH is of the kernel.
//   filters: a filter of seccomp that loads a word of scratch that a way to there didn't store is EINVAL.
//   paths: O_TRUNC of a directory is EISDIR; what is opened with the access mode 3 is neither read nor written; a link to "file/" is
//     ENOTDIR, as one that O_DIRECTORY and O_NOFOLLOW don't follow is; and nothing is made in /proc, ENOENT, nor removed, EPERM.
//   notices: inotify says IN_ACCESS of a directory that getdents reads, and IN_MOVE_SELF and IN_DELETE_SELF of one without IN_ISDIR.
// In a directory of its own that it makes where it runs and takes away.
#define _GNU_SOURCE
#include <elf.h>
#include <errno.h>
#include <fcntl.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/inotify.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/stat.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

#ifdef __x86_64__
extern char after_call[];
static volatile int got;
static void handler(int signal) { got = signal; }

static struct user_regs_struct registers(pid_t pid) {
  struct user_regs_struct regs;
  struct iovec vector = {&regs, sizeof regs};
  memset(&regs, 0, sizeof regs);
  ptrace(PTRACE_GETREGSET, pid, NT_PRSTATUS, &vector);
  return regs;
}

/* struct ptrace_syscall_info, of which the libc of the tests has none */
struct call_info {
  unsigned char op, pad[3];
  unsigned arch;
  unsigned long long ip, sp;
  union {
    struct { unsigned long long nr, args[6]; } entry;
    struct { long long rval; unsigned char is_error; } exit;
  };
};

static void info(pid_t pid, const struct user_regs_struct *regs) {
  struct call_info call;
  memset(&call, 0xee, sizeof call);
  long size = ptrace(0x420e, pid, sizeof call, &call);
  printf("  info of %ld: op %d arch %x, pc %s, sp %s", size, call.op, call.arch, call.ip == regs->rip ? "same" : "other",
         call.sp == regs->rsp ? "same" : "other");
  if (call.op == 1) printf(", number %lld\n", call.entry.nr);
  else printf(", result %lld\n", call.exit.rval);
}

static int code(pid_t pid) {
  siginfo_t signal;
  memset(&signal, 0, sizeof signal);
  ptrace(PTRACE_GETSIGINFO, pid, 0, &signal);
  return signal.si_code;
}

static void stops(void) {
  int status;
  pid_t child = fork();
  if (!child) {
    long result;
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    /* close(-1) */
    __asm__ volatile("mov $3, %%eax; mov $-1, %%edi; syscall; after_call: nop; nop" : "=a"(result) : : "rcx", "r11", "rdi");
    _exit(result == -EBADF ? 7 : 8);
  }
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACESYSGOOD);
  struct user_regs_struct regs;
  const char *names[] = {"start", "end", "start again"};
  for (int stop = 0; stop < 3; stop++) {
    /* past the calls that raise ends with */
    do {
      ptrace(PTRACE_SYSCALL, child, 0, 0);
      waitpid(child, &status, 0);
      regs = registers(child);
    } while (WIFSTOPPED(status) && regs.orig_rax != 3);
    printf("%s: status %x, %ld after the call, number %lld, result %lld\n", names[stop], status,
           (long)(regs.rip - (unsigned long)after_call), (long long)regs.orig_rax, (long long)regs.rax);
    info(child, &regs);
    if (stop == 1) {
      /* the call again, as a tracer that injects one has it */
      regs.rip -= 2;
      regs.rax = regs.orig_rax;
      struct iovec vector = {&regs, sizeof regs};
      said("registers set", ptrace(PTRACE_SETREGSET, child, NT_PRSTATUS, &vector));
    }
  }
  for (int step = 0; step < 2; step++) {
    ptrace(PTRACE_SINGLESTEP, child, 0, 0);
    waitpid(child, &status, 0);
    regs = registers(child);
    printf("step: status %x, %ld after the call, result %lld, code %d\n", status, (long)(regs.rip - (unsigned long)after_call),
           (long long)regs.rax, code(child));
  }
  said("on with a signal that there isn't", ptrace(PTRACE_CONT, child, 0, 65));
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  printf("ends with %x\n", status);
}

/* A call that waits: a read of an empty pipe that PTRACE_INTERRUPT stops, a sleep that it stops, and a read that a signal stops. */
static void left(int how) {
  int status, ends[2], ready[2];
  pipe(ends);
  pipe(ready);
  pid_t child = fork();
  if (!child) {
    char byte;
    long result;
    signal(SIGUSR1, handler);
    close(ends[1]);
    write(ready[1], "r", 1);
    if (how == 1) {
      struct timespec time = {20, 0};
      result = syscall(SYS_nanosleep, &time, 0);
    } else result = read(ends[0], &byte, 1);
    _exit(got == SIGUSR1 ? 50 : result == 1 ? 51 : 52);
  }
  char byte;
  read(ready[0], &byte, 1);
  usleep(30000);
  said("seize", ptrace(PTRACE_SEIZE, child, 0, 0));
  if (how == 2) kill(child, SIGUSR1);
  else said("interrupt", ptrace(PTRACE_INTERRUPT, child, 0, 0));
  waitpid(child, &status, 0);
  struct user_regs_struct regs = registers(child);
  errno = 0;
  long before = ptrace(PTRACE_PEEKTEXT, child, regs.rip - 2, 0);
  printf("stopped with %x in the call %lld, which gives %lld, %s its instruction\n", status, (long long)regs.orig_rax, (long long)regs.rax,
         errno == 0 && (before & 0xffff) == 0x050f ? "after" : "not after");
  if (how == 0) said("detach with a signal", ptrace(PTRACE_DETACH, child, 0, SIGUSR1));
  else if (how == 1) kill(child, SIGKILL);
  else ptrace(PTRACE_CONT, child, 0, 0);
  usleep(30000);
  write(ends[1], "x", 1);
  waitpid(child, &status, 0);
  printf("ends with %x\n", status);
  close(ends[0]);
  close(ends[1]);
  close(ready[0]);
  close(ready[1]);
}

static void *thread(void *argument) { return argument; }

static void threads(void) {
  int status;
  pid_t child = fork();
  if (!child) {
    pthread_t other;
    ptrace(PTRACE_TRACEME, 0, 0, 0);
    raise(SIGSTOP);
    pthread_create(&other, 0, thread, 0);
    pthread_join(other, 0);
    /* once the thread is over, and not only joined */
    usleep(30000);
    _exit(9);
  }
  waitpid(child, &status, 0);
  ptrace(PTRACE_SETOPTIONS, child, 0, PTRACE_O_TRACECLONE);
  ptrace(PTRACE_CONT, child, 0, 0);
  waitpid(child, &status, 0);
  unsigned long made = 0;
  ptrace(PTRACE_GETEVENTMSG, child, 0, &made);
  printf("the leader stops with %x, of a thread of its own: %d\n", status, made != 0 && (pid_t)made != child);
  waitpid(made, &status, __WALL);
  printf("the thread stops with %x\n", status);
  ptrace(PTRACE_CONT, made, 0, 0);
  ptrace(PTRACE_CONT, child, 0, 0);
  for (int ended = 0; ended < 2; ended++) {
    pid_t which = waitpid(-1, &status, __WALL);
    printf("%s ends with %x\n", which == child ? "the leader" : which == (pid_t)made ? "the thread" : "something else", status);
  }
  /* what PTRACE_ATTACH stops with */
  int ends[2];
  pipe(ends);
  child = fork();
  if (!child) {
    char byte;
    close(ends[1]);
    read(ends[0], &byte, 1);
    _exit(0);
  }
  usleep(30000);
  said("attach", ptrace(PTRACE_ATTACH, child, 0, 0));
  waitpid(child, &status, 0);
  siginfo_t signal;
  memset(&signal, 0, sizeof signal);
  ptrace(PTRACE_GETSIGINFO, child, 0, &signal);
  printf("stopped with %x by signal %d of code %d\n", status, signal.si_signo, signal.si_code);
  kill(child, SIGKILL);
  waitpid(child, &status, 0);
  close(ends[0]);
  close(ends[1]);
}

struct filter { unsigned short code; unsigned char jt, jf; unsigned k; };
struct program { unsigned short length; struct filter *filters; };

static void install(const char *what, struct filter *filters, int length) {
  /* in a process of its own, which a filter that is taken is of */
  pid_t child = fork();
  if (!child) {
    struct program program = {length, filters};
    prctl(PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0);
    said(what, syscall(SYS_seccomp, 1, 0, &program));
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
}

static void filters(void) {
  struct filter never[] = {{0x60, 0, 0, 2}, {0x06, 0, 0, 0x7fff0000}};
  struct filter oneWay[] = {{0x20, 0, 0, 0}, {0x15, 0, 1, 39}, {0x02, 0, 0, 2}, {0x60, 0, 0, 2}, {0x06, 0, 0, 0x7fff0000}};
  struct filter otherWord[] = {{0x20, 0, 0, 0}, {0x02, 0, 0, 3}, {0x61, 0, 0, 2}, {0x06, 0, 0, 0x7fff0000}};
  struct filter each[] = {{0x20, 0, 0, 0}, {0x03, 0, 0, 2}, {0x15, 0, 1, 39}, {0x02, 0, 0, 2}, {0x60, 0, 0, 2}, {0x06, 0, 0, 0x7fff0000}};
  install("a filter that loads scratch that nothing stored", never, 2);
  install("that one way didn't store", oneWay, 5);
  install("that is another word than was stored", otherWord, 4);
  install("that each way stored", each, 6);
}
#endif

static void traced(void) {
#ifndef __x86_64__
  /* which qemu, that says what the others do, can't run */
  printf("not traced\n");
#else
  stops();
  for (int how = 0; how < 3; how++) left(how);
  threads();
  filters();
#endif
}

static void paths(void) {
  char byte = 'x';
  mkdir("dir", 0755);
  close(open("file", O_CREAT | O_WRONLY, 0644));
  said("a directory opened with O_TRUNC", open("dir", O_RDONLY | O_TRUNC));
  int both = open("file", 3);
  said("a file opened with the access mode 3", both < 0 ? both : 0);
#ifdef __x86_64__
  /* which qemu lets through */
  said("read of it", read(both, &byte, 1));
#endif
  said("write of it", write(both, &byte, 1));
  struct stat status;
  said("fstat of it", fstat(both, &status));
  close(both);
  symlink("file/", "slashed");
  symlink("dir/", "slashedDir");
  symlink("dir", "toDir");
  said("a link to file/", access("slashed", F_OK));
  said("a link to dir/", access("slashedDir", F_OK));
  said("what is under a link to dir/", access("slashedDir/..", F_OK));
  int link = open("toDir", O_RDONLY | O_NOFOLLOW | O_DIRECTORY);
  said("a link opened with O_NOFOLLOW and O_DIRECTORY", link);
  link = open("toDir", O_RDONLY | O_NOFOLLOW);
  said("and with O_NOFOLLOW", link);
  said("mkdir in /proc/self", mkdir("/proc/self/made", 0755));
  said("a file made in /proc/self", open("/proc/self/made", O_CREAT | O_WRONLY, 0600));
  said("symlink in /proc/self", symlink("target", "/proc/self/made"));
  said("unlink of /proc/self/maps", unlink("/proc/self/maps"));
  said("rmdir of /proc/self/fd", rmdir("/proc/self/fd"));
  said("unlink of what isn't in /proc/self", unlink("/proc/self/nothing"));
  unlink("slashed");
  unlink("slashedDir");
  unlink("toDir");
  unlink("file");
  rmdir("dir");
}

static void heard(int fd, const char *after) {
  char buffer[1024];
  long size = read(fd, buffer, sizeof buffer);
  printf("after %s:", after);
  for (long at = 0; at < size;) {
    struct inotify_event *event = (struct inotify_event *)(buffer + at);
    printf(" %x", event->mask);
    if (event->len) printf(" of %s", event->name);
    at += sizeof *event + event->len;
  }
  printf("\n");
}

static void notices(void) {
  char entries[512];
  int fd = inotify_init1(IN_NONBLOCK);
  mkdir("watched", 0755);
  mkdir("watched/inside", 0755);
  said("a watch", inotify_add_watch(fd, "watched", IN_ALL_EVENTS));
  heard(fd, "nothing");
  int directory = open("watched", O_RDONLY | O_DIRECTORY);
  said("getdents", syscall(SYS_getdents64, directory, entries, sizeof entries) > 0);
  heard(fd, "a read of the directory");
  said("getdents at its end", syscall(SYS_getdents64, directory, entries, sizeof entries));
  heard(fd, "a read at its end");
  close(directory);
  heard(fd, "its close");
  directory = open("watched/inside", O_RDONLY | O_DIRECTORY);
  syscall(SYS_getdents64, directory, entries, sizeof entries);
  close(directory);
  heard(fd, "a read of a directory in it");
  rmdir("watched/inside");
  heard(fd, "that one is removed");
  rename("watched", "moved");
  heard(fd, "it is moved");
  rmdir("moved");
  heard(fd, "it is removed");
  close(fd);
}

int main(void) {
  setvbuf(stdout, 0, _IONBF, 0);
  mkdir("review24", 0755);
  chdir("review24");
  traced();
  paths();
  notices();
  chdir("..");
  rmdir("review24");
  return 0;
}
