// Ids and capabilities, as Linux has them. setfsuid and setfsgid of -1, which isn't an id, change nothing and give what there is.
// capget of a version that isn't one writes _LINUX_CAPABILITY_VERSION_3 and is EINVAL, but with no data it is how a program asks
// which version there is, and gives 0. Those who aren't root have no capabilities: they may set what they have, nothing, and may not
// raise one, nor set those of another. setgroups needs CAP_SETGID, and getgroups of a negative size is EINVAL. A program that runs
// has the saved and filesystem ids of its effective ones. Root may do more than anyone else: what only root may do it says as 1, as
// anyone else does, but it is checked: that setgroups sorts the groups, that a capability that it gives up it hasn't, that a uid that
// isn't 0 has no effective capabilities but keeps the permitted ones while the saved id is 0, which it gets back as the effective id
// is 0 again, that setfsuid gives up and gets back those of files, and that a program that root runs has all of them again. Then it
// is nobody, so that it says the same as anyone else. It says what each call gave, the same on each target.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <sys/syscall.h>
#include <sys/wait.h>
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

struct header { unsigned version; int pid; };
struct data { unsigned effective, permitted, inheritable; };

static const unsigned version3 = 0x20080522;

static long capget(struct header *header, struct data *data) { return result(syscall(SYS_capget, header, data)); }

static long capset(unsigned effective, unsigned permitted, unsigned inheritable, int pid) {
  struct header header = {version3, pid};
  struct data data[2] = {{effective, permitted, inheritable}, {0, 0, 0}};
  return result(syscall(SYS_capset, &header, data));
}

// The low words of the effective and permitted capabilities of the process.
static void own(unsigned *effective, unsigned *permitted) {
  struct header header = {version3, 0};
  struct data data[2] = {{0, 0, 0}, {0, 0, 0}};
  capget(&header, data);
  *effective = data[0].effective;
  *permitted = data[0].permitted;
}

static char *noEnvironment[] = {NULL};

// How a child that runs this program again, with `mode`, exits.
static long again(const char *mode) {
  char *arguments[] = {"identity", (char *)mode, NULL};
  char link[4096] = {0};
  readlink("/proc/self/exe", link, sizeof link - 1);
  syscall(SYS_execve, link, arguments, noEnvironment);
  return 100 + errno;
}

static long waited(pid_t child) {
  int status = 0;
  waitpid(child, &status, 0);
  return WEXITSTATUS(status);
}

int main(int argc, char **argv) {
  if (argc > 1 && argv[1][0] == 'n') {
    // Run after it was given up to be nobody, but for root as the saved id where it could.
    unsigned ruid, euid, suid, rgid, egid, sgid;
    syscall(SYS_getresuid, &ruid, &euid, &suid);
    syscall(SYS_getresgid, &rgid, &egid, &sgid);
    say("exec suid is euid", suid == euid);
    say("exec sgid is egid", sgid == egid);
    say("exec fsuid is euid", syscall(SYS_setfsuid, -1) == (long)euid);
    say("exec fsgid is egid", syscall(SYS_setfsgid, -1) == (long)egid);
    unsigned effective, permitted;
    own(&effective, &permitted);
    say("exec no capabilities", effective == 0 && permitted == 0);
    return 0;
  }
  if (argc > 1 && argv[1][0] == 'r') {
    // Run by root, with one capability that it had given up of its effective ones.
    unsigned effective, permitted;
    own(&effective, &permitted);
    say("root exec all capabilities", getuid() != 0 || (effective == 0xffffffff && permitted == 0xffffffff));
    return 0;
  }
  int root = getuid() == 0;

  // -1 isn't an id, so that it is how one reads what there is.
  long euid = syscall(SYS_geteuid), egid = syscall(SYS_getegid);
  say("setfsuid -1", syscall(SYS_setfsuid, -1) == euid);
  say("setfsuid -1 again", syscall(SYS_setfsuid, -1) == euid);
  say("setfsgid -1", syscall(SYS_setfsgid, -1) == egid);
  say("setfsgid -1 again", syscall(SYS_setfsgid, -1) == egid);

  // The version that there is.
  struct header header = {0x12345678, 0};
  say("capget probe", capget(&header, NULL));
  say("capget probe version", header.version == version3);
  struct data data[2];
  header.version = 0x12345678;
  say("capget bad version", capget(&header, data));
  say("capget bad version written", header.version == version3);
  header.version = version3;
  header.pid = 0;
  say("capget no data", capget(&header, NULL));
  header.version = version3;
  header.pid = -1;
  say("capget pid -1", capget(&header, data));
  header.version = 0x12345678;
  say("capset bad version", result(syscall(SYS_capset, &header, data)));

  // What only root may do.
  if (root) {
    pid_t child = fork();
    if (child == 0) {
      unsigned groups[] = {30, 10, 20}, got[3] = {0, 0, 0};
      long set = result(syscall(SYS_setgroups, 3, groups));
      long count = result(syscall(SYS_getgroups, 3, got));
      _exit(set == 0 && count == 3 && got[0] == 10 && got[1] == 20 && got[2] == 30);
    }
    say("root setgroups sorts", waited(child));
    child = fork();
    if (child == 0) {
      // Without CAP_SETUID.
      long given = capset(0xffffffff & ~(1u << 7), 0xffffffff & ~(1u << 7), 0, 0);
      unsigned effective, permitted;
      own(&effective, &permitted);
      _exit(given == 0 && effective == (0xffffffff & ~(1u << 7)) && permitted == effective &&
            result(syscall(SYS_setresuid, 1, 1, 1)) == -EPERM && result(syscall(SYS_setuid, 1)) == -EPERM);
    }
    say("root capset drops", waited(child));
    child = fork();
    if (child == 0) {
      unsigned effective, permitted, okay = 1;
      okay &= result(syscall(SYS_setresuid, 65534, 65534, 0)) == 0;
      own(&effective, &permitted);
      okay &= effective == 0 && permitted == 0xffffffff;
      okay &= result(syscall(SYS_setgroups, 0, NULL)) == -EPERM;
      okay &= result(syscall(SYS_setresuid, -1, 0, -1)) == 0;
      own(&effective, &permitted);
      okay &= effective == 0xffffffff && permitted == 0xffffffff;
      // Of files only.
      syscall(SYS_setfsuid, 65534);
      own(&effective, &permitted);
      okay &= effective == (0xffffffff & ~0x0800021fu) && permitted == 0xffffffff;
      syscall(SYS_setfsuid, 0);
      own(&effective, &permitted);
      okay &= effective == 0xffffffff;
      okay &= result(syscall(SYS_setresuid, 65534, 65534, 65534)) == 0;
      own(&effective, &permitted);
      okay &= effective == 0 && permitted == 0;
      okay &= result(syscall(SYS_setresuid, 0, 0, 0)) == -EPERM;
      _exit(okay);
    }
    say("root setuid capabilities", waited(child));
    child = fork();
    if (child == 0) {
      capset(0xffffffff & ~1u, 0xffffffff, 0, 0);
      _exit(again("root"));
    }
    waited(child);
  } else {
    say("root setgroups sorts", 1);
    say("root capset drops", 1);
    say("root setuid capabilities", 1);
    say("root exec all capabilities", 1);
  }

  // Of a program that runs: as root, the saved ids are 0 until then.
  pid_t child = fork();
  if (child == 0) {
    if (root) {
      syscall(SYS_setgroups, 0, NULL);
      syscall(SYS_setresgid, 65534, 65534, 0);
      syscall(SYS_setresuid, 65534, 65534, 0);
    }
    _exit(again("nobody"));
  }
  say("exec", waited(child));

  if (root) {
    syscall(SYS_setgroups, 0, NULL);
    syscall(SYS_setresgid, 65534, 65534, 65534);
    syscall(SYS_setresuid, 65534, 65534, 65534);
  }
  unsigned effective, permitted;
  own(&effective, &permitted);
  say("no capabilities", effective == 0 && permitted == 0);
  say("capset nothing", capset(0, 0, 0, 0));
  say("capset raise", capset(1u << 7, 1u << 7, 0, 0));
  say("capset effective beyond permitted", capset(1u << 7, 0, 0, 0));
  say("capset inheritable", capset(0, 0, 1u << 7, 0));
  pid_t other = fork();
  if (other == 0) _exit(0);
  say("capset of another", capset(0, 0, 0, other));
  waited(other);
  say("setgroups", result(syscall(SYS_setgroups, 0, NULL)));
  say("getgroups -1", result(syscall(SYS_getgroups, -1, NULL)));
  say("setfsuid -1 nobody", syscall(SYS_setfsuid, -1) == syscall(SYS_geteuid));
  say("setfsuid -1 nobody again", syscall(SYS_setfsuid, -1) == syscall(SYS_geteuid));
  return 0;
}
