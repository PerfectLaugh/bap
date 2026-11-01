#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <fcntl.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/stat.h>
#include <sys/wait.h>
/* What a program finds in /proc, about itself and about its child. The output has nothing that differs between machines. */
static char b[65536];
static int slurp(const char *path) { int fd = open(path, O_RDONLY); if (fd < 0) return -1; int n = 0, r; while ((r = read(fd, b + n, sizeof b - n - 1)) > 0) n += r; close(fd); b[n] = 0; return n; }
static const char *field(const char *name) { static char v[64]; const char *p = strstr(b, name); v[0] = 0; if (p) sscanf(p + strlen(name), " %63s", v); return v; }
int main(int c, char **v) {
  char l[256]; int n; struct stat s;
  n = slurp("/proc/self/cmdline"); printf("cmdline %d %s %s\n", n, b, b + strlen(b) + 1);
  n = readlink("/proc/self/exe", l, 255); l[n > 0 ? n : 0] = 0; printf("exe %s\n", l);
  slurp("/proc/self/maps"); printf("maps stack %d exec %d\n", strstr(b, "[stack]") != 0, strstr(b, "r-xp") != 0);
  char mine[32]; slurp("/proc/self/status"); strcpy(mine, field("Pid:")); printf("status name %s same %d\n", field("Name:"), atoi(mine) == getpid());
  sprintf(l, "/proc/%d/comm", getpid()); slurp(l); printf("comm by pid %s", b);
  n = readlink("/proc/self", l, 255); l[n > 0 ? n : 0] = 0; printf("self is pid %d\n", atoi(l) == getpid());
  int fd = open("/made", O_CREAT | O_RDWR, 0644); sprintf(l, "/proc/self/fd/%d", fd); char t[256]; n = readlink(l, t, 255); t[n > 0 ? n : 0] = 0; printf("fd link %s\n", t);
  DIR *d = opendir("/proc/self/fd"); int count = 0; struct dirent *e; while (d && (e = readdir(d))) if (e->d_name[0] != '.') count++; if (d) closedir(d); printf("fds %d\n", count > 3);
  stat("/proc/cpuinfo", &s); printf("cpuinfo size %ld read %d\n", (long)s.st_size, slurp("/proc/cpuinfo") > 0);
  slurp("/proc/sys/kernel/ostype"); printf("ostype %s", b);
  printf("custom %d %s", slurp("/custom"), b);
  printf("write refused %d\n", open("/proc/self/status", O_WRONLY) < 0);
  pid_t child = fork();
  if (child == 0) { slurp("/proc/self/status"); char ppid[32]; strcpy(ppid, field("PPid:")); _exit(atoi(ppid) == getppid() ? 7 : 8); }
  sprintf(l, "/proc/%d/status", child); printf("child seen %d\n", slurp(l) > 0);
  int st = 0; waitpid(child, &st, 0); printf("child %d gone %d\n", WEXITSTATUS(st), slurp(l) < 0);
  return 4;
}
