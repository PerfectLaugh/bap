#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <dirent.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <time.h>
int main(int c, char **v) {
  char b[128]; struct stat s; printf("args %d %s\n", c, c > 1 ? v[1] : "-");
  printf("cwd %s\n", getcwd(b, 128) ? b : "?");
  mkdir("/d", 0755); chdir("/d");
  FILE *f = fopen("a.txt", "w"); fprintf(f, "hello %d\n", 42); fclose(f);
  f = fopen("/d/a.txt", "r"); fgets(b, 128, f); fclose(f); printf("read %s", b);
  stat("a.txt", &s); printf("size %ld dir %d\n", (long)s.st_size, S_ISDIR(s.st_mode));
  int fd = open("b", O_CREAT | O_RDWR, 0644); write(fd, "xyz", 3); lseek(fd, 1, SEEK_SET); read(fd, b, 2); b[2] = 0; printf("seek %s\n", b);
  int g = dup(fd); lseek(g, 0, SEEK_SET); read(fd, b, 1); b[1] = 0; printf("dup %s\n", b); close(fd); close(g);
  rename("b", "c"); symlink("c", "l"); readlink("l", b, 128); b[1] = 0; printf("link %s\n", b);
  DIR *d = opendir("."); struct dirent *e; int n = 0; while ((e = readdir(d))) { if (e->d_name[0] != '.') n++; } closedir(d); printf("entries %d\n", n);
  unlink("c"); printf("gone %d\n", access("c", F_OK)); printf("time %d\n", time(0) > 1000000);
  void *m = malloc(1 << 22); memset(m, 1, 1 << 22); printf("malloc %d\n", ((char *)m)[99]);
  f = fopen("/nope", "r"); printf("nope %d\n", f == 0); return 5;
}
