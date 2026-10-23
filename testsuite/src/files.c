/* Reads the file /data/input, which the redirections of the channels
   serve, e.g., --primus-lisp-channel-redirect=/data/input:FILE, or
   Bap_emu.create ~redirects, with open, lseek, read, fopen, fseek,
   ftell, and close, and prints its size, its last 4 bytes, and its
   first line, and fails to open a file, that isn't redirected:

   gcc -O1 -fno-builtin files.c -o ../bin/x86_64-linux-gnu-files */

#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

int main(void) {
    int fd = open("/data/input", O_RDONLY);
    if (fd < 0) return 1;
    long size = lseek(fd, 0, SEEK_END);
    char tail[5] = {0};
    lseek(fd, -4, SEEK_END);
    read(fd, tail, 4);
    long back = lseek(fd, 0, SEEK_SET);
    printf("size %ld tail %s back %ld close %d\n", size, tail, back, close(fd));
    FILE *f = fopen("/data/input", "r");
    char line[64];
    fseek(f, 0, SEEK_SET);
    fgets(line, sizeof line, f);
    printf("line %s", line);
    printf("tell %ld\n", ftell(f));
    fclose(f);
    printf("missing %d\n", open("/data/missing", O_RDONLY));
    return 0;
}
