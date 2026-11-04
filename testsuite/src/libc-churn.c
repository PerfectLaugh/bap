// Pipes and files opened and closed many times, of which what is closed is let go of, and what stays open stays.
#include <fcntl.h>
#include <unistd.h>

int main(void) {
  int kept[2];
  pipe(kept);
  write(kept[1], "kept", 4);
  for (int i = 0; i < 3000; i++) {
    int pipes[2];
    pipe(pipes);
    write(pipes[1], "x", 1);
    close(pipes[0]);
    close(pipes[1]);
    close(open("/dev/null", O_RDONLY));
  }
  char text[4];
  write(1, read(kept[0], text, 4) == 4 && text[0] == 'k' ? "kept\n" : "lost\n", 5);
  return 0;
}
