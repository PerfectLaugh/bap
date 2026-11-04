#include <unistd.h>
#include <sys/wait.h>
/* Two children: one that is over before it is waited for, which a wait that doesn't block finds, and one that a wait waits for.
   Each wait says the pid that it found less the one that fork gave, as a host may give the guest pids of its own. */
static char *decimal(char *out, int value) {
  char digits[12]; int count = 0;
  if (value < 0) { *out++ = '-'; value = -value; }
  do { digits[count++] = '0' + value % 10; value /= 10; } while (value);
  while (count) *out++ = digits[--count];
  return out;
}
int main(void) {
  pid_t quick = fork();
  if (quick == 0) _exit(1);
  int status = 0;
  pid_t found;
  while ((found = waitpid(-1, &status, WNOHANG)) == 0) {}
  pid_t slow = fork();
  if (slow == 0) { for (volatile int i = 0; i < 100000; i++) {} _exit(2); }
  pid_t waited = waitpid(slow, &status, 0);
  char text[32];
  char *at = decimal(text, found - quick);
  *at++ = ' ';
  at = decimal(at, waited - slow);
  *at++ = '\n';
  write(1, text, at - text);
  return 0;
}
