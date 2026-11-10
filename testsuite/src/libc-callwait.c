// Functions that wait, which the host calls with Machine.call and which don't come back by the fuel that it gives them: the program
// then runs as it would have, to its end (testCallWaits).
#define _GNU_SOURCE
#include <stdio.h>
#include <time.h>
#include <unistd.h>

__attribute__((noinline, used)) void waits_forever(void) { pause(); }

__attribute__((noinline, used)) void sleeps_long(void) {
  struct timespec span = {1000, 0};
  nanosleep(&span, 0);
}

int main(void) {
  struct timespec span = {0, 1000000};
  int result = nanosleep(&span, 0);
  printf("ran to its end, a sleep of its own gave %d\n", result);
  return 0;
}
