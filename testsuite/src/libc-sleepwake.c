// A thread sleeps while the main thread works and then joins it: the sleep takes its time, which only the clock ends, whatever else the
// machine is asked to do with the thread while it sleeps (testLinuxSleepWake has it resumed then, as a caller that stopped it would).
//   the sleep took its time: it was at least the 100 ms that the thread asked for, and not more than a second.
#define _GNU_SOURCE
#include <pthread.h>
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static void say(const char *text) { write(1, text, strlen(text)); }

static uint64_t nanos(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000000u + (uint64_t)now.tv_nsec;
}

static void *sleeper(void *result) {
  struct timespec pause = {0, 100000000};
  uint64_t start = nanos();
  nanosleep(&pause, 0);
  *(uint64_t *)result = nanos() - start;
  return 0;
}

int main(void) {
  uint64_t slept = 0;
  pthread_t thread;
  pthread_create(&thread, 0, sleeper, &slept);
  for (volatile int index = 0; index < 200000; index++) {
  }
  pthread_join(thread, 0);
  say(slept >= 100000000u && slept < 1000000000u ? "the sleep took its time\n" : "the sleep didn't take its time\n");
  say("done\n");
  return 0;
}
