// What a program sees of the clocks of AArch64 Linux, where the time between two readings is the work done between them, and every clock
// is one: only what holds of that is printed, never a value, so that a device and the emulator say the same.
//   cntvct: proportional: ten times the work is at least five times the ticks of CNTVCT_EL0, which a counter that steps by the same at
//     each read, or that a read doesn't see move, isn't.
//   clocks: agree: CNTVCT_EL0, by CNTFRQ_EL0, and clock_gettime say about the same of the same work, within a factor of two.
//   clocks: agree over a wait: and of a sleep, which another thread or nothing runs in, as a clock that only counted the work of the
//     thread, or that went on when the machine looked at its threads, wouldn't.
//   clock: proportional: as of CNTVCT_EL0, of clock_gettime.
//   sleep: on time: clock_nanosleep to a time of clock_gettime wakes at it, not before and not a second after, which it doesn't if the
//     deadlines of the kernel go by another clock.
//   monotonic: neither clock goes back over many readings, with work between them, as the test has them in pieces of checkpoints too.
#define _GNU_SOURCE
#include <stdint.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

static void say(const char *text) { write(1, text, strlen(text)); }

static uint64_t counter(void) {
  uint64_t value;
  __asm__ volatile("isb\n\tmrs %0, cntvct_el0" : "=r"(value)::"memory");
  return value;
}

static uint64_t frequency(void) {
  uint64_t value;
  __asm__ volatile("mrs %0, cntfrq_el0" : "=r"(value));
  return value;
}

static uint64_t nanos(void) {
  struct timespec now;
  clock_gettime(CLOCK_MONOTONIC, &now);
  return (uint64_t)now.tv_sec * 1000000000u + (uint64_t)now.tv_nsec;
}

static void work(int count) {
  for (volatile int index = 0; index < count; index++) {
  }
}

int main(void) {
  uint64_t start = counter();
  work(20000);
  uint64_t shortTicks = counter() - start;
  start = counter();
  uint64_t startNanos = nanos();
  work(200000);
  uint64_t longTicks = counter() - start;
  uint64_t longNanos = nanos() - startNanos;
  say(shortTicks > 0 && longTicks >= 5 * shortTicks ? "cntvct: proportional\n" : "cntvct: not proportional\n");

  uint64_t counted = longTicks * 1000000000u / frequency();
  say(counted <= 2 * longNanos && longNanos <= 2 * counted ? "clocks: agree\n" : "clocks: disagree\n");

  struct timespec pause = {0, 1000000};
  start = counter();
  startNanos = nanos();
  nanosleep(&pause, 0);
  uint64_t waitedTicks = counter() - start;
  uint64_t waitedNanos = nanos() - startNanos;
  uint64_t waitedCounted = waitedTicks * 1000000000u / frequency();
  say(waitedCounted <= 2 * waitedNanos && waitedNanos <= 2 * waitedCounted ? "clocks: agree over a wait\n"
                                                                          : "clocks: disagree over a wait\n");

  startNanos = nanos();
  work(20000);
  uint64_t shortNanos = nanos() - startNanos;
  startNanos = nanos();
  work(200000);
  longNanos = nanos() - startNanos;
  say(shortNanos > 0 && longNanos >= 5 * shortNanos ? "clock: proportional\n" : "clock: not proportional\n");

  struct timespec deadline;
  clock_gettime(CLOCK_MONOTONIC, &deadline);
  deadline.tv_nsec += 1000000;
  if (deadline.tv_nsec >= 1000000000) {
    deadline.tv_sec++;
    deadline.tv_nsec -= 1000000000;
  }
  uint64_t due = (uint64_t)deadline.tv_sec * 1000000000u + (uint64_t)deadline.tv_nsec;
  clock_nanosleep(CLOCK_MONOTONIC, TIMER_ABSTIME, &deadline, 0);
  uint64_t woke = nanos();
  say(woke >= due && woke < due + 1000000000u ? "sleep: on time\n" : "sleep: not on time\n");

  int forward = 1;
  uint64_t lastTicks = counter(), lastNanos = nanos();
  for (int round = 0; round < 200; round++) {
    work(2000);
    uint64_t ticks = counter(), now = nanos();
    if (ticks < lastTicks || now < lastNanos) forward = 0;
    lastTicks = ticks;
    lastNanos = now;
  }
  say(forward ? "monotonic\n" : "not monotonic\n");
  say("done\n");
  return 0;
}
