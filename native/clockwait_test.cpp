// What the `pthread_cond_clockwait` of `clockwait.h` does, on its own: a wait to a time of CLOCK_MONOTONIC that nothing signals ends at
// that time, rather than at once, and of another clock it is EINVAL. It takes no part in a build:
//   clang++ -std=c++17 -O1 -fuse-ld=lld -pthread native/clockwait_test.cpp -o /tmp/clockwait && /tmp/clockwait

#include "clockwait.h"

#include <cstdio>

static long long nanosOf(clockid_t clock) {
  struct timespec now;
  clock_gettime(clock, &now);
  return now.tv_sec * 1000000000LL + now.tv_nsec;
}

int main() {
  pthread_cond_t condition = PTHREAD_COND_INITIALIZER;
  pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
  pthread_mutex_lock(&mutex);
  long long start = nanosOf(CLOCK_MONOTONIC);
  long long due = start + 200000000LL;
  struct timespec deadline = {(time_t)(due / 1000000000LL), (long)(due % 1000000000LL)};
  int result = pthread_cond_clockwait(&condition, &mutex, CLOCK_MONOTONIC, &deadline);
  long long waited = nanosOf(CLOCK_MONOTONIC) - start;
  int failures = 0;
  if (result != ETIMEDOUT) {
    std::printf("a wait that nothing signals gives %d, not ETIMEDOUT\n", result);
    failures++;
  }
  if (waited < 150000000LL || waited > 2000000000LL) {
    std::printf("a wait of 200 ms took %lld ms\n", waited / 1000000);
    failures++;
  }
  if (pthread_cond_clockwait(&condition, &mutex, CLOCK_PROCESS_CPUTIME_ID, &deadline) != EINVAL) {
    std::printf("a wait by a clock that it doesn't take isn't EINVAL\n");
    failures++;
  }
  pthread_mutex_unlock(&mutex);
  std::printf(failures == 0 ? "clockwait: ok\n" : "clockwait: %d failed\n", failures);
  return failures == 0 ? 0 : 1;
}
