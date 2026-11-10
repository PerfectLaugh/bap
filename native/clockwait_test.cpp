// What the `pthread_cond_clockwait` of `clockwait.h` does, on its own: a wait to a time of CLOCK_MONOTONIC that nothing signals ends at
// that time, rather than at once, and of another clock it is EINVAL. It takes no part in a build:
//   clang++ -std=c++17 -O1 -fuse-ld=lld -pthread native/clockwait_test.cpp -o /tmp/clockwait && /tmp/clockwait

#include "clockwait.h"

#include <climits>
#include <cstdio>
#include <utility>

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
  // A time far off, as `steady_clock::time_point::max()` gives, waits until it is signaled, rather than failing at once.
  struct Signaler {
    static void *run(void *argument) {
      struct timespec pause = {0, 200000000};
      nanosleep(&pause, 0);
      auto *pair = static_cast<std::pair<pthread_cond_t *, pthread_mutex_t *> *>(argument);
      pthread_mutex_lock(pair->second);
      pthread_cond_signal(pair->first);
      pthread_mutex_unlock(pair->second);
      return 0;
    }
  };
  std::pair<pthread_cond_t *, pthread_mutex_t *> pair{&condition, &mutex};
  pthread_t signaler;
  pthread_create(&signaler, 0, Signaler::run, &pair);
  struct timespec farOff = {(time_t)LLONG_MAX, 999999999};
  start = nanosOf(CLOCK_MONOTONIC);
  result = pthread_cond_clockwait(&condition, &mutex, CLOCK_MONOTONIC, &farOff);
  waited = nanosOf(CLOCK_MONOTONIC) - start;
  // What signals takes the mutex, which a wait that ended at once still has.
  pthread_mutex_unlock(&mutex);
  pthread_join(signaler, 0);
  pthread_mutex_lock(&mutex);
  if (result != 0 || waited < 150000000LL) {
    std::printf("a wait to a time far off gives %d after %lld ms, not 0 when it is signaled\n", result, waited / 1000000);
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
