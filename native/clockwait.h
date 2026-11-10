#pragma once

#ifdef __linux__
#include <errno.h>
#include <pthread.h>
#include <time.h>

// For a glibc that hasn't it, which libstdc++ of a newer one calls for `wait_until` and `wait_for` of steady_clock. A condition variable
// made with its defaults waits by CLOCK_REALTIME, so the time of CLOCK_MONOTONIC that this is given is made one of that: what is left of
// it, from the time of CLOCK_REALTIME now. It was given as it is, which is long past by CLOCK_REALTIME, so that every wait ended at once.
extern "C" int pthread_cond_clockwait(pthread_cond_t *condition,
                                       pthread_mutex_t *mutex,
                                       clockid_t clock,
                                       const struct timespec *timeout) {
  if (clock != CLOCK_MONOTONIC)
    return EINVAL;
  struct timespec monotonic, realtime;
  clock_gettime(CLOCK_MONOTONIC, &monotonic);
  clock_gettime(CLOCK_REALTIME, &realtime);
  long long left = (timeout->tv_sec - monotonic.tv_sec) * 1000000000LL + (timeout->tv_nsec - monotonic.tv_nsec);
  if (left < 0)
    left = 0;
  long long due = realtime.tv_sec * 1000000000LL + realtime.tv_nsec + left;
  struct timespec deadline = {(time_t)(due / 1000000000LL), (long)(due % 1000000000LL)};
  return pthread_cond_timedwait(condition, mutex, &deadline);
}
#endif
