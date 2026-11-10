#pragma once

#ifdef __linux__
#include <errno.h>
#include <limits.h>
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
  // In seconds and nanoseconds apart, and what overflows the seconds as far off as they go: a time far off, as
  // `steady_clock::time_point::max()`, is one that hasn't come, rather than a negative one that has.
  long long seconds;
  if (__builtin_sub_overflow((long long)timeout->tv_sec, (long long)monotonic.tv_sec, &seconds))
    seconds = timeout->tv_sec < monotonic.tv_sec ? LLONG_MIN : LLONG_MAX;
  long long nanos = (long long)timeout->tv_nsec - monotonic.tv_nsec;
  if (nanos < 0 && seconds != LLONG_MIN) {
    nanos += 1000000000LL;
    seconds -= 1;
  }
  if (seconds < 0) {
    seconds = 0;
    nanos = 0;
  }
  nanos += realtime.tv_nsec;
  if (nanos >= 1000000000LL) {
    nanos -= 1000000000LL;
    if (seconds < LLONG_MAX)
      seconds += 1;
  }
  long long due;
  if (__builtin_add_overflow((long long)realtime.tv_sec, seconds, &due)) {
    due = LLONG_MAX;
    nanos = 999999999LL;
  }
  struct timespec deadline = {(time_t)due, (long)nanos};
  return pthread_cond_timedwait(condition, mutex, &deadline);
}
#endif
