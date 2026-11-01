#include <pthread.h>
#include <unistd.h>
/* Threads that add with LR and SC. An update survives only if an SC fails when another thread may have run. */
static volatile int counter;
static void add(void) { int value, failed; do { __asm__("lr.w %0, (%2)\n addi %0, %0, 1\n sc.w %1, %0, (%2)" : "=&r"(value), "=&r"(failed) : "r"(&counter) : "memory"); } while (failed); }
static void *work(void *a) { for (int i = 0; i < 2000; i++) add(); return a; }
int main(void) { pthread_t t[3]; for (long i = 0; i < 3; i++) pthread_create(&t[i], 0, work, (void *)i);
  for (int i = 0; i < 3; i++) pthread_join(t[i], 0); char c = counter == 6000 ? 'y' : 'n'; write(1, &c, 1); return counter == 6000 ? 0 : 1; }
