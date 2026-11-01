#include <pthread.h>
#include <unistd.h>
/* Threads that add with lwarx and stwcx. An update survives only if a store fails when another thread may have run. */
static volatile int counter;
static void add(void) { int value; __asm__("1: lwarx %0, 0, %1\n addi %0, %0, 1\n stwcx. %0, 0, %1\n bne- 1b" : "=&b"(value) : "b"(&counter) : "memory", "cr0"); }
static void *work(void *a) { for (int i = 0; i < 2000; i++) add(); return a; }
int main(void) { pthread_t t[3]; for (long i = 0; i < 3; i++) pthread_create(&t[i], 0, work, (void *)i);
  for (int i = 0; i < 3; i++) pthread_join(t[i], 0); char c = counter == 6000 ? 'y' : 'n'; write(1, &c, 1); return counter == 6000 ? 0 : 1; }
