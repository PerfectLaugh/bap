#include <pthread.h>
#include <unistd.h>
/* Threads that add with exclusive loads and stores. An update survives only if a store fails when another thread may have run. */
static volatile int counter;
static void add(void) { int value, failed; do { __asm__("ldxr %w0, [%2]\n add %w0, %w0, #1\n stxr %w1, %w0, [%2]" : "=&r"(value), "=&r"(failed) : "r"(&counter) : "memory"); } while (failed); }
static void *work(void *a) { for (int i = 0; i < 2000; i++) add(); return a; }
int main(void) { pthread_t t[3]; for (long i = 0; i < 3; i++) pthread_create(&t[i], 0, work, (void *)i);
  for (int i = 0; i < 3; i++) pthread_join(t[i], 0); char c = counter == 6000 ? 'y' : 'n'; write(1, &c, 1); return counter == 6000 ? 0 : 1; }
