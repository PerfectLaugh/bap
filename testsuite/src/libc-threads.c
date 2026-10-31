#include <pthread.h>
#include <unistd.h>
static int counter; static pthread_mutex_t m = PTHREAD_MUTEX_INITIALIZER;
static void *work(void *a) { for (int i = 0; i < 100; i++) { pthread_mutex_lock(&m); counter++; pthread_mutex_unlock(&m); } return a; }
int main(void) { pthread_t t[3]; for (long i = 0; i < 3; i++) pthread_create(&t[i], 0, work, (void *)i);
  for (int i = 0; i < 3; i++) pthread_join(t[i], 0); char c = counter == 300 ? 'y' : 'n'; write(1, &c, 1); return counter == 300 ? 0 : 1; }
