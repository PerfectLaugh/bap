/* What a library needs of a libc, from the base environment of Bap.Linux.BaseEnv, with no libc in the guest:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libbaseuse.so libbaseuse.c -o libbaseuse.so
   `run` says by each bit what came out as it should. */
#include <stddef.h>

typedef unsigned long pthread_t;
typedef struct { int word[10]; } pthread_mutex_t;
typedef struct { int word[12]; } pthread_cond_t;
typedef int pthread_once_t;
typedef unsigned pthread_key_t;

extern void *malloc(size_t);
extern void *calloc(size_t, size_t);
extern void *realloc(void *, size_t);
extern void free(void *);
extern int posix_memalign(void **, size_t, size_t);
extern void *memcpy(void *, const void *, size_t);
extern void *memset(void *, int, size_t);
extern int memcmp(const void *, const void *, size_t);
extern size_t strlen(const char *);
extern int strcmp(const char *, const char *);
extern char *strcpy(char *, const char *);
extern char *strdup(const char *);
extern char *strchr(const char *, int);
extern char *strstr(const char *, const char *);
extern int *__errno_location(void);
extern int pthread_create(pthread_t *, const void *, void *(*)(void *), void *);
extern int pthread_join(pthread_t, void **);
extern int pthread_mutex_lock(pthread_mutex_t *);
extern int pthread_mutex_unlock(pthread_mutex_t *);
extern int pthread_cond_wait(pthread_cond_t *, pthread_mutex_t *);
extern int pthread_cond_signal(pthread_cond_t *);
extern int pthread_once(pthread_once_t *, void (*)(void));
extern int pthread_key_create(pthread_key_t *, void (*)(void *));
extern int pthread_setspecific(pthread_key_t, const void *);
extern void *pthread_getspecific(pthread_key_t);
extern pthread_t pthread_self(void);

static pthread_mutex_t lock;
static pthread_cond_t ready;
static volatile long counter;
static volatile int turn;
static int onceRuns;
static pthread_once_t once;
static pthread_key_t key;

static void initialize(void) { onceRuns++; }

static void *worker(void *argument) {
  long index = (long)argument;
  pthread_setspecific(key, (void *)(index + 100));
  for (int i = 0; i < 1000; i++) {
    pthread_mutex_lock(&lock);
    counter = counter + 1;
    pthread_mutex_unlock(&lock);
  }
  pthread_once(&once, initialize);
  return (void *)((long)pthread_getspecific(key) * 10);
}

static void *waiter(void *ignored) {
  pthread_mutex_lock(&lock);
  while (turn == 0) pthread_cond_wait(&ready, &lock);
  turn = 2;
  pthread_mutex_unlock(&lock);
  return ignored;
}

int run(void) {
  int found = 0;
  char *text = malloc(32);
  strcpy(text, "hello base");
  if (strlen(text) == 10 && strcmp(text, "hello base") == 0 && strchr(text, 'b') == text + 6 && strstr(text, "base") == text + 6)
    found |= 1 << 0;
  char *copy = strdup(text);
  text = realloc(text, 4096);
  if (copy && copy != text && strcmp(copy, text) == 0 && memcmp(copy, "hello", 5) == 0) found |= 1 << 1;
  int *zeros = calloc(16, sizeof(int));
  int allZero = 1;
  for (int i = 0; i < 16; i++) allZero &= zeros[i] == 0;
  memset(zeros, 7, 4);
  void *aligned = 0;
  if (allZero && zeros[0] == 0x07070707 && posix_memalign(&aligned, 256, 100) == 0 && ((unsigned long)aligned & 255) == 0)
    found |= 1 << 2;
  free(copy);
  free(text);
  free(zeros);
  free(aligned);
  *__errno_location() = 42;
  if (*__errno_location() == 42) found |= 1 << 3;

  // Threads that count under a lock, with what each gives back.
  pthread_key_create(&key, 0);
  pthread_setspecific(key, (void *)7);
  pthread_t threads[4];
  for (long i = 0; i < 4; i++) pthread_create(&threads[i], 0, worker, (void *)i);
  long given = 0;
  for (int i = 0; i < 4; i++) {
    void *result = 0;
    pthread_join(threads[i], &result);
    given += (long)result;
  }
  if (counter == 4000) found |= 1 << 4;
  if (given == (100 + 101 + 102 + 103) * 10) found |= 1 << 5;
  if (onceRuns == 1 && (long)pthread_getspecific(key) == 7) found |= 1 << 6;

  // One waits on a condition that another makes true.
  pthread_t other;
  pthread_create(&other, 0, waiter, 0);
  pthread_mutex_lock(&lock);
  turn = 1;
  pthread_cond_signal(&ready);
  pthread_mutex_unlock(&lock);
  pthread_join(other, 0);
  if (turn == 2 && pthread_self() != other) found |= 1 << 7;
  return found;
}

/* What another library that a libc has the same names of as the base environment calls. */
size_t length_of(const char *text) { return strlen(text); }

/* A handler of a signal, which says what came. */
static volatile int caught;
void on_signal(int signal) { caught = signal; }
int caught_signal(void) { return caught; }
