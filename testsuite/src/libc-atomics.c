/* Atomics of AArch64 that threads race on: exclusive loads and stores in loops, as code without LSE has them, and each LSE
   instruction with each of its orders, to the same words, with switches between threads wherever the emulator makes them. Nothing
   that a thread adds is lost, a bit that a thread owns is what it left, and a count of references that the main thread holds one
   of never comes to zero, as that of a shared_ptr that is copied and let go of. It says what it found, a line for each. */
#include <pthread.h>
#include <unistd.h>

#define THREADS 4
#define ROUNDS 2000

static void say(const char *label, unsigned long got, unsigned long want) {
  char line[96];
  int n = 0;
  while (label[n]) { line[n] = label[n]; n++; }
  line[n++] = ' ';
  line[n++] = got == want ? 'y' : 'n';
  if (got != want) {
    char digits[24];
    int d = 0;
    do { digits[d++] = (char)('0' + got % 10); got /= 10; } while (got);
    line[n++] = ' ';
    while (d) line[n++] = digits[--d];
  }
  line[n++] = '\n';
  write(1, line, n);
}

static unsigned long exclusive64, exclusiveAcquire32Word, ldaddPlain, ldaddAcquire, ldaddRelease, ldaddBoth, staddWord,
  casWord, swpLockHeld, swpCounter, references = 1, prematureZero, bitsSet, bitsToggled, bitMistakes;
static unsigned exclusive32;
static unsigned long pairWord[2] __attribute__((aligned(16)));

#define LSE ".arch armv8.1-a\n"

static void *work(void *argument) {
  unsigned long self = (unsigned long)argument;
  unsigned long bit = 1ul << self;
  for (int round = 0; round < ROUNDS; round++) {
    unsigned long value, status;
    unsigned value32, status32;
    /* ldxr/stxr, and ldaxr/stlxr of 32 bits */
    __asm__ volatile("1: ldxr %0, [%2]\n add %0, %0, #1\n stxr %w1, %0, [%2]\n cbnz %w1, 1b"
                     : "=&r"(value), "=&r"(status) : "r"(&exclusive64) : "memory");
    __asm__ volatile("1: ldaxr %w0, [%2]\n add %w0, %w0, #1\n stlxr %w1, %w0, [%2]\n cbnz %w1, 1b"
                     : "=&r"(value32), "=&r"(status32) : "r"(&exclusive32) : "memory");
    /* ldaxp/stlxp of a pair, both words one more */
    unsigned long low, high;
    __asm__ volatile("1: ldaxp %0, %1, [%3]\n add %0, %0, #1\n add %1, %1, #1\n stlxp %w2, %0, %1, [%3]\n cbnz %w2, 1b"
                     : "=&r"(low), "=&r"(high), "=&r"(status) : "r"(pairWord) : "memory");
    /* ldadd in each order, and stadd */
    unsigned long one = 1, old;
    __asm__ volatile(LSE "ldadd %1, %0, [%2]" : "=&r"(old) : "r"(one), "r"(&ldaddPlain) : "memory");
    __asm__ volatile(LSE "ldadda %1, %0, [%2]" : "=&r"(old) : "r"(one), "r"(&ldaddAcquire) : "memory");
    __asm__ volatile(LSE "ldaddl %1, %0, [%2]" : "=&r"(old) : "r"(one), "r"(&ldaddRelease) : "memory");
    __asm__ volatile(LSE "ldaddal %1, %0, [%2]" : "=&r"(old) : "r"(one), "r"(&ldaddBoth) : "memory");
    __asm__ volatile(LSE "stadd %0, [%1]" : : "r"(one), "r"(&staddWord) : "memory");
    /* casal in a loop */
    unsigned long expected = __atomic_load_n(&casWord, __ATOMIC_RELAXED);
    for (;;) {
      unsigned long seen = expected;
      __asm__ volatile(LSE "casal %0, %2, [%1]" : "+r"(seen) : "r"(&casWord), "r"(expected + 1) : "memory");
      if (seen == expected) break;
      expected = seen;
    }
    /* A lock of swpa and stlr, around a count that isn't atomic */
    unsigned long taken;
    do __asm__ volatile(LSE "swpa %1, %0, [%2]" : "=&r"(taken) : "r"(one), "r"(&swpLockHeld) : "memory");
    while (taken);
    swpCounter = swpCounter + 1;
    __asm__ volatile("stlr xzr, [%0]" : : "r"(&swpLockHeld) : "memory");
    /* A reference copied and let go of, as a shared_ptr is: the count never comes to zero while the main thread holds one */
    __asm__ volatile(LSE "ldadd %1, %0, [%2]" : "=&r"(old) : "r"(one), "r"(&references) : "memory");
    unsigned long minusOne = (unsigned long)-1;
    __asm__ volatile(LSE "ldaddal %1, %0, [%2]" : "=&r"(old) : "r"(minusOne), "r"(&references) : "memory");
    if (old == 1) __atomic_add_fetch(&prematureZero, 1, __ATOMIC_SEQ_CST);
    /* Its own bit, set and cleared, and toggled: what was there before is what it left */
    __asm__ volatile(LSE "ldsetal %1, %0, [%2]" : "=&r"(old) : "r"(bit), "r"(&bitsSet) : "memory");
    if (old & bit) __atomic_add_fetch(&bitMistakes, 1, __ATOMIC_SEQ_CST);
    __asm__ volatile(LSE "ldclral %1, %0, [%2]" : "=&r"(old) : "r"(bit), "r"(&bitsSet) : "memory");
    if (!(old & bit)) __atomic_add_fetch(&bitMistakes, 1, __ATOMIC_SEQ_CST);
    __asm__ volatile(LSE "ldeoral %1, %0, [%2]" : "=&r"(old) : "r"(bit), "r"(&bitsToggled) : "memory");
    if (((old & bit) != 0) != (round % 2 != 0)) __atomic_add_fetch(&bitMistakes, 1, __ATOMIC_SEQ_CST);
  }
  return 0;
}

int main(void) {
  pthread_t threads[THREADS];
  for (long index = 0; index < THREADS; index++) pthread_create(&threads[index], 0, work, (void *)index);
  for (int index = 0; index < THREADS; index++) pthread_join(threads[index], 0);
  unsigned long total = THREADS * ROUNDS;
  say("ldxr/stxr", exclusive64, total);
  say("ldaxr/stlxr 32", exclusive32, total);
  say("ldaxp/stlxp", pairWord[0] + pairWord[1], 2 * total);
  say("ldadd", ldaddPlain, total);
  say("ldadda", ldaddAcquire, total);
  say("ldaddl", ldaddRelease, total);
  say("ldaddal", ldaddBoth, total);
  say("stadd", staddWord, total);
  say("casal", casWord, total);
  say("swpa lock", swpCounter, total);
  say("references", references, 1);
  say("never zero", prematureZero, 0);
  say("own bits", bitMistakes, 0);
  say("bits left", bitsSet, 0);
  return 0;
}
