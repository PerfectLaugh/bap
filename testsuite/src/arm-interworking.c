/* Calls between ARM and Thumb, and the page of helpers that the kernel maps. */
#include <stdio.h>
__attribute__((target("arm"),noinline)) int in_arm(int x) { return x * 3 + 1; }
__attribute__((target("thumb"),noinline)) int in_thumb(int x) { return in_arm(x) + 100; }
__attribute__((target("arm"),noinline)) int arm_calls_thumb(int x) { return in_thumb(x) * 2; }
typedef void *(get_tls_t)(void); typedef int (cmpxchg_t)(int, int, volatile int *);
int main(void) { static volatile int word = 5;
  int (*volatile p)(int) = in_thumb;
  printf("%d %d %d\n", in_thumb(1), arm_calls_thumb(2), p(3));
  void *tp = (*(get_tls_t *)0xffff0fe0)(); printf("tls %d\n", tp != 0);
  int r = (*(cmpxchg_t *)0xffff0fc0)(5, 9, &word); printf("cas %d %d\n", r, word);
  r = (*(cmpxchg_t *)0xffff0fc0)(5, 7, &word); printf("cas %d %d\n", r != 0, word);
  printf("version %d\n", *(volatile int *)0xffff0ffc > 0); return 0; }
