/* Thread-local storage in a library, in the model that needs a static offset, for the loader of Bap.Linux.Library:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -ftls-model=initial-exec -fuse-ld=lld libtls.c -o libtls.so */
__thread int per_thread = 3;
__thread int per_thread_zero;
__thread long long per_thread_aligned __attribute__((aligned(64))) = 5;
int get(void) { return per_thread; }
int set(int value) { per_thread = value; return per_thread; }
int get_zero(void) { return per_thread_zero; }
int aligned_right(void) { return ((unsigned long)&per_thread_aligned & 63) == 0 && per_thread_aligned == 5; }
