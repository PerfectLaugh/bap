/* A library with thread-local storage, which Bap.Linux.Library refuses, as what it needs is a libc's:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -ftls-model=initial-exec -fuse-ld=lld libtls.c -o libtls.so */
__thread int per_thread = 3;
int get(void) { return per_thread; }
