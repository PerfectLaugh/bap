/* Names that are one function, as a loader's SDK has them, for the dispatch of Bap.Linux.Library by what is imported:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libalias.so libalias.c -o libalias.so
   Its constructor says that it ran, through what the host serves. */

extern void host_note(int);

int impl_value(int value) { return value + 1000; }
int alias_one(int value) __attribute__((alias("impl_value")));
int alias_two(int value) __attribute__((alias("impl_value")));

__attribute__((constructor)) static void alias_start(void) { host_note(1); }
