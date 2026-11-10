/* What was linked to the old version of `f` of libversioned.so, `f@VER_1`, which it is bound to when it is loaded, rather than to the
   default `f@@VER_2` (testVersionedSymbols):
     clang --target=aarch64-linux-musl -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libuseold.so libuseold.c -L. -lversioned \
       -o libuseold.so */
__asm__(".symver f_old, f@VER_1");
extern int f_old(void);
int use_old(void) { return f_old(); }
