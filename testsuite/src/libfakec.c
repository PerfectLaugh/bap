/* A libc that has some of the names of the base environment, with what isn't what they do, for Bap.Linux.BaseEnv: what is linked against
   the base environment has its own, and what isn't has these.
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libfakec.so libfakec.c -o libfakec.so */
#include <stddef.h>
size_t strlen(const char *text) { (void)text; return 999; }
void *malloc(size_t size) { (void)size; return 0; }
