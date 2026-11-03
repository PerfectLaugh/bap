/* What links against a libc that is loaded, and then against the base environment, for Bap.Linux.BaseEnv:
     clang --target=<triple> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libplain.so libplain.c libfakec.so -o libplain.so */
#include <stddef.h>
extern size_t strlen(const char *);
size_t plain_length(const char *text) { return strlen(text); }
