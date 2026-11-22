/* A library that calls and takes the address of `late`, which it doesn't define: an IFUNC of libifneed.so, which needs this one, so
   that this is relocated before the library whose resolver picks what `late` is (testIfuncOfNeeder):
     clang --target=x86_64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libifdep.so -Wl,-z,undefs libifdep.c \
       -o libifdep.so */
int late(void);
int call_late(void) { return late(); }
void *address_of_late(void) { return (void *)late; }
