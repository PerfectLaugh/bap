/* A library whose IFUNC `late` a library that it needs, libifdep.so, is bound to (testIfuncOfNeeder). Its resolver reads what it picks
   from a pointer that is relocated, so that it picks nothing until its library is. Clang has no ifunc for a target of musl, and this
   has no libc:
     clang --target=x86_64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libifneed.so libifneed.c -L. -lifdep \
       -o libifneed.so */
int call_late(void);
void *address_of_late(void);
static int implementation(void) { return 77; }
static int (*volatile picked)(void) = implementation;
static void *pick(void) { return (void *)picked; }
int late(void) __attribute__((ifunc("pick")));
int through_needed(void) { return call_late(); }
int same_address(void) { return address_of_late() == (void *)late; }
