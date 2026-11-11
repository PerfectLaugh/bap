/* A library that calls its own indirect function through its table, by name, which a definition that is to be had first takes the place
   of, as of any other name (testLinuxLibraries): its resolver reads what it picks, so that the compiler can't pick it itself. Clang has
   no ifunc for a target of musl, and this has no libc:
     --target=x86_64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld libifuncown.c -o libifuncown.so */
static int own_implementation(void) { return 77; }
static int (*volatile picked)(void) = own_implementation;
static void *pick(void) { return (void *)picked; }
int own(void) __attribute__((ifunc("pick")));
int call_own(void) { return own(); }
