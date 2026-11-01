/* A function that a resolver chooses when it is loaded, for the loader of Bap.Linux.Library. Clang has no ifunc for a target of musl, and
   this has no libc: --target=x86_64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld libifunc.c -o libifunc.so */
static int chosen_implementation(void) { return 77; }
static void *pick(void) { return chosen_implementation; }
int chosen(void) __attribute__((ifunc("pick")));
int (*const chosen_pointer)(void) = chosen;
int through_plt(void) { return chosen(); }
int through_pointer(void) { return chosen_pointer(); }
