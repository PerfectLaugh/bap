// A library whose one function is an IFUNC of a version, `f@@VER_1`, which picks `impl` (testVersionedIfunc), of a target of glibc as
// clang has no ifunc for one of musl:
//   clang --target=aarch64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libifver.so \
//     -Wl,--version-script=libifver.map libifver.c -o libifver.so
static int impl(void) { return 42; }
static void *resolve(void) { return impl; }
int f(void) __attribute__((ifunc("resolve")));
