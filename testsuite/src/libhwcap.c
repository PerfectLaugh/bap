/* A function that a resolver chooses, which says what the resolver was called with: on ARM and PowerPC `AT_HWCAP`, and on RISC-V that
   and what `__riscv_hwprobe` may be, as glibc's loader calls one (testIfuncArguments):
     clang --target=<triple, of gnu, as clang has no ifunc of musl> -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libhwcap.so libhwcap.c -o libhwcap.so */
static unsigned long seen;
static unsigned long saw(void) { return seen; }
static unsigned long (*resolve(unsigned long hwcap))(void) {
  seen = hwcap;
  return saw;
}
unsigned long hwcap_seen(void) __attribute__((ifunc("resolve")));
