/* A library of i386 that isn't position-independent, whose call of what another library has is a relocation of its text of R_386_PC32,
   as GNU ld leaves one by default and glibc's loader takes (testLinuxLoaderOrder):
     clang --target=i686-linux-musl -shared -nostdlib -fno-pic -O1 -fuse-ld=lld -Wl,-z,notext libtextrel.c -o libtextrel.so */
int either_one(void);
int call_other(void) { return either_one() + 1; }
