/* What was linked to `f@VER_1` of libifver.so, an IFUNC, which a reference of that version is bound to what its resolver picks, as
   `ld.so` has it, rather than to the resolver (testVersionedIfunc):
     clang --target=aarch64-linux-gnu -shared -fPIC -nostdlib -O1 -fuse-ld=lld -Wl,-soname,libifveruse.so libifveruse.c -L. -lifver \
       -o libifveruse.so */
int f(void);
int g(void) { return f(); }
