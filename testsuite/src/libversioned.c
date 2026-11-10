// A library of two versions of one function, the old one first, as glibc keeps them: `f@VER_1`, for what was linked to it, and the
// default `f@@VER_2`, which a reference to `f` alone is bound to (testVersionedSymbols).
__asm__(".symver f_old, f@VER_1");
__asm__(".symver f_new, f@@VER_2");

int f_old(void) { return 1; }
int f_new(void) { return 2; }
