/* A weak function, which clang makes a weak external whose default is in the object, called and pointed to, and two
   that nothing here defines: testsuite/obj/x86_64-windows-weak.obj, of
     zig cc -target x86_64-windows-gnu -O1 -g0 -c weak.c -o x86_64-windows-weak.obj */
extern int ext(int);
extern int other(int);
__attribute__((weak)) int weakf(int x) { return x + 1; }
int (*fp)(int) = weakf;
int caller(int x) { return weakf(x) + ext(x) + other(x); }
