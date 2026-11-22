/* A function of Thumb that only a pointer goes to: testsuite/obj/thumb-windows-pe.exe, of
     zig cc -target thumb-windows-gnu -O1 -g0 -c thumb.c -o thumb.obj
     lld-link /subsystem:console /entry:entry /nodefaultlib /debug:symtab /out:thumb-windows-pe.exe thumb.obj */
static int st = 7;
int arr[8] = {1, 2, 3};
__attribute__((noinline)) int callee(int x) { return x * 3 + st + arr[x & 7]; }
__attribute__((noinline)) int other(int x) { return callee(x) + callee(x + 1); }
int (*fp)(int) = other;
int entry(int x) { return callee(x) + fp(x); }
