/* the output of the programs of PE, that test the loaders: putchar is
   called through the import address table, and ExitProcess through
   the thunk, that the linker makes */

__declspec(dllimport) int putchar(int);
void __stdcall ExitProcess(unsigned int);

static void print(const char *s) {
    while (*s) putchar(*s++);
}

static void hex(unsigned long long x) {
    char buf[17];
    int i = 16;
    buf[i] = 0;
    do {
        buf[--i] = "0123456789abcdef"[x & 15];
        x >>= 4;
    } while (x);
    print(buf + i);
}

static void line(const char *name, unsigned long long x) {
    print(name);
    putchar(' ');
    hex(x);
    putchar('\n');
}
