/* the output of the programs, that test the loaders, through putchar */

extern int putchar(int);
extern void exit(int);

static void print(const char *s) {
    while (*s) putchar(*s++);
}

static void hex(unsigned long x) {
    char buf[17];
    int i = 16;
    buf[i] = 0;
    do {
        buf[--i] = "0123456789abcdef"[x & 15];
        x >>= 4;
    } while (x);
    print(buf + i);
}

static void line(const char *name, unsigned long x) {
    print(name);
    putchar(' ');
    hex(x);
    putchar('\n');
}
