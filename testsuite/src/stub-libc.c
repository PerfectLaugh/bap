/* the stand-in libc of thumb-crc-loop.c */

int putchar(int c) { return c; }
int __libc_start_main(int (*main)(int, char **, char **), int argc, char **argv,
                      void (*init)(void), void (*fini)(void),
                      void (*rtld_fini)(void), void *stack_end) {
    return main(argc, argv, 0);
}

void *memcpy(void *dst, const void *src, unsigned n) {
    for (unsigned i = 0; i < n; i++) ((char *)dst)[i] = ((const char *)src)[i];
    return dst;
}
