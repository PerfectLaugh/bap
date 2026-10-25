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

#ifdef LOCK
/* the external function of starve.c, which the script replaces */
int lock(volatile long *p) { return 0; }
#endif

#ifdef PTHREAD
/* the functions of the threads of pthreads.c, which fail, as the
   emulator runs its own */
int pthread_create(void *t, const void *attr, void *(*fn)(void *), void *arg) {
    return 99;
}
int pthread_join(unsigned long t, void **r) { return 99; }
int pthread_detach(unsigned long t) { return 99; }
unsigned long pthread_self(void) { return 99; }
int pthread_equal(unsigned long a, unsigned long b) { return 0; }
int pthread_attr_init(void *a) { return 99; }
int pthread_attr_setdetachstate(void *a, int s) { return 99; }
int pthread_attr_destroy(void *a) { return 99; }
#endif
