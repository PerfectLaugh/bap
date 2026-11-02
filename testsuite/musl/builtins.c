/* What musl has from elsewhere in the copy that zig keeps, or a compiler's runtime would give, as simply as it can be. */
typedef __SIZE_TYPE__ size_t;
void *memcpy(void *restrict d, const void *restrict s, size_t n) { char *a = d; const char *b = s; while (n--) *a++ = *b++; return d; }
void *memmove(void *d, const void *s, size_t n) { char *a = d; const char *b = s; if (a < b) while (n--) *a++ = *b++; else while (n--) a[n] = b[n]; return d; }
void *memset(void *d, int v, size_t n) { char *a = d; while (n--) *a++ = v; return d; }
int memcmp(const void *x, const void *y, size_t n) { const unsigned char *a = x, *b = y; for (; n; n--, a++, b++) if (*a != *b) return *a - *b; return 0; }
size_t strlen(const char *s) { size_t n = 0; while (s[n]) n++; return n; }
int strcmp(const char *a, const char *b) { for (; *a && *a == *b; a++, b++); return *(unsigned char *)a - *(unsigned char *)b; }
int strncmp(const char *a, const char *b, size_t n) { if (!n--) return 0; for (; *a && *b && n && *a == *b; a++, b++, n--); return *(unsigned char *)a - *(unsigned char *)b; }
char *strchr(const char *s, int c) { for (;; s++) { if (*s == (char)c) return (char *)s; if (!*s) return 0; } }
/* What a 32-bit target asks of compiler-rt, for what musl and the test divide. */
#if __SIZEOF_POINTER__ == 4
unsigned long long __udivmoddi4(unsigned long long n, unsigned long long d, unsigned long long *r) {
    unsigned long long q = 0, b = 1;
    if (d == 0) return 0;
    while (d < n && !(d >> 63)) { d <<= 1; b <<= 1; }
    while (b) { if (n >= d) { n -= d; q |= b; } d >>= 1; b >>= 1; }
    if (r) *r = n;
    return q;
}
unsigned long long __udivdi3(unsigned long long n, unsigned long long d) { return __udivmoddi4(n, d, 0); }
unsigned long long __umoddi3(unsigned long long n, unsigned long long d) { unsigned long long r = 0; __udivmoddi4(n, d, &r); return r; }
long long __divdi3(long long n, long long d) { unsigned long long q = __udivdi3(n < 0 ? -n : n, d < 0 ? -d : d); return ((n < 0) != (d < 0)) ? -(long long)q : q; }
long long __moddi3(long long n, long long d) { unsigned long long r = __umoddi3(n < 0 ? -n : n, d < 0 ? -d : d); return n < 0 ? -(long long)r : r; }
#endif
int __bap_builtins_present;
#include <sys/syscall.h>
long syscall(long, ...);
int getpid(void) { return syscall(SYS_getpid); }
unsigned getuid(void) { return syscall(SYS_getuid); }
void _exit(int code) { for (;;) syscall(SYS_exit_group, code); }
__attribute__((visibility("hidden"))) int __mprotect(void *address, size_t size, int protection) { return syscall(SYS_mprotect, address, size, protection); }
int getppid(void) { return syscall(SYS_getppid); }
int close(int fd) { return syscall(SYS_close, fd); }
int madvise(void *address, size_t size, int advice) { return syscall(SYS_madvise, address, size, advice); }
int mprotect(void *address, size_t size, int protection) { return syscall(SYS_mprotect, address, size, protection); }
#ifdef SYS_unlink
int unlink(const char *path) { return syscall(SYS_unlink, path); }
#else
int unlink(const char *path) { return syscall(SYS_unlinkat, -100, path, 0); }
#endif
int pipe(int ends[2]) {
#if defined(SYS_pipe) && !defined(__mips__)
  return syscall(SYS_pipe, ends);
#else
  return syscall(SYS_pipe2, ends, 0);
#endif
}
