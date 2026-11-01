/* What a libc has for `__tls_get_addr`, by what a host writes in `rt_blocks`: where each module's block is, for the thread that runs. */
typedef __SIZE_TYPE__ size_t;
char *rt_blocks[16];
#if defined(__riscv)
#define DTP_OFFSET 0x800
#elif defined(__mips__) || defined(__powerpc__)
#define DTP_OFFSET 0x8000
#else
#define DTP_OFFSET 0
#endif
void *__tls_get_addr(size_t *entry) { return rt_blocks[entry[0]] + entry[1] + DTP_OFFSET; }
#if defined(__i386__)
__attribute__((regparm(1))) void *___tls_get_addr(size_t *entry) { return rt_blocks[entry[0]] + entry[1]; }
#endif
