int __libc_start_main(int (*main) (int, char **, char **), int, char **, void *auxv);
void __stack_chk_fail(void) __attribute__((noreturn));
int __printf_chk(int flag, const char *format, ...);
int __fprintf_chk(void *stream, int flag, const char *format, ...);
int __sprintf_chk(char *str, int flag, unsigned long slen, const char *format, ...);
int __snprintf_chk(char *str, unsigned long maxlen, int flag, unsigned long slen, const char *format, ...);
