void __security_init_cookie(void);

/* KERNEL32, whose functions the startup code of mingw calls */
void GetSystemTimeAsFileTime(void *time);
unsigned int GetCurrentProcessId(void);
unsigned int GetCurrentThreadId(void);
void *GetCurrentProcess(void);
unsigned int GetTickCount(void);
int QueryPerformanceCounter(void *count);
unsigned int GetLastError(void);
void GetStartupInfoA(void *info);
void Sleep(unsigned int milliseconds);
void InitializeCriticalSection(void *section);
void DeleteCriticalSection(void *section);
void EnterCriticalSection(void *section);
void LeaveCriticalSection(void *section);
void *TlsGetValue(unsigned int index);
void *SetUnhandledExceptionFilter(void *filter);
int UnhandledExceptionFilter(void *info);
int TerminateProcess(void *process, unsigned int code);
void ExitProcess(unsigned int code) __attribute__((noreturn));
unsigned long VirtualQuery(const void *addr, void *buffer, unsigned long length);
int VirtualProtect(void *addr, unsigned long size, unsigned int protect, unsigned int *old);
int RtlAddFunctionTable(void *table, unsigned int count, unsigned long base);
void RtlCaptureContext(void *context);

/* msvcrt, whose functions the startup code of mingw calls */
void __set_app_type(int type);
void __setusermatherr(void *handler);
int __lconv_init(void);
void _lock(int lock);
void _unlock(int lock);
void *__dllonexit(void *func, void *begin, void *end);
void *_onexit(void *func);
void _amsg_exit(int code) __attribute__((noreturn));
void _cexit(void);
int __getmainargs(int *argc, char ***argv, char ***envp, int wildcard, void *info);
void _initterm(void *begin, void *end);
void *__iob_func(void);
int __C_specific_handler(void *record, void *frame, void *context, void *dispatch);
void *signal(int signum, void *handler);
