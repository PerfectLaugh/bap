/* The threads of Windows, that CreateThread creates, and their objects,
   one after another, each of which prints its line:

   - create: 4 threads add under a critical section, and Sleep(0),
     whose exit codes main sums, after it waits for all of them;
   - events: main and a thread take turns, with the events of the
     automatic reset, strictly, while the thread waits on the event,
     at the mark of the scripts, win_waits, which taint the turns, see
     tools/testsuite/inputs/emu/threads-win;
   - semaphore: 3 threads wait on a semaphore, that main releases, and
     add under a mutex;
   - condition: a producer and a consumer of a queue, with an SRW lock
     and a condition variable, and a critical section and another one;
   - address: WaitOnAddress, and WakeByAddressSingle;
   - tls: the threads keep their own values in a slot of TLS, and read
     their own TEBs;
   - suspended: the thread, that is created suspended, runs after
     ResumeThread;
   - timeouts: the waits, that time out, at once, and as no thread
     wakes them;
   - exit: a thread exits with ExitThread, whose code main gets;
   - orphan: main exits with ExitThread, before the last thread, which
     returns 7, the code of the process.

   It is built with clang, and lld-link, without a libc, with the
   import libraries of threads-win.def, and of msvcrt.def, of loader:

   llvm-dlltool -m $MACHINE -k -d threads-win$X.def -l kernel32.lib
   llvm-dlltool -m $MACHINE -d loader/msvcrt.def -l msvcrt.lib
   clang --target=$TARGET -O1 -ffreestanding -fno-builtin \
     -fno-stack-protector -c threads-win.c -o threads-win.obj
   lld-link /entry:start /subsystem:console /nodefaultlib /debug:symtab \
     threads-win.obj \
     kernel32.lib msvcrt.lib /out:../bin/$TARGET-threads-win

   with TARGET=x86_64-pc-windows-msvc and MACHINE=i386:x86-64, and
   TARGET=i686-pc-windows-msvc, MACHINE=i386, and X=-x86, see
   threads-win.sh */

#define API __declspec(dllimport) __stdcall
typedef void *HANDLE;
typedef unsigned long DWORD;
typedef DWORD(__stdcall *START)(void *);

/* the fields, that the functions use */
typedef struct {
    void *debug;
    long lock;
    long recursion;
    void *owner;
    void *semaphore;
    unsigned long *spin;
} CRITICAL_SECTION;

__declspec(dllimport) int putchar(int);
API void ExitProcess(unsigned);
API HANDLE CreateThread(void *, __SIZE_TYPE__, START, void *, DWORD, DWORD *);
API void ExitThread(DWORD);
API DWORD GetCurrentThreadId(void);
API DWORD GetThreadId(HANDLE);
API int GetExitCodeThread(HANDLE, DWORD *);
API DWORD ResumeThread(HANDLE);
API int CloseHandle(HANDLE);
API void Sleep(DWORD);
API int SwitchToThread(void);
API DWORD WaitForSingleObject(HANDLE, DWORD);
API DWORD WaitForMultipleObjects(DWORD, HANDLE *, int, DWORD);
API HANDLE CreateEventA(void *, int, int, const char *);
API int SetEvent(HANDLE);
API int ResetEvent(HANDLE);
API HANDLE CreateMutexA(void *, int, const char *);
API int ReleaseMutex(HANDLE);
API HANDLE CreateSemaphoreA(void *, long, long, const char *);
API int ReleaseSemaphore(HANDLE, long, long *);
API void InitializeCriticalSection(CRITICAL_SECTION *);
API void EnterCriticalSection(CRITICAL_SECTION *);
API int TryEnterCriticalSection(CRITICAL_SECTION *);
API void LeaveCriticalSection(CRITICAL_SECTION *);
API void DeleteCriticalSection(CRITICAL_SECTION *);
API void InitializeSRWLock(void **);
API void AcquireSRWLockExclusive(void **);
API void ReleaseSRWLockExclusive(void **);
API void InitializeConditionVariable(void **);
API int SleepConditionVariableSRW(void **, void **, DWORD, unsigned long);
API int SleepConditionVariableCS(void **, CRITICAL_SECTION *, DWORD);
API void WakeConditionVariable(void **);
API void WakeAllConditionVariable(void **);
API int WaitOnAddress(volatile void *, void *, __SIZE_TYPE__, DWORD);
API void WakeByAddressSingle(void *);
API DWORD TlsAlloc(void);
API int TlsSetValue(DWORD, void *);
API void *TlsGetValue(DWORD);
API int TlsFree(DWORD);

#define INFINITE 0xFFFFFFFF

static void put(const char *s) {
    while (*s) putchar(*s++);
}

static void print(long long x) {
    char buf[24];
    int n = 0;
    unsigned long long u = x < 0 ? -x : x;
    if (x < 0) putchar('-');
    do {
        buf[n++] = '0' + u % 10;
        u /= 10;
    } while (u);
    while (n) putchar(buf[--n]);
}

static void line(const char *name, long long x) {
    put(name);
    putchar(' ');
    print(x);
    putchar('\n');
}

static HANDLE spawn(START fn, void *arg) {
    return CreateThread(0, 0, fn, arg, 0, 0);
}

/* the mark of the scripts, which they pause at, whose argument is the
   address of the data, that they taint */
__declspec(noinline) void win_waits(char *data, long *seed, long *mixed) {
    __asm__ volatile("" ::"r"(data), "r"(seed), "r"(mixed));
}

/* create */

static CRITICAL_SECTION section;
static long total;

static DWORD __stdcall adder(void *arg) {
    for (int i = 0; i < 1000; i++) {
        EnterCriticalSection(&section);
        /* the section is recursive */
        EnterCriticalSection(&section);
        long x = total;
        if (i % 100 == 0) Sleep(0);
        total = x + 1;
        LeaveCriticalSection(&section);
        LeaveCriticalSection(&section);
    }
    return 10 + (DWORD)(long long)arg;
}

static void create(void) {
    HANDLE threads[4];
    InitializeCriticalSection(&section);
    for (int i = 0; i < 4; i++) threads[i] = spawn(adder, (void *)(long long)i);
    WaitForMultipleObjects(4, threads, 1, INFINITE);
    long long codes = 0;
    for (int i = 0; i < 4; i++) {
        DWORD code;
        GetExitCodeThread(threads[i], &code);
        codes += code;
        CloseHandle(threads[i]);
    }
    DeleteCriticalSection(&section);
    put("create ");
    print(total);
    putchar(' ');
    print(codes);
    putchar('\n');
}

/* events */

#define ROUNDS 50
static HANDLE ping, pong;
static char turns[2 * ROUNDS];
static int taken;
static long seed = 5, mixed;

static DWORD __stdcall ponger(void *arg) {
    for (int i = 0; i < ROUNDS; i++) {
        WaitForSingleObject(ping, INFINITE);
        turns[taken++] = 1;
        SetEvent(pong);
    }
    /* the seed, that the scripts taint, goes to mixed in the thread */
    mixed = seed * 3 + taken;
    return 0;
}

static void events(void) {
    ping = CreateEventA(0, 0, 0, 0);
    pong = CreateEventA(0, 0, 0, 0);
    HANDLE thread = spawn(ponger, 0);
    /* the thread waits on ping */
    Sleep(0);
    win_waits(turns, &seed, &mixed);
    for (int i = 0; i < ROUNDS; i++) {
        turns[taken++] = 0;
        SetEvent(ping);
        WaitForSingleObject(pong, INFINITE);
    }
    WaitForSingleObject(thread, INFINITE);
    int ok = taken == 2 * ROUNDS;
    for (int i = 0; i < taken; i++)
        if (turns[i] != i % 2) ok = 0;
    if (mixed != 5 * 3 + 2 * ROUNDS) ok = 0;
    put(ok ? "events ok\n" : "events bad\n");
}

/* semaphore */

static HANDLE semaphore, mutex;
static int passed;

static DWORD __stdcall passer(void *arg) {
    WaitForSingleObject(semaphore, INFINITE);
    WaitForSingleObject(mutex, INFINITE);
    /* the mutex is recursive */
    WaitForSingleObject(mutex, INFINITE);
    int x = passed;
    Sleep(0);
    passed = x + 1;
    ReleaseMutex(mutex);
    ReleaseMutex(mutex);
    return 0;
}

static void semaphores(void) {
    HANDLE threads[3];
    semaphore = CreateSemaphoreA(0, 0, 3, 0);
    mutex = CreateMutexA(0, 0, 0);
    for (int i = 0; i < 3; i++) threads[i] = spawn(passer, 0);
    Sleep(0);
    int before = passed;
    long previous = -1;
    ReleaseSemaphore(semaphore, 3, &previous);
    int over = ReleaseSemaphore(semaphore, 1, 0) &&
               ReleaseSemaphore(semaphore, 3, 0);
    WaitForMultipleObjects(3, threads, 1, INFINITE);
    line("semaphore", before * 100 + previous * 10 + passed + over * 1000);
}

/* condition */

static void *lock, *nonempty;
static CRITICAL_SECTION cs;
static void *cs_cond;
static int queue[16], head, tail, consumed, cs_ready;

static DWORD __stdcall consumer(void *arg) {
    int sum = 0;
    for (int n = 0; n < 10; n++) {
        AcquireSRWLockExclusive(&lock);
        while (head == tail) SleepConditionVariableSRW(&nonempty, &lock, INFINITE, 0);
        sum += queue[head++ % 16];
        ReleaseSRWLockExclusive(&lock);
    }
    consumed = sum;
    /* the critical section and its condition variable */
    EnterCriticalSection(&cs);
    while (!cs_ready) SleepConditionVariableCS(&cs_cond, &cs, INFINITE);
    consumed += cs_ready;
    LeaveCriticalSection(&cs);
    return 0;
}

static void condition(void) {
    InitializeSRWLock(&lock);
    InitializeConditionVariable(&nonempty);
    InitializeConditionVariable(&cs_cond);
    InitializeCriticalSection(&cs);
    HANDLE thread = spawn(consumer, 0);
    for (int i = 1; i <= 10; i++) {
        AcquireSRWLockExclusive(&lock);
        queue[tail++ % 16] = i;
        WakeConditionVariable(&nonempty);
        ReleaseSRWLockExclusive(&lock);
        if (i % 3 == 0) Sleep(0);
    }
    Sleep(0);
    EnterCriticalSection(&cs);
    cs_ready = 100;
    WakeAllConditionVariable(&cs_cond);
    LeaveCriticalSection(&cs);
    WaitForSingleObject(thread, INFINITE);
    line("condition", consumed);
}

/* address */

static volatile long flag;
static long seen_flag;

static DWORD __stdcall waiter(void *arg) {
    long zero = 0;
    while (flag == 0) WaitOnAddress(&flag, &zero, sizeof flag, INFINITE);
    seen_flag = flag;
    return 0;
}

static void address(void) {
    HANDLE thread = spawn(waiter, 0);
    Sleep(0);
    flag = 42;
    WakeByAddressSingle((void *)&flag);
    WaitForSingleObject(thread, INFINITE);
    line("address", seen_flag);
}

/* tls */

static DWORD slot;
static int tls_ok = 1;
static volatile int tls_started;

/* NtTib.Self of the TEB */
static void *teb(void) {
    void *p;
#if defined(__x86_64__)
    __asm__ volatile("mov %%gs:0x30, %0" : "=r"(p));
#else
    __asm__ volatile("mov %%fs:0x18, %0" : "=r"(p));
#endif
    return p;
}

static void *tebs[3];

static DWORD __stdcall keeper(void *arg) {
    long long n = (long long)arg;
    TlsSetValue(slot, (void *)(n + 1000));
    tebs[n] = teb();
    __atomic_add_fetch(&tls_started, 1, __ATOMIC_SEQ_CST);
    while (tls_started < 3) Sleep(0);
    if ((long long)TlsGetValue(slot) != n + 1000) tls_ok = 0;
    if (teb() != tebs[n]) tls_ok = 0;
    return 0;
}

static void tls(void) {
    HANDLE threads[3];
    slot = TlsAlloc();
    TlsSetValue(slot, (void *)7);
    void *main_teb = teb();
    for (int i = 0; i < 3; i++)
        threads[i] = spawn(keeper, (void *)(long long)i);
    WaitForMultipleObjects(3, threads, 1, INFINITE);
    if ((long long)TlsGetValue(slot) != 7) tls_ok = 0;
    for (int i = 0; i < 3; i++) {
        if (tebs[i] == main_teb || tebs[i] == 0) tls_ok = 0;
        for (int j = 0; j < i; j++)
            if (tebs[i] == tebs[j]) tls_ok = 0;
    }
    TlsFree(slot);
    put(tls_ok ? "tls ok\n" : "tls bad\n");
}

/* suspended */

static volatile int ran;

static DWORD __stdcall runner(void *arg) {
    ran = 1;
    return 0;
}

static void suspended(void) {
    HANDLE thread = CreateThread(0, 0, runner, 0, 4, 0);
    for (int i = 0; i < 3; i++) SwitchToThread();
    int before = ran;
    DWORD count = ResumeThread(thread);
    WaitForSingleObject(thread, INFINITE);
    line("suspended", before * 100 + count * 10 + ran);
}

/* timeouts */

static void timeouts(void) {
    HANDLE event = CreateEventA(0, 1, 0, 0);
    DWORD now = WaitForSingleObject(event, 0);
    DWORD later = WaitForSingleObject(event, 10);
    SetEvent(event);
    DWORD set = WaitForSingleObject(event, 10);
    put("timeouts ");
    print(now);
    putchar(' ');
    print(later);
    putchar(' ');
    print(set);
    putchar('\n');
}

/* exit */

static DWORD worker_tid;

static DWORD __stdcall exiter(void *arg) {
    worker_tid = GetCurrentThreadId();
    ExitThread(5);
    return 1;
}

static void exits(void) {
    DWORD tid;
    HANDLE thread = CreateThread(0, 0, exiter, 0, 0, &tid);
    WaitForSingleObject(thread, INFINITE);
    DWORD code;
    GetExitCodeThread(thread, &code);
    int ok = tid == worker_tid && tid == GetThreadId(thread) &&
             tid != GetCurrentThreadId();
    line(ok ? "exit" : "exit bad", code);
}

/* orphan */

static DWORD __stdcall orphan(void *arg) {
    for (int i = 0; i < 3; i++) Sleep(0);
    put("orphan\n");
    return 7;
}

void start(void) {
    create();
    events();
    semaphores();
    condition();
    address();
    tls();
    suspended();
    timeouts();
    exits();
    spawn(orphan, 0);
    ExitThread(0);
}
