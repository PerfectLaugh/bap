/* The system calls of Linux, that the threads of threads-weird.c call,
   on each target: syscall6, which returns the negated number of the
   error, as x86 does, also on MIPS and PowerPC, which flag the errors,
   spawn, whose child runs fn(arg) on its stack, and exits, and the
   thread pointer, whose block of TLS starts with its address, which
   clone sets, with tls_arg, and init_tls sets for main, on x86, where
   the descriptor of the segment of GS has it, and start_main, which
   calls __libc_start_main, as _start does, e.g., of glibc of PowerPC,
   which passes main in startup_info, and the stack of the entry. */

typedef int (*main_t)(int, char **, char **);
int __libc_start_main(main_t, int, char **, void (*)(void), void (*)(void),
                      void (*)(void), void *);

#if !defined(__powerpc__)
static void start_main(main_t main) { __libc_start_main(main, 0, 0, 0, 0, 0, 0); }
#endif

#if defined(__x86_64__)
#define SYS_clone 56
#define SYS_clone3 435
#define SYS_exit 60
#define SYS_futex 202
#define SYS_sched_yield 24
#define SYS_set_tid_address 218

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    long r;
    register long r10 __asm__("r10") = d;
    register long r8 __asm__("r8") = e;
    register long r9 __asm__("r9") = f;
    __asm__ volatile("syscall"
                     : "=a"(r)
                     : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10), "r"(r8),
                       "r"(r9)
                     : "rcx", "r11", "memory");
    return r;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    long r;
    register long r10 __asm__("r10") = (long)ctid;
    register long r8 __asm__("r8") = (long)tls;
    register long r12 __asm__("r12") = arg;
    register long r13 __asm__("r13") = (long)fn;
    __asm__ volatile("syscall\n"
                     "test %%rax, %%rax\n"
                     "jnz 1f\n"
                     "xor %%ebp, %%ebp\n"
                     "mov %%r12, %%rdi\n"
                     "call *%%r13\n"
                     "mov $60, %%eax\n"
                     "xor %%edi, %%edi\n"
                     "syscall\n"
                     "1:\n"
                     : "=a"(r)
                     : "a"(SYS_clone), "D"(flags), "S"(stack), "d"(ptid),
                       "r"(r10), "r"(r8), "r"(r12), "r"(r13)
                     : "rcx", "r11", "memory");
    return r;
}

static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mov %%fs:0, %0" : "=r"(p));
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }

#elif defined(__i386__)
#define SYS_clone 120
#define SYS_clone3 435
#define SYS_exit 1
#define SYS_futex 240
#define SYS_sched_yield 158
#define SYS_set_tid_address 258
#define SYS_set_thread_area 243

/* int 0x80, with the sixth argument in EBP, which is the frame pointer,
   so it is 0 here */
static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    long r;
    __asm__ volatile("int $0x80"
                     : "=a"(r)
                     : "a"(n), "b"(a), "c"(b), "d"(c), "S"(d), "D"(e)
                     : "memory");
    return r;
}

/* the child pops fn, after which arg is its argument, on its stack */
static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    long r;
    long *sp = (long *)stack - 4;
    sp[0] = (long)fn;
    sp[1] = arg;
    __asm__ volatile("int $0x80\n"
                     "test %%eax, %%eax\n"
                     "jnz 1f\n"
                     "xor %%ebp, %%ebp\n"
                     "pop %%eax\n"
                     "call *%%eax\n"
                     "mov $1, %%eax\n"
                     "xor %%ebx, %%ebx\n"
                     "int $0x80\n"
                     "1:\n"
                     : "=a"(r)
                     : "a"(SYS_clone), "b"(flags), "c"(sp), "d"(ptid),
                       "S"(tls), "D"(ctid)
                     : "memory");
    return r;
}

static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mov %%gs:0, %0" : "=r"(p));
    return p;
}

/* the struct user_desc of set_thread_area, of the segment of 4 GiB */
struct user_desc {
    unsigned entry;
    unsigned base;
    unsigned limit;
    unsigned flags;
};

static struct user_desc descs[8];
static unsigned tls_entry;

static void init_tls(void *block) {
    struct user_desc d = {-1u, (unsigned)block, 0xfffff, 0x51};
    syscall6(SYS_set_thread_area, (long)&d, 0, 0, 0, 0, 0);
    tls_entry = d.entry;
    __asm__ volatile("mov %0, %%gs" ::"r"(d.entry * 8 + 3));
}

static void *tls_arg(int i, void *block) {
    struct user_desc d = {tls_entry, (unsigned)block, 0xfffff, 0x51};
    descs[i] = d;
    return &descs[i];
}

#elif defined(__aarch64__)
#define SYS_clone 220
#define SYS_clone3 435
#define SYS_exit 93
#define SYS_futex 98
#define SYS_sched_yield 124
#define SYS_set_tid_address 96

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long x8 __asm__("x8") = n;
    register long x0 __asm__("x0") = a;
    register long x1 __asm__("x1") = b;
    register long x2 __asm__("x2") = c;
    register long x3 __asm__("x3") = d;
    register long x4 __asm__("x4") = e;
    register long x5 __asm__("x5") = f;
    __asm__ volatile("svc #0"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x5)
                     : "memory");
    return x0;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    register long x8 __asm__("x8") = SYS_clone;
    register long x0 __asm__("x0") = flags;
    register long x1 __asm__("x1") = (long)stack;
    register long x2 __asm__("x2") = (long)ptid;
    register long x3 __asm__("x3") = (long)tls;
    register long x4 __asm__("x4") = (long)ctid;
    register long x19 __asm__("x19") = arg;
    register long x20 __asm__("x20") = (long)fn;
    __asm__ volatile("svc #0\n"
                     "cbnz x0, 1f\n"
                     "mov x29, #0\n"
                     "mov x0, x19\n"
                     "blr x20\n"
                     "mov x8, #93\n"
                     "mov x0, #0\n"
                     "svc #0\n"
                     "1:\n"
                     : "+r"(x0)
                     : "r"(x8), "r"(x1), "r"(x2), "r"(x3), "r"(x4), "r"(x19),
                       "r"(x20)
                     : "x30", "memory");
    return x0;
}

static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mrs %0, tpidr_el0" : "=r"(p));
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }

#elif defined(__arm__)
#define SYS_clone 120
#define SYS_clone3 435
#define SYS_exit 1
#define SYS_futex 240
#define SYS_sched_yield 158
#define SYS_set_tid_address 256

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long r7 __asm__("r7") = n;
    register long r0 __asm__("r0") = a;
    register long r1 __asm__("r1") = b;
    register long r2 __asm__("r2") = c;
    register long r3 __asm__("r3") = d;
    register long r4 __asm__("r4") = e;
    register long r5 __asm__("r5") = f;
    __asm__ volatile("svc #0"
                     : "+r"(r0)
                     : "r"(r7), "r"(r1), "r"(r2), "r"(r3), "r"(r4), "r"(r5)
                     : "memory");
    return r0;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    register long r7 __asm__("r7") = SYS_clone;
    register long r0 __asm__("r0") = flags;
    register long r1 __asm__("r1") = (long)stack;
    register long r2 __asm__("r2") = (long)ptid;
    register long r3 __asm__("r3") = (long)tls;
    register long r4 __asm__("r4") = (long)ctid;
    register long r5 __asm__("r5") = (long)fn;
    register long r6 __asm__("r6") = arg;
    __asm__ volatile("svc #0\n"
                     "cmp r0, #0\n"
                     "bne 1f\n"
                     "mov r11, #0\n"
                     "mov r0, r6\n"
                     "blx r5\n"
                     "mov r7, #1\n"
                     "mov r0, #0\n"
                     "svc #0\n"
                     "1:\n"
                     : "+r"(r0)
                     : "r"(r7), "r"(r1), "r"(r2), "r"(r3), "r"(r4), "r"(r5),
                       "r"(r6)
                     : "lr", "memory", "cc");
    return r0;
}

static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mrc p15, 0, %0, c13, c0, 3" : "=r"(p));
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }

#elif defined(__mips__)
#if _MIPS_SIM == _ABIO32
#define SYS_BASE 4000
#define SYS_clone (SYS_BASE + 120)
#define SYS_exit (SYS_BASE + 1)
#define SYS_futex (SYS_BASE + 238)
#define SYS_sched_yield (SYS_BASE + 162)
#define SYS_set_tid_address (SYS_BASE + 252)
#else
#define SYS_BASE 5000
#define SYS_clone (SYS_BASE + 55)
#define SYS_exit (SYS_BASE + 58)
#define SYS_futex (SYS_BASE + 194)
#define SYS_sched_yield (SYS_BASE + 23)
#define SYS_set_tid_address (SYS_BASE + 212)
#endif
#define SYS_clone3 (SYS_BASE + 435)

/* the error is in A3, and its number in V0; the fifth and the sixth
   arguments of o32 are on the stack, after the space of the four
   ones in the registers, and in A4 and A5 of n64 */
static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long v0 __asm__("$2") = n;
    register long a0 __asm__("$4") = a;
    register long a1 __asm__("$5") = b;
    register long a2 __asm__("$6") = c;
    register long a3 __asm__("$7") = d;
#if _MIPS_SIM == _ABIO32
    __asm__ volatile(".set noreorder\n"
                     "addiu $sp, $sp, -32\n"
                     "sw %5, 16($sp)\n"
                     "sw %6, 20($sp)\n"
                     "syscall\n"
                     "addiu $sp, $sp, 32\n"
                     ".set reorder\n"
                     : "+r"(v0), "+r"(a3)
                     : "r"(a0), "r"(a1), "r"(a2), "r"(e), "r"(f)
                     : "$1", "$3", "$8", "$9", "$10", "$11", "$12", "$13",
                       "$14", "$15", "$24", "$25", "hi", "lo", "memory");
#else
    register long a4 __asm__("$8") = e;
    register long a5 __asm__("$9") = f;
    __asm__ volatile("syscall"
                     : "+r"(v0), "+r"(a3)
                     : "r"(a0), "r"(a1), "r"(a2), "r"(a4), "r"(a5)
                     : "$1", "$3", "$10", "$11", "$12", "$13", "$14", "$15",
                       "$24", "$25", "hi", "lo", "memory");
#endif
    return a3 ? -v0 : v0;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    register long v0 __asm__("$2") = SYS_clone;
    register long a0 __asm__("$4") = flags;
    register long a1 __asm__("$5") = (long)stack;
    register long a2 __asm__("$6") = (long)ptid;
    register long a3 __asm__("$7") = (long)tls;
    register long s0 __asm__("$16") = (long)fn;
    register long s1 __asm__("$17") = arg;
#if _MIPS_SIM == _ABIO32
    __asm__ volatile(".set noreorder\n"
                     "addiu $sp, $sp, -32\n"
                     "sw %5, 16($sp)\n"
                     "syscall\n"
                     "bnez $7, 1f\n"
                     "nop\n"
                     "bnez $2, 1f\n"
                     "nop\n"
                     "move $4, $17\n"
                     "move $25, $16\n"
                     "jalr $25\n"
                     "nop\n"
                     "li $2, 4001\n"
                     "li $4, 0\n"
                     "syscall\n"
                     "1:\n"
                     "addiu $sp, $sp, 32\n"
                     ".set reorder\n"
                     : "+r"(v0), "+r"(a3)
                     : "r"(a0), "r"(a1), "r"(a2), "r"(ctid), "r"(s0),
                       "r"(s1)
                     : "$1", "$3", "$8", "$9", "$10", "$11", "$12", "$13",
                       "$14", "$15", "$24", "$25", "$31", "hi", "lo",
                       "memory");
#else
    register long a4 __asm__("$8") = (long)ctid;
    __asm__ volatile(".set noreorder\n"
                     "syscall\n"
                     "bnez $7, 1f\n"
                     "nop\n"
                     "bnez $2, 1f\n"
                     "nop\n"
                     "move $4, $17\n"
                     "move $25, $16\n"
                     "jalr $25\n"
                     "nop\n"
                     "li $2, 5058\n"
                     "li $4, 0\n"
                     "syscall\n"
                     "1:\n"
                     ".set reorder\n"
                     : "+r"(v0), "+r"(a3)
                     : "r"(a0), "r"(a1), "r"(a2), "r"(a4), "r"(s0), "r"(s1)
                     : "$1", "$3", "$9", "$10", "$11", "$12", "$13", "$14",
                       "$15", "$24", "$25", "$31", "hi", "lo", "memory");
#endif
    return a3 ? -v0 : v0;
}

/* UserLocal, which the kernel sets */
static void *thread_pointer(void) {
    void *p;
    __asm__ volatile(".set push\n"
                     ".set mips32r2\n"
                     "rdhwr $3, $29\n"
                     ".set pop\n"
                     "move %0, $3"
                     : "=r"(p)
                     :
                     : "$3");
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }

#elif defined(__powerpc__)
#define SYS_clone 120
#define SYS_clone3 435
#define SYS_exit 1
#define SYS_futex 221
#define SYS_sched_yield 158
#define SYS_set_tid_address 232

/* the error is in SO of CR0, and its number in R3 */
static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long r0 __asm__("r0") = n;
    register long r3 __asm__("r3") = a;
    register long r4 __asm__("r4") = b;
    register long r5 __asm__("r5") = c;
    register long r6 __asm__("r6") = d;
    register long r7 __asm__("r7") = e;
    register long r8 __asm__("r8") = f;
    __asm__ volatile("sc\n"
                     "bns+ 1f\n"
                     "neg 3, 3\n"
                     "1:\n"
                     : "+r"(r0), "+r"(r3), "+r"(r4), "+r"(r5), "+r"(r6),
                       "+r"(r7), "+r"(r8)
                     :
                     : "r9", "r10", "r11", "r12", "cr0", "ctr", "memory");
    return r3;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    register long r0 __asm__("r0") = SYS_clone;
    register long r3 __asm__("r3") = flags;
    register long r4 __asm__("r4") = (long)stack;
    register long r5 __asm__("r5") = (long)ptid;
    register long r6 __asm__("r6") = (long)tls;
    register long r7 __asm__("r7") = (long)ctid;
    register long r30 __asm__("r30") = (long)fn;
    register long r31 __asm__("r31") = arg;
    __asm__ volatile("sc\n"
                     "bns+ 2f\n"
                     "neg 3, 3\n"
                     "b 1f\n"
                     "2:\n"
                     "cmpwi 3, 0\n"
                     "bne 1f\n"
                     "mr 3, 31\n"
                     "mtctr 30\n"
                     "bctrl\n"
                     "li 0, 1\n"
                     "li 3, 0\n"
                     "sc\n"
                     "1:\n"
                     : "+r"(r0), "+r"(r3), "+r"(r4), "+r"(r5), "+r"(r6),
                       "+r"(r7)
                     : "r"(r30), "r"(r31)
                     : "r8", "r9", "r10", "r11", "r12", "cr0", "ctr", "lr",
                       "memory");
    return r3;
}

struct startup_info {
    void *sda;
    main_t main;
    void *init;
    void *fini;
};

static void start_main(main_t main) {
    static struct startup_info info;
    long stack[4] = {0};
    info.main = main;
    /* main is the first argument too, for the generic stub */
    __libc_start_main(main, 0, 0, 0, 0, (void (*)(void))&info, stack);
}

/* R2, which the compiler doesn't use */
static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mr %0, 2" : "=r"(p));
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }

#elif defined(__riscv)
#define SYS_clone 220
#define SYS_clone3 435
#define SYS_exit 93
#define SYS_futex 98
#define SYS_sched_yield 124
#define SYS_set_tid_address 96

static long syscall6(long n, long a, long b, long c, long d, long e, long f) {
    register long a7 __asm__("a7") = n;
    register long a0 __asm__("a0") = a;
    register long a1 __asm__("a1") = b;
    register long a2 __asm__("a2") = c;
    register long a3 __asm__("a3") = d;
    register long a4 __asm__("a4") = e;
    register long a5 __asm__("a5") = f;
    __asm__ volatile("ecall"
                     : "+r"(a0)
                     : "r"(a7), "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(a5)
                     : "memory");
    return a0;
}

static long spawn(long flags, void *stack, int *ptid, int *ctid, void *tls,
                  void (*fn)(long), long arg) {
    register long a7 __asm__("a7") = SYS_clone;
    register long a0 __asm__("a0") = flags;
    register long a1 __asm__("a1") = (long)stack;
    register long a2 __asm__("a2") = (long)ptid;
    register long a3 __asm__("a3") = (long)tls;
    register long a4 __asm__("a4") = (long)ctid;
    register long s1 __asm__("s1") = (long)fn;
    register long s2 __asm__("s2") = arg;
    __asm__ volatile("ecall\n"
                     "bnez a0, 1f\n"
                     "li s0, 0\n"
                     "mv a0, s2\n"
                     "jalr s1\n"
                     "li a7, 93\n"
                     "li a0, 0\n"
                     "ecall\n"
                     "1:\n"
                     : "+r"(a0)
                     : "r"(a7), "r"(a1), "r"(a2), "r"(a3), "r"(a4), "r"(s1),
                       "r"(s2)
                     : "ra", "memory");
    return a0;
}

static void *thread_pointer(void) {
    void *p;
    __asm__ volatile("mv %0, tp" : "=r"(p));
    return p;
}

static void init_tls(void *block) {}
static void *tls_arg(int i, void *block) { return block; }
#endif
