/* PowerPC: 32-bit SysV or 64-bit ELFv2, either byte order */

#if defined(__powerpc64__)
#define WORD_SIZE 8
#else
#define WORD_SIZE 4
#endif

#if defined(__ASSEMBLER__)
#define SLOT(i) ((i) * WORD_SIZE)
#endif

/* the state is an array of words: the general purpose registers by their
   numbers, CR, XER, LR, CTR, the native stack pointer and the address of
   the landing */
#define SLOT_CR 32
#define SLOT_XER 33
#define SLOT_LR 34
#define SLOT_CTR 35
#define SLOT_NSP 36
#define SLOT_LAND 37
#define SLOT_CODE 38
#define STATE_SIZE 40

#define SYS_fork 2
#define SYS_read 3
#define SYS_write 4
#define SYS_mmap 90
#define SYS_wait4 114
#define SYS_exit_group 234

#ifndef __ASSEMBLER__

typedef unsigned long word;

#ifdef __BIG_ENDIAN__
#define BIG_ENDIAN_ARCH 1
#else
#define BIG_ENDIAN_ARCH 0
#endif

/* a register, or, if bit is not zero, its bit bit - 1 */
struct reg {
  const char *name;
  int slot, size, bit;
};

#define R(n) {"R" #n, n, WORD_SIZE, 0}
/* the bits of the field n of CR, LT is the most significant */
#define CR(n)                                                                 \
  {"CR" #n "LT", SLOT_CR, 4, 32 - 4 * n}, {"CR" #n "GT", SLOT_CR, 4, 31 - 4 * n}, \
      {"CR" #n "EQ", SLOT_CR, 4, 30 - 4 * n},                                 \
      {"CR" #n "UN", SLOT_CR, 4, 29 - 4 * n}
static const struct reg regs[] = {
    R(0),  R(2),  R(3),  R(4),  R(5),  R(6),  R(7),  R(8),  R(9),  R(10),
    R(11), R(12), R(13), R(14), R(15), R(16), R(17), R(18), R(19), R(20),
    R(21), R(22), R(23), R(24), R(25), R(26), R(27), R(28), R(29), R(30),
    R(31), {"LR", SLOT_LR, WORD_SIZE, 0}, {"CTR", SLOT_CTR, WORD_SIZE, 0},
    CR(0), CR(1), CR(2), CR(3), CR(4), CR(5), CR(6), CR(7),
    {"SO", SLOT_XER, 4, 32}, {"OV", SLOT_XER, 4, 31}, {"CA", SLOT_XER, 4, 30},
    {"OV32", SLOT_XER, 4, 20}, {"CA32", SLOT_XER, 4, 19},
};
#undef R
#undef CR

#define MAP_PRIVATE_ANON_FIXED 0x32

long sys(long n, long a, long b, long c, long d, long e, long f);

static long sys_fork(void) { return sys(SYS_fork, 0, 0, 0, 0, 0, 0); }

static void sys_wait(long pid, int *status) {
  sys(SYS_wait4, pid, (long)status, 0, 0, 0, 0);
}

/* QEMU notices the changes of the translated code */
static void flush_icache(void *p, unsigned long n) { (void)p, (void)n; }

static void initialize_state(word *s) { (void)s; }

#endif
