/* MIPS: o32 or n64, either byte order, with or without HI and LO (R6) */

#if defined(__ASSEMBLER__)
#define SLOT(i) ((i) * WORD_SIZE)
#endif

#if _MIPS_SIM == _ABI64
#define WORD_SIZE 8
#else
#define WORD_SIZE 4
#endif

/* the state is an array of words: the general purpose registers by their
   numbers, HI, LO, the native stack pointer, the address of the landing
   and the address of the code */
#define SLOT_HI 32
#define SLOT_LO 33
#define SLOT_NSP 34
#define SLOT_LAND 35
#define SLOT_CODE 36
#define STATE_SIZE 40

#if _MIPS_SIM == _ABI64
#define SYS_read 5000
#define SYS_write 5001
#define SYS_mmap 5009
#define SYS_fork 5056
#define SYS_wait4 5059
#define SYS_exit_group 5205
#else
#define SYS_read 4003
#define SYS_write 4004
#define SYS_fork 4002
#define SYS_mmap 4090
#define SYS_wait4 4114
#define SYS_exit_group 4246
#endif

#ifndef __ASSEMBLER__

typedef unsigned long word;

#ifdef __MIPSEB__
#define BIG_ENDIAN_ARCH 1
#else
#define BIG_ENDIAN_ARCH 0
#endif

/* a register, or, if bit is not zero, its bit bit - 1 */
struct reg {
  const char *name;
  int slot, size, bit;
};

#define R(n) {"R" #n, n, WORD_SIZE}
static const struct reg regs[] = {
    R(1),  R(2),  R(3),  R(4),  R(5),  R(6),  R(7),  R(8),  R(9),  R(10),
    R(11), R(12), R(13), R(14), R(15), R(16), R(17), R(18), R(19), R(20),
    R(21), R(22), R(23), R(24), R(25), R(26), R(27), R(28), R(30), R(31),
#if __mips_isa_rev < 6
    {"HI", SLOT_HI, WORD_SIZE},
    {"LO", SLOT_LO, WORD_SIZE},
#endif
};
#undef R

#define MAP_PRIVATE_ANON_FIXED 0x812

long sys(long n, long a, long b, long c, long d, long e, long f);

static long sys_fork(void) { return sys(SYS_fork, 0, 0, 0, 0, 0, 0); }

static void sys_wait(long pid, int *status) {
  sys(SYS_wait4, pid, (long)status, 0, 0, 0, 0);
}

/* QEMU notices the changes of the translated code */
static void flush_icache(void *p, unsigned long n) { (void)p, (void)n; }

static void initialize_state(word *s) { (void)s; }

#endif
