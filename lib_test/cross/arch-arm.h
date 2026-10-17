/* ARM: AArch32 in the A32 state, little endian, EABI */

#if defined(__ASSEMBLER__)
#define SLOT(i) ((i) * 4)
#endif

/* the state is an array of words: R0-R12 by their numbers, LR, the APSR,
   the native stack pointer, the address of the landing and the address of
   the code, SP holds the state, so the instructions can't use it */
#define SLOT_LR 14
#define SLOT_APSR 16
#define SLOT_NSP 17
#define SLOT_LAND 18
#define SLOT_CODE 19
#define STATE_SIZE 24

/* the A32 and T32 runners have an epilogue in the other state, see
   runner.c */
#define ALT_EPILOGUE 1

#define SYS_fork 2
#define SYS_read 3
#define SYS_write 4
#define SYS_wait4 114
#define SYS_mmap 192 /* mmap2, the offset is in pages */
#define SYS_exit_group 248

#ifndef __ASSEMBLER__

typedef unsigned long word;

#define BIG_ENDIAN_ARCH 0

/* a register, or, if bit is not zero, its bit bit - 1 */
struct reg {
  const char *name;
  int slot, size, bit;
};

#define R(n) {"R" #n, n, 4}
static const struct reg regs[] = {
    R(0),
    R(1),
    R(2),
    R(3),
    R(4),
    R(5),
    R(6),
    R(7),
    R(8),
    R(9),
    R(10),
    R(11),
    R(12),
    {"LR", SLOT_LR, 4},
    {"NF", SLOT_APSR, 4, 32},
    {"ZF", SLOT_APSR, 4, 31},
    {"CF", SLOT_APSR, 4, 30},
    {"VF", SLOT_APSR, 4, 29},
    {"QF", SLOT_APSR, 4, 28},
};
#undef R

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
