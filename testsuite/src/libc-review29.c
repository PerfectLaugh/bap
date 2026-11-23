// What Linux and the processor do of instructions of RISC-V, MIPS and PowerPC that a review found the machine ended the run of, or
// did wrong:
//   RISC-V: the time, `rdtime`, and of RV32 its upper half, is read, by CSRRS and CSRRC of x0 and by their immediate forms, and goes
//     on; the cycles and the instructions retired aren't a program's to read without an event of perf (scounteren), SIGILL, where
//     qemu-user gives them; an operation of floating point of a reserved rounding mode in its instruction, the returns from traps,
//     `wfi`, and the word of all the bits are SIGILL with ILL_ILLOPC at the instruction.
//   MIPS: `add`, `addi`, `sub` and those of doublewords that overflow are SIGFPE with FPE_INTOVF at the instruction, or at the
//     branch of one in a delay slot; `rdhwr` gives the processor, the step of `synci`, the count, which goes on, and its
//     resolution, and of another register is SIGILL; `cfc1` of FIR says what the FPU has; `ctc1` of a cause whose exception is
//     enabled is SIGFPE with the code of the cause, with the cause cleared (do_fpe), where qemu leaves it; and the instructions of
//     the kernel and of a coprocessor that isn't there are SIGILL of the kernel.
//   PowerPC: `dcbz` zeros the block that AT_DCACHEBSIZE says; the time base is read and goes on; VRSAVE is a program's; the
//     processor version is read; XER keeps its count of bytes, and has CA32 only of a 64-bit processor; a write of a floating point
//     register zeros the other half of its VSX register; `bctar` goes where TAR says; `darn` gives numbers; an instruction or a
//     register of the supervisor is SIGILL with ILL_PRVOPC (qemu-user says ILL_PRVREG of a register), and a register that isn't
//     there ILL_ILLOPC. The operations of quad precision that round to odd, are fused, convert and round to an integral value, and
//     the rounds of AES, are what the processor does, where the machine had none: as qemu has each but `xsnmsubqpo`, which it
//     rounds as `xsnmsubqp`, to the nearest (the last argument of its VSX_MADDQ of it), where the others round to odd.
// Each test is a function of assembly that is given a block of words to read and to write.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/auxv.h>

typedef unsigned long word;
extern char tests_begin[], tests_end[];
static sigjmp_buf back;
static const char *name;

static void handler(int signal, siginfo_t *info, void *context) {
  word address = (word)info->si_addr;
  // The address is of a fault: of a signal of the kernel, as MIPS sends, there is none.
  int inside = info->si_code != SI_KERNEL && address >= (word)tests_begin && address < (word)tests_end;
  printf("%s: signal %d code %d at a test %d\n", name, signal, info->si_code, inside);
  siglongjmp(back, 1);
}

#if defined(__mips__)
#define TEST(n, body) void n(word *); __asm__(".text\n.set push\n.set noreorder\n.set noat\n.globl " #n "\n.ent " #n "\n" #n ":\n" body "\n jr $31\n nop\n.end " #n "\n.set pop\n");
#elif defined(__powerpc__)
#define TEST(n, body) void n(word *); __asm__(".text\n.globl " #n "\n.type " #n ",@function\n" #n ":\n" body "\n blr\n");
#else
#define TEST(n, body) void n(word *); __asm__(".text\n.option push\n.option norvc\n.globl " #n "\n" #n ":\n" body "\n ret\n.option pop\n");
#endif

__asm__(".text\n.globl tests_begin\ntests_begin:\n");

#if defined(__riscv)
#if __riscv_xlen == 64
#define STORE "sd"
#define STEP "8"
#else
#define STORE "sw"
#define STEP "4"
#endif
// The time, twice, with work between, by each of the ways to read a CSR without writing it.
#define SPIN " li t0,1024\n1: addi t0,t0,-1\n bnez t0,1b\n"
TEST(time_csrrs, " csrrs a1,time,x0\n" SPIN " rdtime a2\n " STORE " a1,0(a0)\n " STORE " a2," STEP "(a0)\n")
TEST(time_csrrc, " csrrc a1,time,x0\n" SPIN " csrrc a2,time,x0\n " STORE " a1,0(a0)\n " STORE " a2," STEP "(a0)\n")
TEST(time_csrrsi, " csrrsi a1,time,0\n" SPIN " csrrci a2,time,0\n " STORE " a1,0(a0)\n " STORE " a2," STEP "(a0)\n")
TEST(time_write, " csrrw a1,time,a1\n")
TEST(time_set, " li a2,1\n csrrs a1,time,a2\n")
TEST(cycle, " rdcycle a1\n")
TEST(instret, " rdinstret a1\n")
#if __riscv_xlen == 32
TEST(time_high, " .word 0xc81025f3\n .word 0xc8102673\n sw a1,0(a0)\n sw a2,4(a0)\n")
#else
TEST(time_high, " .word 0xc81025f3\n")
#endif
// fadd.d and fcvt.d.w of the rounding modes 5 and 6, and fmadd.s of 5.
TEST(round5, " .word 0x02a5d553\n")
TEST(round6, " .word 0xd2056553\n")
TEST(round5_fused, " .word 0x00a5d543\n")
TEST(sret, " .word 0x10200073\n")
TEST(mret, " .word 0x30200073\n")
TEST(uret, " .word 0x00200073\n")
TEST(wfi, " .word 0x10500073\n")
TEST(sfence, " .word 0x12000073\n")
TEST(all_bits, " .word 0xffffffff\n")
#endif

#if defined(__mips__)
#if _MIPS_SIM == _ABI64
#define STORE "sd"
#define STEP "8"
#else
#define STORE "sw"
#define STEP "4"
#endif
TEST(add_overflow, " lui $8,0x7fff\n add $8,$8,$8\n")
TEST(addi_overflow, " lui $8,0x7fff\n ori $8,$8,0xffff\n addi $8,$8,1\n")
TEST(sub_overflow, " lui $8,0x8000\n li $9,1\n sub $8,$8,$9\n")
TEST(add_in_slot, " lui $8,0x7fff\n b 1f\n add $8,$8,$8\n1: nop\n")
TEST(no_overflow, " lui $8,0x8000\n li $9,1\n subu $8,$8,$9\n li $9,-1\n add $8,$9,$9\n lui $9,0x7fff\n addi $9,$9,-1\n " STORE " $8,0($4)\n " STORE " $9," STEP "($4)\n")
#if _MIPS_SIM == _ABI64
TEST(dadd_overflow, " li $8,1\n dsll32 $8,$8,30\n dadd $8,$8,$8\n")
TEST(daddi_overflow, " li $8,1\n dsll32 $8,$8,31\n daddi $8,$8,-1\n")
TEST(dsub_overflow, " li $8,1\n dsll32 $8,$8,31\n li $9,1\n dsub $8,$8,$9\n")
TEST(dadd_no_overflow, " lui $8,0x7fff\n dadd $8,$8,$8\n sd $8,0($4)\n")
#endif
// rdhwr $3, of the registers 0 to 3, the count again, and 29.
#define SPIN " li $8,64\n1: addiu $8,$8,-1\n bnez $8,1b\n nop\n"
TEST(hardware, " .word 0x7c03003b\n " STORE " $3,0($4)\n .word 0x7c03083b\n " STORE " $3," STEP "($4)\n .word 0x7c03183b\n " STORE " $3,2*" STEP "($4)\n"
     " .word 0x7c03e83b\n " STORE " $3,3*" STEP "($4)\n .word 0x7c03103b\n move $9,$3\n" SPIN " .word 0x7c03103b\n " STORE " $9,4*" STEP "($4)\n " STORE " $3,5*" STEP "($4)\n")
TEST(hardware_other, " .word 0x7c03203b\n")
TEST(fir, " .word 0x44480000\n " STORE " $8,0($4)\n")
// ctc1 to FCSR of a cause with its enable, of each of the five, and of one without; cfc1 of FCSR, and ctc1 of zero.
TEST(cause_invalid, " lui $8,1\n ori $8,$8,0x0800\n .word 0x44c8f800\n")
TEST(cause_division, " ori $8,$0,0x8400\n .word 0x44c8f800\n")
TEST(cause_overflow, " ori $8,$0,0x4200\n .word 0x44c8f800\n")
TEST(cause_underflow, " ori $8,$0,0x2100\n .word 0x44c8f800\n")
TEST(cause_inexact, " ori $8,$0,0x1080\n .word 0x44c8f800\n")
TEST(cause_disabled, " lui $8,1\n ori $8,$8,0xf000\n .word 0x44c8f800\n")
TEST(status_read, " .word 0x4448f800\n " STORE " $8,0($4)\n .word 0x44c0f800\n")
TEST(eret, " .word 0x42000018\n")
TEST(wait, " .word 0x42000020\n")
TEST(cache, " .word 0xbfa00000\n")
TEST(mfc2, " .word 0x48080000\n")
TEST(sdbbp, " .word 0x7000003f\n")
#endif

#if defined(__powerpc__)
#if defined(__powerpc64__)
#define STORE "std"
#define STEP "8"
#else
#define STORE "stw"
#define STEP "4"
#endif
#define SPIN " li 6,64\n mtctr 6\n1: bdnz 1b\n"
// dcbz of the address that the block has.
TEST(zero, " mr 4,3\n .long 0x7c0027ec\n")
// mfspr of 268, twice, and mftb of it.
TEST(time_base, " .long 0x7c8c42a6\n" SPIN " .long 0x7cac42a6\n " STORE " 4,0(3)\n " STORE " 5," STEP "(3)\n .long 0x7c8c42e6\n " STORE " 4,2*" STEP "(3)\n")
TEST(time_base_upper, " .long 0x7c8d42a6\n " STORE " 4,0(3)\n")
TEST(time_base_write, " .long 0x7c8c43a6\n")
TEST(vrsave, " li 4,-1\n .long 0x7c8043a6\n li 4,0\n .long 0x7c8042a6\n " STORE " 4,0(3)\n li 4,0\n .long 0x7c8043a6\n")
TEST(version, " .long 0x7c9f42a6\n " STORE " 4,0(3)\n")
TEST(sprg3, " li 4,-1\n .long 0x7c8342a6\n " STORE " 4,0(3)\n")
// mtxer of every bit, and of none, and what an addition that carries leaves.
TEST(xer, " mfxer 7\n li 4,0x7f\n mtxer 4\n mfxer 5\n " STORE " 5,0(3)\n li 4,0\n mtxer 4\n li 4,-1\n addic 4,4,1\n mfxer 5\n " STORE " 5," STEP "(3)\n mtxer 7\n")
// lfd, fmr, fadd, fcfid, mffs and lfs to f1, each after vs1 is made what vs34 is: both halves of vs1, by vs36.
#define FILL " .long 0x7c401e99\n .long 0xf0221496\n"
#define KEEP(at) " .long 0xf0810c91\n li 6," #at "\n .long 0x7c861f99\n"
TEST(float_writes, FILL " lfd 1,32(3)\n" KEEP(64) FILL " lfd 2,32(3)\n fmr 1,2\n" KEEP(80) FILL " fadd 1,2,2\n" KEEP(96)
     FILL " fcfid 1,2\n" KEEP(112) FILL " mffs 1\n" KEEP(128) FILL " lfs 1,40(3)\n" KEEP(144))
// bctar to what is after the instruction that says it wasn't taken.
#if defined(__powerpc64__)
TEST(branch_tar, " mflr 7\n bl 1f\n1: mflr 4\n mtlr 7\n addi 4,4,36\n .long 0x7c8fcba6\n li 5,1\n .long 0x4e800460\n li 5,2\n li 5,3\n li 6,4\n std 5,0(3)\n")
TEST(dscr, " .long 0x7c9102a6\n mr 7,4\n li 4,5\n .long 0x7c8303a6\n li 4,0\n .long 0x7c9102a6\n std 4,0(3)\n .long 0x7ce303a6\n")
TEST(darn, " .long 0x7c8105e6\n .long 0x7ca105e6\n .long 0x7cc005e6\n .long 0x7ce305e6\n std 4,0(3)\n std 5,8(3)\n std 6,16(3)\n std 7,24(3)\n")
#else
TEST(dscr, " .long 0x7c8302a6\n")
#endif
// Quad precision and AES: an operation of v2 and v3 to v4, which has the third operand of the fused ones, from and to the block.
#define VECTOR(n, w) TEST(n, " .long 0x7c401e99\n li 4,16\n .long 0x7c641e99\n li 4,32\n .long 0x7c841e99\n .long " #w "\n li 4,32\n .long 0x7c841f99\n")
#define VECTORS \
  X(xsaddqpo, 0xfc821809, 2) X(xssubqpo, 0xfc821c09, 2) X(xsmulqpo, 0xfc821849, 2) X(xsdivqpo, 0xfc821c49, 2) X(xssqrtqpo, 0xfc9b1649, 1) \
  X(xscvdpqp, 0xfc961688, 1) X(xscvqpdp, 0xfc941688, 1) X(xscvqpdpo, 0xfc941689, 1) X(xscvsdqp, 0xfc8a1688, 1) X(xscvudqp, 0xfc821688, 1) \
  X(xscvsqqp, 0xfc8b1688, 1) X(xscvuqqp, 0xfc831688, 1) X(xscvqpsdz, 0xfc991688, 1) X(xscvqpudz, 0xfc911688, 1) X(xscvqpswz, 0xfc891688, 1) \
  X(xscvqpuwz, 0xfc811688, 1) X(xscvqpsqz, 0xfc881688, 1) X(xscvqpuqz, 0xfc801688, 1) X(xsrqpi_away, 0xfc80100a, 1) \
  X(xsrqpi_current, 0xfc80160a, 1) X(xsrqpi_even, 0xfc81100a, 1) X(xsrqpi_zero, 0xfc81120a, 1) X(xsrqpi_up, 0xfc81140a, 1) \
  X(xsrqpi_down, 0xfc81160a, 1) X(xsrqpix_zero, 0xfc81120b, 1) X(xsmaddqp, 0xfc821b08, 2) X(xsmsubqp, 0xfc821b48, 2) \
  X(xsnmaddqp, 0xfc821b88, 2) X(xsnmsubqp, 0xfc821bc8, 2) X(xsmaddqpo, 0xfc821b09, 2) X(xsmsubqpo, 0xfc821b49, 2) \
  X(xsnmaddqpo, 0xfc821b89, 2) X(xsnmsubqpo, 0xfc821bc9, 2) \
  X(vcipher, 0x10821d08, 2) X(vcipherlast, 0x10821d09, 2) X(vncipher, 0x10821d48, 2) X(vncipherlast, 0x10821d49, 2) X(vsbox, 0x108205c8, 1)
#if defined(__powerpc64__)
#define X(n, w, k) VECTOR(n, w)
VECTORS
#undef X
#endif
TEST(mfmsr, " .long 0x7c8000a6\n")
TEST(mtmsr, " .long 0x7c800124\n")
TEST(rfid, " .long 0x4c000024\n")
TEST(tlbie, " .long 0x7c002264\n")
TEST(privileged_register, " .long 0x7c9ffaa6\n")
TEST(no_register, " .long 0x7c8202a6\n")
#endif

__asm__(".text\n.globl tests_end\ntests_end:\n");

// Runs a test on a block, and says the signal that it raised, if it did: whether it ended.
static int run(const char *what, void (*test)(word *), word *block) {
  name = what;
  if (sigsetjmp(back, 1)) return 0;
  test(block);
  return 1;
}

#if defined(__powerpc64__)
// The doublewords of quads, of doubles and of integers, by their edges: zeros, ones, what is between, the greatest and the least,
// infinities and NaNs, and what is at the ends of the integers of 32, 64 and 128 bits.
static const unsigned long long quads[][2] = {
  {0, 0}, {0x8000000000000000ull, 0}, {0x3fff000000000000ull, 0}, {0xbfff000000000000ull, 0}, {0x3fff000000000000ull, 1},
  {0x3ffe000000000000ull, 0}, {0x3ffd555555555555ull, 0x5555555555555555ull}, {0x4000800000000000ull, 0}, {0xc000800000000000ull, 0},
  {0x3fff800000000000ull, 0}, {0xbffe800000000000ull, 0}, {0x7ffeffffffffffffull, 0xffffffffffffffffull},
  {0xfffeffffffffffffull, 0xffffffffffffffffull}, {0, 1}, {0x0001000000000000ull, 0}, {0x7fff000000000000ull, 0},
  {0xffff000000000000ull, 0}, {0x7fff800000000000ull, 0x123}, {0x7fff400000000000ull, 0x456}, {0xffff000000000001ull, 0},
  {0x403dffffffffffffull, 0xffffffffffffffffull}, {0xc03e000000000000ull, 0}, {0xc03e000000000000ull, 1ull << 48},
  {0x403e000000000000ull, 0}, {0x403f000000000000ull, 0}, {0x401e000000000000ull, 0}, {0xc01e000000000000ull, 0},
  {0x401dffffffffc000ull, 0}, {0x401f000000000000ull, 0}, {0x407e000000000000ull, 0}, {0xc07e000000000000ull, 0},
  {0x407f000000000000ull, 0}, {0x43ff000000000000ull, 0x8000000000000000ull}, {0x3c00000000000000ull, 1},
  {0x4033123456789abcull, 0xdef0123456789abcull}, {0x3fd0000000000000ull, 0}, {0x4070ffffffffffffull, 0xfffffffffffffffeull},
  {0x7ff0000000000000ull, 0}, {0x7ff4000000000000ull, 1}, {0x7ff8000000000000ull, 2}, {0x0010000000000000ull, 0},
  {0x000fffffffffffffull, 7}, {0x8000000000000001ull, 9}, {0x3ff8000000000000ull, 0}, {0xc00c000000000000ull, 0},
  {0xffffffffffffffffull, 0xffffffffffffffffull}, {1, 0}, {0x7fffffffffffffffull, 0xffffffffffffffffull}, {0x4010000000000000ull, 0},
  {0x3ffe000000000000ull, 1}, {0x3ffdffffffffffffull, 0xffffffffffffffffull}, {0x4002400000000000ull, 0},
};
#define QUADS (sizeof quads / sizeof quads[0])

// What an operation makes of the values, of each with itself and with some of the others, all in two words.
static void vectors(const char *what, void (*test)(word *), int operands) {
  unsigned long long block[6], high = 0xcbf29ce484222325ull, low = high;
  for (unsigned first = 0; first < QUADS; first++)
    for (unsigned second = 0; second < (operands == 2 ? QUADS : 1); second++) {
      if (operands == 2 && (first * 7 + second * 3) % 5 != 0 && first != second) continue;
      unsigned other = operands == 2 ? second : first, third = (3 * first + 5 * second + 2) % QUADS;
      block[0] = quads[first][0], block[1] = quads[first][1], block[2] = quads[other][0], block[3] = quads[other][1];
      block[4] = quads[third][0], block[5] = quads[third][1];
      if (!run(what, test, (word *)block)) return;
      // The shift has every bit of a value, its sign too, in the lower bits of what follows.
      high = (high ^ block[4]) * 0x100000001b3ull, high ^= high >> 29;
      low = (low ^ block[5]) * 0x100000001b3ull, low ^= low >> 29;
    }
  printf("%s: %016llx %016llx\n", what, high, low);
}
#endif

static void faults(const char *what, void (*test)(word *)) {
  word block[8] = {0};
  if (run(what, test, block)) printf("%s: no signal\n", what);
}

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = handler;
  action.sa_flags = SA_SIGINFO | SA_NODEFER;
  for (int signal = 1; signal < 32; signal++)
    if (signal != SIGKILL && signal != SIGSTOP) sigaction(signal, &action, 0);
  setvbuf(stdout, 0, _IONBF, 0);
  word block[32] = {0};

#if defined(__riscv)
  if (run("time by csrrs", time_csrrs, block)) printf("time by csrrs: goes on %d\n", block[1] > block[0] && block[0] > 0);
  if (run("time by csrrc", time_csrrc, block)) printf("time by csrrc: goes on %d\n", block[1] > block[0] && block[0] > 0);
  if (run("time by immediates", time_csrrsi, block)) printf("time by immediates: goes on %d\n", block[1] > block[0] && block[0] > 0);
  faults("time written", time_write);
  faults("time set", time_set);
  faults("cycle", cycle);
  faults("instret", instret);
#if __riscv_xlen == 32
  if (run("timeh", time_high, block)) printf("timeh: the same twice %d\n", block[0] == block[1]);
#else
  faults("timeh", time_high);
#endif
  faults("rounding mode 5", round5);
  faults("rounding mode 6", round6);
  faults("rounding mode 5 fused", round5_fused);
  faults("sret", sret);
  faults("mret", mret);
  faults("uret", uret);
  faults("wfi", wfi);
  faults("sfence.vma", sfence);
  faults("all bits", all_bits);
#endif

#if defined(__mips__)
  faults("add", add_overflow);
  faults("addi", addi_overflow);
  faults("sub", sub_overflow);
  faults("add in a delay slot", add_in_slot);
  if (run("no overflow", no_overflow, block)) printf("no overflow: %lx %lx\n", block[0], block[1]);
#if _MIPS_SIM == _ABI64
  faults("dadd", dadd_overflow);
  faults("daddi", daddi_overflow);
  faults("dsub", dsub_overflow);
  if (run("dadd of words", dadd_no_overflow, block)) printf("dadd of words: %lx\n", block[0]);
#endif
  if (run("rdhwr", hardware, block))
    printf("rdhwr: processor %lu step %lu resolution %lu thread pointer %d count goes on %d\n", block[0], block[1], block[2],
           block[3] == (word)__builtin_thread_pointer(), (int)(block[5] - block[4]) > 0);
  faults("rdhwr of 4", hardware_other);
  if (run("fir", fir, block)) printf("fir: has %lx\n", (block[0] >> 16) & 0xff);
  {
    static const struct { const char *name; void (*test)(word *); } causes[] = {
      {"invalid cause", cause_invalid}, {"division cause", cause_division}, {"overflow cause", cause_overflow},
      {"underflow cause", cause_underflow}, {"inexact cause", cause_inexact}, {"cause that isn't enabled", cause_disabled}};
    for (unsigned index = 0; index < sizeof causes / sizeof causes[0]; index++) {
      faults(causes[index].name, causes[index].test);
      // What is left of the register: the causes that were taken are cleared before the signal.
      if (run("fcsr", status_read, block)) printf("fcsr: %lx\n", block[0] & 0xffffffff);
    }
  }
  faults("eret", eret);
  faults("wait", wait);
  faults("cache", cache);
  faults("mfc2", mfc2);
  faults("sdbbp", sdbbp);
#endif

#if defined(__powerpc__)
  // A block of the cache in the middle of bytes that aren't zero, from an address inside it.
  word size = getauxval(AT_DCACHEBSIZE);
  printf("block: %lu\n", size);
  if (size) {
    unsigned char *bytes = aligned_alloc(size, 3 * size);
    memset(bytes, 0xff, 3 * size);
    if (run("dcbz", zero, (word *)(bytes + size + 5))) {
      word first = 0, zeros = 0;
      for (word index = 0; index < 3 * size; index++)
        if (!bytes[index]) { if (!zeros) first = index; zeros++; }
      printf("dcbz: %d\n", first == size && zeros == size);
    }
    free(bytes);
  }
  if (run("time base", time_base, block)) printf("time base: goes on %d %d\n", block[1] > block[0], block[2] > block[1]);
  if (run("time base upper", time_base_upper, block)) printf("time base upper: read\n");
  faults("time base written", time_base_write);
  if (run("vrsave", vrsave, block)) printf("vrsave: %lx\n", block[0]);
  if (run("version", version, block)) printf("version: read %d\n", block[0] != 0);
  if (run("sprg3", sprg3, block)) printf("sprg3: %lx\n", block[0]);
  if (run("xer", xer, block)) printf("xer: %lx %lx\n", block[0], block[1]);
  {
    // The doublewords of a vector, a double and a single to load, and where what each write left is kept.
    unsigned long long *doubles = aligned_alloc(16, 256);
    memset(doubles, 0, 256);
    doubles[0] = 0x1111111111111111ull, doubles[1] = 0x2222222222222222ull, doubles[4] = 0x4000000000000000ull;
    *(unsigned *)&doubles[5] = 0x3f800000;
    if (run("float writes", float_writes, (word *)doubles)) {
      printf("float writes:");
      // The half that isn't the register's is the second in memory, as lxvd2x and stxvd2x have the doublewords in both byte orders.
      for (int index = 0; index < 6; index++)
        printf(" %llx", doubles[8 + 2 * index + 1]);
      printf("\n");
    }
    free(doubles);
  }
#if defined(__powerpc64__)
  if (run("bctar", branch_tar, block)) printf("bctar: %lu\n", block[0]);
  if (run("dscr", dscr, block)) printf("dscr: %lu\n", block[0]);
  if (run("darn", darn, block))
    printf("darn: numbers %d of a word %d failed %d\n", block[0] != block[1] && block[0] != -1ul && block[1] != -1ul, block[2] >> 32 == 0,
           block[3] == -1ul);
#else
  faults("dscr", dscr);
#endif
#if defined(__powerpc64__)
#define X(n, w, k) vectors(#n, n, k);
  VECTORS
#undef X
#endif
  faults("mfmsr", mfmsr);
  faults("mtmsr", mtmsr);
  faults("rfid", rfid);
  faults("tlbie", tlbie);
  faults("privileged register", privileged_register);
  faults("no register", no_register);
#endif
  return 0;
}
