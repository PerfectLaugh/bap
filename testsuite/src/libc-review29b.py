#!/usr/bin/env python3
# Makes libc-review29b.c: `python3 libc-review29b.py libc-review29b.c`. The instructions are in the lists below, as the assembler
# of LLVM (llvm-mc) takes them, or as words where it doesn't; the program that runs them is TEMPLATE, whose table and classes
# this fills.
import subprocess, re, sys

TEMPLATE = r'''// What a POWER10 does of the instructions that the machine had left to intrinsics that nothing served, which ended a run:
//   quad precision: `xsrqpxp`, which rounds to the double extended precision; `xvcvbf16spn` and `xvcvspbf16` of bfloat16; the
//     permute controls of `xxgenpcvbm` and of the other sizes; the estimates `vexptefp` and `vlogefp`, which are the power of 2 and
//     the logarithm rounded to the nearest, where qemu's power of 2 is a series that is off by more than the ISA lets it be;
//   the outer products of the matrix-multiply assist, of integers, of halves, of bfloat16, of singles and of doubles, with what
//     they accumulate and with the masks of their prefixed forms;
//   the atomic memory operations `lwat`, `ldat`, `stwat` and `stdat`, of each function that they have, as the ISA 3.0 has them: the
//     signed maximum and minimum of words are of words, the compare and swap stores RT+2 where memory isn't RT+1, the increment is
//     bounded by the word after and the decrement by the word before, and what is given for a bound that is met is the least word
//     or doubleword. qemu has others of these (it compares words as doublewords, stores RT+1, and so on), and isn't followed;
//   the decimal floating point, of 64 and of 128 bits: the arithmetic, the quantizations and the roundings by each mode, the
//     comparisons and the tests, the conversions, the shifts and the binary-coded decimals, with what each says in FPSCR. FR, which
//     says that a result was rounded up, is counted apart: qemu never sets it;
//   the signed decimals of the vector registers, `bcdadd.` and the rest, of operands that are valid, of which the result of the
//     others is undefined. Of the two that are unsigned, `bcdus.` and `bcdutrunc.`, a result that isn't zero is greater than it,
//     where qemu says less;
//   AMR, CTRL and PPR, which a program reads, and of which it writes the first and the priorities that it may of the last;
//   `hashst` and `hashchk`, which Linux has on for a program, and whose failure is SIGILL with ILL_ILLOPN (qemu-user has them
//     off, and its special purpose registers aren't those of Linux: it refuses AMR and gives another PPR); `copy`, and `paste.` to
//     memory that isn't of an accelerator, SIGBUS with BUS_OBJERR at the address; and what is of a facility that a program of a
//     POWER10 doesn't have, the vectored system call (which the machine doesn't say in AT_HWCAP2), the transactional memory, the
//     event-based branches and the branch history, or of an architecture after the ISA 3.1, SIGILL with ILL_ILLOPC.
// Each instruction is a word, or two, of the table, with what goes before and after it: it is put where it can run and called
// with registers from a block of doublewords, which has them back after. This file is made by libc-review29b.py from the list of
// the instructions; its table has their words as the assembler of LLVM has them.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>

typedef unsigned long long u64;
typedef unsigned __int128 u128;

enum { /*CLASSES*/ };

static const struct { const char *name; int count; unsigned words[7]; int class, cases; } table[] = {
/*TABLE*/
};

// Runs the code at r4 with the registers of the block at r3, and puts them back there:
//   in: FPSCR 6, f8 and f9 7, f4:f5 and v2 2, f6:f7 and v3 4, v4 8, v5 10, vs0 to vs3 12 (f1 14, f2 16, f3 18), r5 to r7 20, and
//     r4 is where 41 is; the condition register and FPSCR are as they were after, and 39 is zero; out: f1 24, f8 25, f9 26, CR 27, FPSCR 28, v4 29, vs0 to vs3 31, r5 48, r6 49.
void run_code(u64 *block, void *code);
__asm__(".text\n.globl run_code\n.type run_code,@function\nrun_code:\n"
        " mflr 0\n std 0,16(1)\n mfcr 0\n std 0,8(1)\n mtctr 4\n"
        " lfd 0,48(3)\n .long 0xfffe058e\n"   /* mtfsf 255,0,1,0 */
        " lfd 4,16(3)\n lfd 5,24(3)\n lfd 6,32(3)\n lfd 7,40(3)\n lfd 8,56(3)\n lfd 9,56(3)\n"
        " li 4,16\n .long 0x7c441e99\n li 4,32\n .long 0x7c641e99\n li 4,64\n .long 0x7c841e99\n li 4,80\n .long 0x7ca41e99\n"
        " li 4,96\n .long 0x7c041e98\n li 4,112\n .long 0x7c241e98\n li 4,128\n .long 0x7c441e98\n li 4,144\n .long 0x7c641e98\n"
        " li 4,0\n mtcr 4\n ld 5,160(3)\n ld 6,168(3)\n ld 7,176(3)\n addi 4,3,328\n std 3,-8(1)\n"
        " bctrl\n"
        " ld 3,-8(1)\n stfd 1,192(3)\n stfd 8,200(3)\n stfd 9,208(3)\n mfcr 4\n std 4,216(3)\n"
        " li 4,232\n .long 0x7c841f99\n li 4,248\n .long 0x7c041f98\n li 4,264\n .long 0x7c241f98\n li 4,280\n .long 0x7c441f98\n"
        " li 4,296\n .long 0x7c641f98\n std 5,384(3)\n std 6,392(3)\n mffs 0\n stfd 0,224(3)\n"
        " lfd 0,312(3)\n .long 0xfffe058e\n ld 0,8(1)\n mtcr 0\n ld 0,16(1)\n mtlr 0\n blr\n");

// What was written at r3 is what runs there: its block of the caches is flushed and invalidated.
void flush_code(void *code);
__asm__(".text\n.globl flush_code\n.type flush_code,@function\nflush_code:\n dcbf 0,3\n sync\n icbi 0,3\n isync\n blr\n");

static u64 state = 0x243f6a8885a308d3ull;
static u64 rnd(void) { state ^= state << 13; state ^= state >> 7; state ^= state << 17; return state; }
static u64 below(u64 n) { return rnd() % n; }
static u128 rnd128(void) { u128 high = rnd(); return high << 64 | rnd(); }

// The densely packed decimals: the declet of three digits is the least of those that are them.
static unsigned declet_of[1000];
static unsigned digits_of(unsigned b) {
  unsigned p = b >> 9 & 1, q = b >> 8 & 1, r = b >> 7 & 1, s = b >> 6 & 1, t = b >> 5 & 1, u = b >> 4 & 1, v = b >> 3 & 1, w = b >> 2 & 1,
           x = b >> 1 & 1, y = b & 1, high, middle, low;
  if (!v) high = 4 * p + 2 * q + r, middle = 4 * s + 2 * t + u, low = 4 * w + 2 * x + y;
  else if (!w && !x) high = 4 * p + 2 * q + r, middle = 4 * s + 2 * t + u, low = 8 + y;
  else if (!w) high = 4 * p + 2 * q + r, middle = 8 + u, low = 4 * s + 2 * t + y;
  else if (!x) high = 8 + r, middle = 4 * s + 2 * t + u, low = 4 * p + 2 * q + y;
  else if (!s && !t) high = 8 + r, middle = 8 + u, low = 4 * p + 2 * q + y;
  else if (!s) high = 8 + r, middle = 4 * p + 2 * q + u, low = 8 + y;
  else if (!t) high = 4 * p + 2 * q + r, middle = 8 + u, low = 8 + y;
  else high = 8 + r, middle = 8 + u, low = 8 + y;
  return 100 * high + 10 * middle + low;
}
static u128 power(int n) { u128 value = 1; while (n-- > 0) value *= 10; return value; }

// A decimal of a width, of a sign, a coefficient and an exponent, or an infinity (1), a quiet NaN (2) or a signaling one (3).
static u128 decimal(int width, int sign, u128 coefficient, int exponent, int kind) {
  int bits = width == 32 ? 6 : width == 64 ? 8 : 12, bias = width == 32 ? 101 : width == 64 ? 398 : 6176, precision = (width - 6 - bits) / 10 * 3 + 1;
  int rest = width - 6 - bits;
  u128 top = (u128)sign << (width - 1), field = 0, low = coefficient % power(precision - 1);
  for (int index = 0; index < rest / 10; index++, low /= 1000) field |= (u128)declet_of[low % 1000] << (10 * index);
  if (kind == 1) return top | (u128)30 << (width - 6);
  if (kind) return top | (u128)31 << (width - 6) | (u128)(kind == 3 ? 1 << (bits - 1) : 0) << rest | field;
  unsigned biased = exponent + bias, lead = coefficient / power(precision - 1), high = biased >> bits;
  unsigned combination = lead >= 8 ? 24 + 2 * high + (lead - 8) : 8 * high + lead;
  return top | (u128)combination << (width - 6) | (u128)(biased & ((1 << bits) - 1)) << rest | field;
}

// A decimal by its edges: the specials, zeros, coefficients of few digits and of all, and exponents by 0 and at both ends.
static u128 some_decimal(int width) {
  int bits = width == 32 ? 6 : width == 64 ? 8 : 12, bias = width == 32 ? 101 : width == 64 ? 398 : 6176, precision = (width - 6 - bits) / 10 * 3 + 1;
  int greatest = 3 * (1 << bits) - 1 - bias, sign = below(2), kind = below(100);
  if (kind < 6) return decimal(width, sign, 0, 0, 1);
  if (kind < 10) return decimal(width, sign, (u128[]){0, 7, 123456, power(precision - 1) - 1}[below(4)], 0, 2);
  if (kind < 13) return decimal(width, sign, (u128[]){0, 5, 99}[below(3)], 0, 3);
  if (kind < 18) return width == 128 ? rnd128() : rnd() >> (64 - width);
  if (kind < 26) return decimal(width, sign, 0, (int[]){0, -3, 5, greatest, -bias, (int)below(greatest + bias + 1) - bias}[below(6)], 0);
  int length = (int[]){1, 1, 2, 3, 5, precision / 2, precision - 1, precision, precision}[below(9)];
  u128 coefficient = below(10) < 7 ? power(length - 1) + rnd128() % (9 * power(length - 1))
    : (u128[]){power(length) - 1, power(length - 1), 5 * power(length - 1)}[below(3)];
  if (below(10) < 3) coefficient -= coefficient % power(length / 2);
  int where = below(100), exponent;
  if (where < 60) exponent = (int)below(2 * precision + 7) - precision - 3;
  else if (where < 75) exponent = (int[]){greatest, greatest - 1, greatest - precision + 1, greatest - length, greatest - 2}[below(5)];
  else if (where < 90) exponent = (int[]){-bias, -bias + 1, -bias + precision - 1, -bias + length, -bias + 3}[below(5)];
  else exponent = (int)below(greatest + bias + 1) - bias;
  return decimal(width, sign, coefficient, exponent, 0);
}

// Digits in nibbles, with a sign code in the last if `sign`: all valid, but for one digit if `spoil`.
static u128 some_digits(int nibbles, int sign, int spoil) {
  u128 value = 0;
  int zeros = below(10) < 3 ? below(nibbles + 1) : 0, nines = below(100) < 12;
  for (int index = 0; index < nibbles; index++) value = value << 4 | (index < zeros ? 0 : nines ? 9 : below(10));
  if (spoil) value |= (u128)(11 + below(5)) << (4 * (1 + below(nibbles - 1)));
  if (sign) value = (value & ~(u128)15) | (u64[]){0xc, 0xd, 0xf, 0xa, 0xb, 0xe, 0xc, 0xd}[below(8)];
  return value;
}

static void put(u64 *where, u128 value) { where[0] = value >> 64, where[1] = value; }

static const u64 counts[] = {0, 1, 2, 5, 7, 15, 16, 17, 33, 34, 35, 63};
static const u64 shifts[] = {0, 1, 2, 5, 30, 31, 32, 33, 40, 255, 254, 251, 226, 225, 224, 223, 200, 128, 127};
static const unsigned singles[] = {0, 0x80000000, 0x3f800000, 0xbf800000, 0x7f800000, 0xff800000, 0x7fc00000, 0x7fa00001, 0x00000001,
  0x00800000, 0x7f7fffff, 0x3c003c00, 0x7c007e00, 0x7e01fc00, 0x00010400, 0x3e80bc00, 0x41200000, 0xc2c80000, 0x42fe0000, 0x43000000,
  0xc3160000, 0x3f000000, 0x4049999a, 0x3f7fffff, 0x3f800001, 0x7f000080, 0x80ff7fff, 0x00017fff, 0x7fff8000, 0x80008000};
static u64 some_singles(int kind) {
  u64 r = rnd();
  unsigned a = singles[r % (sizeof singles / 4)], b = singles[(r >> 8) % (sizeof singles / 4)];
  if (kind == 0) return r;
  if (kind == 2) a = (unsigned)(r >> 16) & 0xc3ffffff, b = (r >> 60 & 1) ? (unsigned)(r >> 40) & 0xc7ffffff : b;
  return (u64)a << 32 | b;
}

// The registers of a case of a class.
static void prepare(u64 *block, int class, int index, const char *name) {
  memset(block, 0, 64 * 8);
  block[6] = (u64)(index % 8) << 32;
  block[7] = block[14] = 0x1111111111111111ull;
  switch (class) {
  case C_QUAD:
    put(block + 2, rnd128());
    block[2] = (block[2] & 0x8000ffffffffffffull) | (u64)(index % 5 == 0 ? 0 : index % 7 == 0 ? 0x7ffe : 0x3ff0 + index) << 48;
    if (index == 9) block[2] |= 0x7fff000000000000ull;
    if (index == 11) block[2] = 0x7ffeffffffffffffull, block[3] = ~0ull;
    break;
  case C_SINGLE: case C_GER: case C_BITS:
    for (int k = 2; k < 20; k++) block[k] = k == 6 || k == 7 ? block[k] : some_singles(class == C_BITS ? 0 : index % 3);
    break;
  case C_EXPONENT:
    // Powers that a single has, by their bits: of integers, of halves, and of what is by them.
    for (int k = 2; k < 4; k++)
      block[k] = (u64)(unsigned[]){0x41200000, 0xc1200000, 0x3f000000, 0xbe800000, 0x42fe0000, 0xc2fc0000, 0x40490fdb, 0x7fc00000, 0x7f800000,
        0xff800000, 0, 0x80000000, 0x42ffffff, 0x43000000, 0xc3150000, 0xc3160000, 0x3f800001, 0x00000001}[below(18)] << 32
        | (unsigned)(rnd() & 0xc2ffffff);
    break;
  case C_AMO:
    block[20] = rnd(), block[21] = index % 4 == 0 ? 1 : rnd(), block[22] = rnd();
    for (int k = 40; k < 44; k++) block[k] = index % 3 == 0 ? block[21] : index % 3 == 1 ? rnd() : 0x7fffffff80000000ull + index;
    if (index % 5 == 0) block[42] = block[41], block[40] = block[41];
    if (index % 5 == 1) block[41] = block[21];
    break;
  case C_DD: case C_DDI:
    block[16] = some_decimal(64), block[18] = some_decimal(64);
    if (class == C_DDI && index % 3) block[18] = decimal(64, below(2), rnd() % 10000000000000000ull, (int[]){0, 0, 1, 2, 3, -1, -2, -5, 4}[below(9)], 0);
    if (index % 4 == 1 && (name[1] == 'a' || name[1] == 's' || name[1] == 'c')) block[18] = block[16] ^ below(2) << 63;
    break;
  case C_QQ: case C_QQI:
    put(block + 2, some_decimal(128)), put(block + 4, some_decimal(128));
    if (class == C_QQI && index % 3)
      put(block + 4, decimal(128, below(2), rnd128() % power((int[]){5, 19, 20, 34}[below(4)]), (int[]){0, 0, 1, 2, 5, -1, -2, -5, 10}[below(9)], 0));
    if (index % 4 == 1 && (name[1] == 'a' || name[1] == 's' || name[1] == 'c')) block[4] = block[2] ^ below(2) << 63, block[5] = block[3];
    break;
  case C_ID: block[16] = below(13) == 12 ? rnd() : counts[below(12)], block[18] = some_decimal(64); break;
  case C_IQ: block[16] = below(13) == 12 ? rnd() : counts[below(12)], put(block + 4, some_decimal(128)); break;
  case C_ED:
    block[16] = (u64[]){0, 1, 398, 767, 768, -1ull, -2ull, -3ull, -4ull, below(768), below(768)}[below(11)], block[18] = some_decimal(64);
    break;
  case C_EQ:
    block[16] = (u64[]){0, 1, 6176, 12287, 12288, -1ull, -2ull, -3ull, -4ull, below(12288), below(12288)}[below(11)];
    put(block + 4, some_decimal(128));
    break;
  case C_D32: block[18] = (u64)some_decimal(32) | (index % 5 == 0 ? rnd() << 32 : 0); break;
  case C_INT:
    block[18] = (u64[]){0, 1, 1ull << 63, -1ull, (1ull << 63) - 1, 10000000000000000ull, 9999999999999999ull, 9999999999999995ull,
      99999999999999995ull, rnd(), rnd() >> 24}[below(11)];
    break;
  case C_VINT:
    put(block + 4, (u128[]){0, 1, (u128)1 << 127, ~(u128)0, ((u128)1 << 127) - 1, power(34), power(34) - 1, power(34) + 5, rnd128(), rnd128() >> 8,
      rnd128() >> 28}[below(11)]);
    break;
  case C_BCD0: case C_BCD1: block[18] = some_digits(16, class == C_BCD1, index % 6 == 5); break;
  case C_BCDQ0: case C_BCDQ1: put(block + 4, some_digits(32, class == C_BCDQ1, index % 6 == 5)); break;
  case C_VSS: put(block + 2, some_digits(32, 1, 0)), put(block + 4, some_digits(32, 1, 0)); break;
  case C_VS16: put(block + 4, some_digits(32, 1, 0) & (index % 4 ? ((u128)1 << 68) - 1 : ~(u128)0)); break;
  case C_VS7: put(block + 4, some_digits(32, 1, 0) & (index % 4 ? ((u128)1 << 32) - 1 : ~(u128)0)); break;
  case C_VCS: put(block + 2, (u128)shifts[below(19)] << 64 | (rnd128() & ~((u128)0xffff << 64))), put(block + 4, some_digits(32, 1, 0)); break;
  case C_VCU: put(block + 2, (u128)shifts[below(19)] << 64), put(block + 4, some_digits(32, 0, 0)); break;
  case C_VNAT: {
    u128 value = 0;
    for (int k = 0; k < 7; k++) value = value << 16 | (0x30 + below(10));
    put(block + 4, value << 16 | (below(2) ? 0x2b : 0x2d));
    break;
  }
  case C_VZ0: case C_VZ1: {
    u128 value = 0;
    unsigned zone = class == C_VZ1 ? 0xf : 0x3;
    for (int k = 0; k < 16; k++) value = value << 8 | zone << 4 | below(10);
    put(block + 4, (value & ~(u128)0xf0) | (u64[]){0xa, 0xb, 0xc, 0xd, 0xe, 0xf, zone, zone, class == C_VZ1 ? 0xc : 0x7}[below(9)] << 4);
    break;
  }
  case C_VQ:
    put(block + 4, (u128[]){0, 1, ~(u128)0, power(31) - 1, 1 - power(31), rnd128() >> 40, -(rnd128() >> 40), rnd128() >> 30, 12345}[below(9)]);
    break;
  default:
    block[20] = 0x0123456789abcdefull, block[21] = 0xfedcba9876543210ull;
    break;
  }
}

static sigjmp_buf back;
static u64 *cells;
static unsigned *code;
static const char *running;

static void handler(int signal, siginfo_t *info, void *context) {
  u64 address = (u64)info->si_addr;
  printf("%s: signal %d code %d at %s\n", running, signal, info->si_code,
         address >= (u64)code && address < (u64)code + 65536 ? "the instruction" : address == (u64)cells ? "the address" : "nothing of it");
  siglongjmp(back, 1);
}

int main(void) {
  static u64 block[64] __attribute__((aligned(16)));
  for (int bits = 1023; bits >= 0; bits--) declet_of[digits_of(bits)] = bits;
  code = mmap(0, 65536, PROT_READ | PROT_WRITE | PROT_EXEC, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  cells = block + 41;
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = handler;
  action.sa_flags = SA_SIGINFO | SA_NODEFER;
  sigaction(SIGILL, &action, 0), sigaction(SIGBUS, &action, 0), sigaction(SIGSEGV, &action, 0), sigaction(SIGTRAP, &action, 0);
  setvbuf(stdout, 0, _IONBF, 0);
  for (unsigned row = 0; row < sizeof table / sizeof table[0]; row++) {
    // Each has code of its own, 64 bytes on, so that none is run where another was.
    unsigned *at = code + 16 * (row % 1000);
    for (int k = 0; k < table[row].count; k++) at[k] = table[row].words[k];
    at[table[row].count] = 0x4e800020;
    flush_code(at);
    running = table[row].name;
    u64 values = 0xcbf29ce484222325ull, status = values, up = 0;
    for (int index = 0; index < table[row].cases; index++) {
      prepare(block, table[row].class, index, table[row].name);
      if (sigsetjmp(back, 1)) break;
      run_code(block, at);
      if (table[row].class == C_SIGNAL) { printf("%s: no signal\n", running); continue; }
      if (table[row].class == C_SHOW) { printf("%s: %llx %llx\n", running, block[48], block[49]); continue; }
      for (int k = 24; k < 50; k++) {
        if (k == 28) continue;
        if (k >= 44 && k < 48) continue;
        values = (values ^ block[k]) * 0x100000001b3ull, values ^= values >> 29;
      }
      status = (status ^ (block[28] & ~0x40000ull)) * 0x100000001b3ull, status ^= status >> 29;
      up += block[28] >> 18 & 1;
    }
    if (table[row].class != C_SIGNAL && table[row].class != C_SHOW)
      printf("%s: %016llx %016llx rounded up %llu\n", running, values, status, up);
  }
  return 0;
}
'''

rows=[]   # (name, [asm lines] or words, class, count)
def X(name, asm, cls, count=12): rows.append((name, asm if isinstance(asm,list) else [asm], cls, count))
# quad, bfloat16, permute controls, estimates
for n,a in [("xsrqpxp even","xsrqpxp 1,4,2,0"),("xsrqpxp zero","xsrqpxp 1,4,2,1"),("xsrqpxp up","xsrqpxp 1,4,2,2"),("xsrqpxp down","xsrqpxp 1,4,2,3"),("xsrqpxp away","xsrqpxp 0,4,2,0"),("xsrqpxp current","xsrqpxp 0,4,2,3")]: X(n,a,'quad')
X("xvcvbf16spn","xvcvbf16spn 36,34",'single'); X("xvcvspbf16","xvcvspbf16 36,34",'single')
X("vlogefp","vlogefp 4,2",'single')
X("vexptefp","vexptefp 4,2",'exponent')
for sz in "bhwd":
    for i in range(4): X(f"xxgenpcv{sz}m {i}",f"xxgenpcv{sz}m 36,2,{i}",'bits',8)
G="xvi4ger8 xvi4ger8pp xvi8ger4 xvi8ger4pp xvi8ger4spp xvi16ger2 xvi16ger2s xvi16ger2pp xvi16ger2spp xvf16ger2 xvf16ger2pp xvf16ger2pn xvf16ger2np xvf16ger2nn xvbf16ger2 xvbf16ger2pp xvbf16ger2pn xvbf16ger2np xvbf16ger2nn xvf32ger xvf32gerpp xvf32gerpn xvf32gernp xvf32gernn".split()
for g in G: X(g,["xxmtacc 0",f"{g} 0,34,35","xxmfacc 0"],'ger')
for g in "xvf64ger xvf64gerpp xvf64gerpn xvf64gernp xvf64gernn".split(): X(g,["xxmtacc 0",f"{g} 0,36,34","xxmfacc 0"],'ger')
for g,m in [("xvi4ger8","5,3,0xa5"),("xvi4ger8pp","15,9,0x3c"),("xvi8ger4","5,3,9"),("xvi8ger4pp","10,15,6"),("xvi8ger4spp","7,14,15"),("xvi16ger2","5,3,2"),("xvi16ger2s","15,15,1"),("xvi16ger2pp","9,6,3"),("xvi16ger2spp","3,12,2"),("xvf16ger2","5,3,2"),("xvf16ger2pp","15,7,1"),("xvf16ger2pn","9,14,3"),("xvf16ger2np","6,13,2"),("xvf16ger2nn","15,15,1"),("xvbf16ger2","13,3,3"),("xvbf16ger2pp","7,11,1"),("xvbf16ger2pn","14,5,2"),("xvbf16ger2np","3,15,3"),("xvbf16ger2nn","6,11,2"),("xvf32ger","5,3"),("xvf32gerpp","15,6"),("xvf32gerpn","11,13"),("xvf32gernp","7,14"),("xvf32gernn","9,3")]:
    X("pm"+g,["xxmtacc 0",f"pm{g} 0,34,35,{m}","xxmfacc 0"],'ger',8)
for g,m in [("xvf64ger","5,2"),("xvf64gerpp","15,1"),("xvf64gerpn","10,3"),("xvf64gernp","11,1"),("xvf64gernn","6,2")]: X("pm"+g,["xxmtacc 0",f"pm{g} 0,36,34,{m}","xxmfacc 0"],'ger',8)
X("xxsetaccz",["xxmtacc 0","xxsetaccz 0","xxmfacc 0"],'ger',2)
# atomic memory operations: RT is r5, so that what it takes is of r6 and r7
for fc in [0,1,2,3,4,5,6,7,8,16,24,28]:
    X(f"lwat {fc}",f".long {0x7c00048c|5<<21|4<<16|fc<<11:#x}",'amo',10); X(f"ldat {fc}",f".long {0x7c0004cc|5<<21|4<<16|fc<<11:#x}",'amo',10)
for fc in [0,1,2,3,4,5,6,7,24]:
    X(f"stwat {fc}",f".long {0x7c00058c|6<<21|4<<16|fc<<11:#x}",'amo',10); X(f"stdat {fc}",f".long {0x7c0005cc|6<<21|4<<16|fc<<11:#x}",'amo',10)
# the decimal floating point
for o in ['dadd','dsub','dmul','ddiv']:
    X(o,f"{o} 1,2,3",'dd',24); X(o+'q',f"{o}q 8,4,6",'qq',24); X(o+'.',f"{o}. 1,2,3",'dd',4); X(o+'q.',f"{o}q. 8,4,6",'qq',4)
def word(asm, orbits):
    out=subprocess.run(['llvm-mc','-triple=powerpc64','-mcpu=pwr10','-show-encoding'],input=asm,capture_output=True,text=True).stdout
    b=re.search(r'encoding: \[(.*)\]',out).group(1).replace('0x','').replace(',','')
    return '.long 0x%08x'%(int(b,16)|orbits)
for r in range(4):
    X(f'dqua {r}',f"dqua 1,2,3,{r}",'dd'); X(f'dquaq {r}',f"dquaq 8,4,6,{r}",'qq')
    X(f'drrnd {r}',f"drrnd 1,2,3,{r}",'id'); X(f'drrndq {r}',f"drrndq 8,2,6,{r}",'iq')
    for R in range(2):
        X(f'drintx {R} {r}',f"drintx {R},1,3,{r}",'dd',8); X(f'drintn {R} {r}',f"drintn {R},1,3,{r}",'dd',8)
        X(f'drintxq {R} {r}',f"drintxq {R},8,6,{r}",'qq',8); X(f'drintnq {R} {r}',f"drintnq {R},8,6,{r}",'qq',8)
for te,r in [(0,0),(3,1),(-5,2),(15,3),(-16,3),(2,0)]:
    X(f'dquai {te} {r}',word(f"dquai 0,1,3,{r}",(te&31)<<16),'dd'); X(f'dquaiq {te} {r}',word(f"dquaiq 0,8,6,{r}",(te&31)<<16),'qq')
for o in ['dcmpo','dcmpu','dtstex']:
    X(o,f"{o} 3,2,3",'dd',16); X(o+'q',f"{o}q 3,4,6",'qq',16)
X('dtstsf',"dtstsf 3,2,3",'id'); X('dtstsfq',"dtstsfq 3,2,6",'iq')
for u in [0,1,7,16,34,63]:
    X(f'dtstsfi {u}',f"dtstsfi 3,{u},3",'dd',6); X(f'dtstsfiq {u}',f"dtstsfiq 3,{u},6",'qq',6)
for m in [0x3f,0x20,0x10,0x08,0x04,0x02,0x01,0x15]:
    X(f'dtstdc {m}',f"dtstdc 3,3,{m}",'dd',8); X(f'dtstdcq {m}',f"dtstdcq 3,6,{m}",'qq',8)
    X(f'dtstdg {m}',f"dtstdg 3,3,{m}",'dd',8); X(f'dtstdgq {m}',f"dtstdgq 3,6,{m}",'qq',8)
X('diex',"diex 1,2,3",'ed'); X('diexq',"diexq 8,2,6",'eq'); X('dxex',"dxex 1,3",'dd'); X('dxexq',"dxexq 1,6",'qq')
X('dctdp',"dctdp 1,3",'d32'); X('drsp',"drsp 1,3",'dd',24); X('dctqpq',"dctqpq 8,3",'dd'); X('drdpq',"drdpq 8,6",'qq',24)
X('dcffix',"dcffix 1,3",'int',16); X('dcffixq',"dcffixq 8,3",'int'); X('dctfix',"dctfix 1,3",'ddi',24); X('dctfixq',"dctfixq 1,6",'qqi',24)
X('dcffixqq',"dcffixqq 8,3",'vint',16); X('dctfixqq',"dctfixqq 4,6",'qqi',24)
for sh in [0,1,5,15,16,17,33,34,35,63]:
    X(f'dscli {sh}',f"dscli 1,3,{sh}",'dd',6); X(f'dscri {sh}',f"dscri 1,3,{sh}",'dd',6); X(f'dscliq {sh}',f"dscliq 8,6,{sh}",'qq',6); X(f'dscriq {sh}',f"dscriq 8,6,{sh}",'qq',6)
for sp in range(4):
    X(f'ddedpd {sp}',f"ddedpd {sp},1,3",'dd'); X(f'ddedpdq {sp}',f"ddedpdq {sp},8,6",'qq')
for s in range(2):
    X(f'denbcd {s}',f"denbcd {s},1,3",f'bcd{s}'); X(f'denbcdq {s}',f"denbcdq {s},8,6",f'bcdq{s}')
# the signed decimals of the vector registers
for ps in range(2):
    for o in ['bcdadd','bcdsub']: X(f'{o}. {ps}',f"{o}. 4,2,3,{ps}",'vss',16)
    for o in ['bcds','bcdsr','bcdtrunc']: X(f'{o}. {ps}',f"{o}. 4,2,3,{ps}",'vcs',16)
    X(f'bcdcfn. {ps}',f"bcdcfn. 4,3,{ps}",'vnat'); X(f'bcdcfsq. {ps}',f"bcdcfsq. 4,3,{ps}",'vq'); X(f'bcdcfz. {ps}',f"bcdcfz. 4,3,{ps}",f'vz{ps}')
    X(f'bcdctz. {ps}',f"bcdctz. 4,3,{ps}",'vs16'); X(f'bcdsetsgn. {ps}',f"bcdsetsgn. 4,3,{ps}",'vss')
X('bcdus.',"bcdus. 4,2,3",'vcu',16); X('bcdutrunc.',"bcdutrunc. 4,2,3",'vcu',16); X('bcdcpsgn.',"bcdcpsgn. 4,2,3",'vss'); X('bcdctn.',"bcdctn. 4,3",'vs7'); X('bcdctsq.',"bcdctsq. 4,3",'vss')
# what a program reads and writes of its special purpose registers: r5 and r6 are what is shown
X("amr",["mfspr 7,13","mtspr 13,5","mfspr 6,13","li 5,0","mtspr 13,7"],'show',1)
X("ctrl","mfspr 5,136",'show',1)
X("ppr",["mfspr 5,896","li 6,1","sldi 6,6,52","mtspr 896,6","mfspr 6,896","mtspr 896,5"],'show',1)
X("ppr of no priority",["mfspr 7,896","li 6,7","sldi 6,6,50","mtspr 896,6","mfspr 6,896","li 5,0","mtspr 896,7"],'show',1)
X("copy and cp_abort",["copy 0,4",".long 0x7c00068c","li 5,1"],'show',1)
X("hashst and hashchk",["mr 6,5","hashst 6,-8(4)","hashchk 6,-8(4)","li 5,1","li 6,2"],'show',1)
# what is a signal
X("hashchk of another",["hashst 6,-8(4)","addi 6,6,1","hashchk 6,-8(4)"],'signal',1)
X("paste.","paste. 0,4",'signal',1)
X("scv","scv 0",'signal',1)
X("tbegin.","tbegin. 0",'signal',1)
X("tend.","tend. 0",'signal',1)
X("tabort.","tabort. 5",'signal',1)
X("rfebb","rfebb 1",'signal',1)
X("clrbhrb","clrbhrb",'signal',1)
X("mfbhrbe","mfbhrbe 5,1",'signal',1)
X("mtspr of ctrl","mtspr 136,5",'signal',1)
X("mtspr of uamor","mtspr 157,5",'signal',1)
X("hashstp","hashstp 6,-8(4)",'signal',1)
X("lwat of a function that isn't",f".long {0x7c00048c|5<<21|4<<16|9<<11:#x}",'signal',1)
X("lxvkq of a reserved value",".long 0xf05f52d1",'signal',1)
# what LLVM has of an architecture after the ISA 3.1, by its words
for n,w in [("xxaes192encp","f0453610"),("lxvrl","7c442c1b"),("stxvrl","7c442d1b"),("vucmprhb","10821883"),("xxgfmul128xts","f04327d7"),
            ("xxssumudm","ec4324cf"),("vupkhsntob","10801183"),("lxvpb32x","7c442eda"),("xsaddadduqm","ec432307")]:
    X(n,f".long 0x{w}",'signal',1)
# assemble
lines=[l for r in rows for l in r[1] if not l.startswith('.long')]
out=subprocess.run(['llvm-mc','-triple=powerpc64','-mcpu=pwr10','-show-encoding'],input='\n'.join(lines)+'\n',capture_output=True,text=True)
if out.returncode or 'error' in out.stderr: print(out.stderr[:2000]); sys.exit(1)
encs=re.findall(r'encoding: \[(.*?)\]',out.stdout)
assert len(encs)==len(lines),(len(encs),len(lines))
it=iter(encs)
table=[]
classes=sorted(set(r[2] for r in rows))
for name,asm,cls,count in rows:
    words=[]
    for l in asm:
        if l.startswith('.long'): words.append('%08x'%int(l.split()[1],16)); continue
        b=next(it).replace('0x','').replace(',','')
        words+=[b[i:i+8] for i in range(0,len(b),8)]
    assert len(words)<=7
    table.append('  {"%s", %d, {%s}, C_%s, %d},'%(name,len(words),', '.join('0x'+w for w in words),cls.upper(),count))
body=TEMPLATE
body=body.replace('/*CLASSES*/',', '.join('C_'+c.upper() for c in classes)).replace('/*TABLE*/','\n'.join(table))
open(sys.argv[1],'w').write(body)
print(len(rows),'rows')
