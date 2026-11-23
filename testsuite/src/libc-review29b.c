// What a POWER10 does of the instructions that the machine had left to intrinsics that nothing served, which ended a run:
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

enum { C_AMO, C_BCD0, C_BCD1, C_BCDQ0, C_BCDQ1, C_BITS, C_D32, C_DD, C_DDI, C_ED, C_EQ, C_EXPONENT, C_GER, C_ID, C_INT, C_IQ, C_QQ, C_QQI, C_QUAD, C_SHOW, C_SIGNAL, C_SINGLE, C_VCS, C_VCU, C_VINT, C_VNAT, C_VQ, C_VS16, C_VS7, C_VSS, C_VZ0, C_VZ1 };

static const struct { const char *name; int count; unsigned words[7]; int class, cases; } table[] = {
  {"xsrqpxp even", 1, {0xfc81104a}, C_QUAD, 12},
  {"xsrqpxp zero", 1, {0xfc81124a}, C_QUAD, 12},
  {"xsrqpxp up", 1, {0xfc81144a}, C_QUAD, 12},
  {"xsrqpxp down", 1, {0xfc81164a}, C_QUAD, 12},
  {"xsrqpxp away", 1, {0xfc80104a}, C_QUAD, 12},
  {"xsrqpxp current", 1, {0xfc80164a}, C_QUAD, 12},
  {"xvcvbf16spn", 1, {0xf090176f}, C_SINGLE, 12},
  {"xvcvspbf16", 1, {0xf091176f}, C_SINGLE, 12},
  {"vlogefp", 1, {0x108011ca}, C_SINGLE, 12},
  {"vexptefp", 1, {0x1080118a}, C_EXPONENT, 12},
  {"xxgenpcvbm 0", 1, {0xf0801729}, C_BITS, 8},
  {"xxgenpcvbm 1", 1, {0xf0811729}, C_BITS, 8},
  {"xxgenpcvbm 2", 1, {0xf0821729}, C_BITS, 8},
  {"xxgenpcvbm 3", 1, {0xf0831729}, C_BITS, 8},
  {"xxgenpcvhm 0", 1, {0xf080172b}, C_BITS, 8},
  {"xxgenpcvhm 1", 1, {0xf081172b}, C_BITS, 8},
  {"xxgenpcvhm 2", 1, {0xf082172b}, C_BITS, 8},
  {"xxgenpcvhm 3", 1, {0xf083172b}, C_BITS, 8},
  {"xxgenpcvwm 0", 1, {0xf0801769}, C_BITS, 8},
  {"xxgenpcvwm 1", 1, {0xf0811769}, C_BITS, 8},
  {"xxgenpcvwm 2", 1, {0xf0821769}, C_BITS, 8},
  {"xxgenpcvwm 3", 1, {0xf0831769}, C_BITS, 8},
  {"xxgenpcvdm 0", 1, {0xf080176b}, C_BITS, 8},
  {"xxgenpcvdm 1", 1, {0xf081176b}, C_BITS, 8},
  {"xxgenpcvdm 2", 1, {0xf082176b}, C_BITS, 8},
  {"xxgenpcvdm 3", 1, {0xf083176b}, C_BITS, 8},
  {"xvi4ger8", 3, {0x7c010162, 0xec02191e, 0x7c000162}, C_GER, 12},
  {"xvi4ger8pp", 3, {0x7c010162, 0xec021916, 0x7c000162}, C_GER, 12},
  {"xvi8ger4", 3, {0x7c010162, 0xec02181e, 0x7c000162}, C_GER, 12},
  {"xvi8ger4pp", 3, {0x7c010162, 0xec021816, 0x7c000162}, C_GER, 12},
  {"xvi8ger4spp", 3, {0x7c010162, 0xec021b1e, 0x7c000162}, C_GER, 12},
  {"xvi16ger2", 3, {0x7c010162, 0xec021a5e, 0x7c000162}, C_GER, 12},
  {"xvi16ger2s", 3, {0x7c010162, 0xec02195e, 0x7c000162}, C_GER, 12},
  {"xvi16ger2pp", 3, {0x7c010162, 0xec021b5e, 0x7c000162}, C_GER, 12},
  {"xvi16ger2spp", 3, {0x7c010162, 0xec021956, 0x7c000162}, C_GER, 12},
  {"xvf16ger2", 3, {0x7c010162, 0xec02189e, 0x7c000162}, C_GER, 12},
  {"xvf16ger2pp", 3, {0x7c010162, 0xec021896, 0x7c000162}, C_GER, 12},
  {"xvf16ger2pn", 3, {0x7c010162, 0xec021c96, 0x7c000162}, C_GER, 12},
  {"xvf16ger2np", 3, {0x7c010162, 0xec021a96, 0x7c000162}, C_GER, 12},
  {"xvf16ger2nn", 3, {0x7c010162, 0xec021e96, 0x7c000162}, C_GER, 12},
  {"xvbf16ger2", 3, {0x7c010162, 0xec02199e, 0x7c000162}, C_GER, 12},
  {"xvbf16ger2pp", 3, {0x7c010162, 0xec021996, 0x7c000162}, C_GER, 12},
  {"xvbf16ger2pn", 3, {0x7c010162, 0xec021d96, 0x7c000162}, C_GER, 12},
  {"xvbf16ger2np", 3, {0x7c010162, 0xec021b96, 0x7c000162}, C_GER, 12},
  {"xvbf16ger2nn", 3, {0x7c010162, 0xec021f96, 0x7c000162}, C_GER, 12},
  {"xvf32ger", 3, {0x7c010162, 0xec0218de, 0x7c000162}, C_GER, 12},
  {"xvf32gerpp", 3, {0x7c010162, 0xec0218d6, 0x7c000162}, C_GER, 12},
  {"xvf32gerpn", 3, {0x7c010162, 0xec021cd6, 0x7c000162}, C_GER, 12},
  {"xvf32gernp", 3, {0x7c010162, 0xec021ad6, 0x7c000162}, C_GER, 12},
  {"xvf32gernn", 3, {0x7c010162, 0xec021ed6, 0x7c000162}, C_GER, 12},
  {"xvf64ger", 3, {0x7c010162, 0xec0411de, 0x7c000162}, C_GER, 12},
  {"xvf64gerpp", 3, {0x7c010162, 0xec0411d6, 0x7c000162}, C_GER, 12},
  {"xvf64gerpn", 3, {0x7c010162, 0xec0415d6, 0x7c000162}, C_GER, 12},
  {"xvf64gernp", 3, {0x7c010162, 0xec0413d6, 0x7c000162}, C_GER, 12},
  {"xvf64gernn", 3, {0x7c010162, 0xec0417d6, 0x7c000162}, C_GER, 12},
  {"pmxvi4ger8", 4, {0x7c010162, 0x0790a553, 0xec02191e, 0x7c000162}, C_GER, 8},
  {"pmxvi4ger8pp", 4, {0x7c010162, 0x07903cf9, 0xec021916, 0x7c000162}, C_GER, 8},
  {"pmxvi8ger4", 4, {0x7c010162, 0x07909053, 0xec02181e, 0x7c000162}, C_GER, 8},
  {"pmxvi8ger4pp", 4, {0x7c010162, 0x079060af, 0xec021816, 0x7c000162}, C_GER, 8},
  {"pmxvi8ger4spp", 4, {0x7c010162, 0x0790f07e, 0xec021b1e, 0x7c000162}, C_GER, 8},
  {"pmxvi16ger2", 4, {0x7c010162, 0x07908053, 0xec021a5e, 0x7c000162}, C_GER, 8},
  {"pmxvi16ger2s", 4, {0x7c010162, 0x079040ff, 0xec02195e, 0x7c000162}, C_GER, 8},
  {"pmxvi16ger2pp", 4, {0x7c010162, 0x0790c096, 0xec021b5e, 0x7c000162}, C_GER, 8},
  {"pmxvi16ger2spp", 4, {0x7c010162, 0x0790803c, 0xec021956, 0x7c000162}, C_GER, 8},
  {"pmxvf16ger2", 4, {0x7c010162, 0x07908053, 0xec02189e, 0x7c000162}, C_GER, 8},
  {"pmxvf16ger2pp", 4, {0x7c010162, 0x079040f7, 0xec021896, 0x7c000162}, C_GER, 8},
  {"pmxvf16ger2pn", 4, {0x7c010162, 0x0790c09e, 0xec021c96, 0x7c000162}, C_GER, 8},
  {"pmxvf16ger2np", 4, {0x7c010162, 0x0790806d, 0xec021a96, 0x7c000162}, C_GER, 8},
  {"pmxvf16ger2nn", 4, {0x7c010162, 0x079040ff, 0xec021e96, 0x7c000162}, C_GER, 8},
  {"pmxvbf16ger2", 4, {0x7c010162, 0x0790c0d3, 0xec02199e, 0x7c000162}, C_GER, 8},
  {"pmxvbf16ger2pp", 4, {0x7c010162, 0x0790407b, 0xec021996, 0x7c000162}, C_GER, 8},
  {"pmxvbf16ger2pn", 4, {0x7c010162, 0x079080e5, 0xec021d96, 0x7c000162}, C_GER, 8},
  {"pmxvbf16ger2np", 4, {0x7c010162, 0x0790c03f, 0xec021b96, 0x7c000162}, C_GER, 8},
  {"pmxvbf16ger2nn", 4, {0x7c010162, 0x0790806b, 0xec021f96, 0x7c000162}, C_GER, 8},
  {"pmxvf32ger", 4, {0x7c010162, 0x07900053, 0xec0218de, 0x7c000162}, C_GER, 8},
  {"pmxvf32gerpp", 4, {0x7c010162, 0x079000f6, 0xec0218d6, 0x7c000162}, C_GER, 8},
  {"pmxvf32gerpn", 4, {0x7c010162, 0x079000bd, 0xec021cd6, 0x7c000162}, C_GER, 8},
  {"pmxvf32gernp", 4, {0x7c010162, 0x0790007e, 0xec021ad6, 0x7c000162}, C_GER, 8},
  {"pmxvf32gernn", 4, {0x7c010162, 0x07900093, 0xec021ed6, 0x7c000162}, C_GER, 8},
  {"pmxvf64ger", 4, {0x7c010162, 0x07900058, 0xec0411de, 0x7c000162}, C_GER, 8},
  {"pmxvf64gerpp", 4, {0x7c010162, 0x079000f4, 0xec0411d6, 0x7c000162}, C_GER, 8},
  {"pmxvf64gerpn", 4, {0x7c010162, 0x079000ac, 0xec0415d6, 0x7c000162}, C_GER, 8},
  {"pmxvf64gernp", 4, {0x7c010162, 0x079000b4, 0xec0413d6, 0x7c000162}, C_GER, 8},
  {"pmxvf64gernn", 4, {0x7c010162, 0x07900068, 0xec0417d6, 0x7c000162}, C_GER, 8},
  {"xxsetaccz", 3, {0x7c010162, 0x7c030162, 0x7c000162}, C_GER, 2},
  {"lwat 0", 1, {0x7ca4048c}, C_AMO, 10},
  {"ldat 0", 1, {0x7ca404cc}, C_AMO, 10},
  {"lwat 1", 1, {0x7ca40c8c}, C_AMO, 10},
  {"ldat 1", 1, {0x7ca40ccc}, C_AMO, 10},
  {"lwat 2", 1, {0x7ca4148c}, C_AMO, 10},
  {"ldat 2", 1, {0x7ca414cc}, C_AMO, 10},
  {"lwat 3", 1, {0x7ca41c8c}, C_AMO, 10},
  {"ldat 3", 1, {0x7ca41ccc}, C_AMO, 10},
  {"lwat 4", 1, {0x7ca4248c}, C_AMO, 10},
  {"ldat 4", 1, {0x7ca424cc}, C_AMO, 10},
  {"lwat 5", 1, {0x7ca42c8c}, C_AMO, 10},
  {"ldat 5", 1, {0x7ca42ccc}, C_AMO, 10},
  {"lwat 6", 1, {0x7ca4348c}, C_AMO, 10},
  {"ldat 6", 1, {0x7ca434cc}, C_AMO, 10},
  {"lwat 7", 1, {0x7ca43c8c}, C_AMO, 10},
  {"ldat 7", 1, {0x7ca43ccc}, C_AMO, 10},
  {"lwat 8", 1, {0x7ca4448c}, C_AMO, 10},
  {"ldat 8", 1, {0x7ca444cc}, C_AMO, 10},
  {"lwat 16", 1, {0x7ca4848c}, C_AMO, 10},
  {"ldat 16", 1, {0x7ca484cc}, C_AMO, 10},
  {"lwat 24", 1, {0x7ca4c48c}, C_AMO, 10},
  {"ldat 24", 1, {0x7ca4c4cc}, C_AMO, 10},
  {"lwat 28", 1, {0x7ca4e48c}, C_AMO, 10},
  {"ldat 28", 1, {0x7ca4e4cc}, C_AMO, 10},
  {"stwat 0", 1, {0x7cc4058c}, C_AMO, 10},
  {"stdat 0", 1, {0x7cc405cc}, C_AMO, 10},
  {"stwat 1", 1, {0x7cc40d8c}, C_AMO, 10},
  {"stdat 1", 1, {0x7cc40dcc}, C_AMO, 10},
  {"stwat 2", 1, {0x7cc4158c}, C_AMO, 10},
  {"stdat 2", 1, {0x7cc415cc}, C_AMO, 10},
  {"stwat 3", 1, {0x7cc41d8c}, C_AMO, 10},
  {"stdat 3", 1, {0x7cc41dcc}, C_AMO, 10},
  {"stwat 4", 1, {0x7cc4258c}, C_AMO, 10},
  {"stdat 4", 1, {0x7cc425cc}, C_AMO, 10},
  {"stwat 5", 1, {0x7cc42d8c}, C_AMO, 10},
  {"stdat 5", 1, {0x7cc42dcc}, C_AMO, 10},
  {"stwat 6", 1, {0x7cc4358c}, C_AMO, 10},
  {"stdat 6", 1, {0x7cc435cc}, C_AMO, 10},
  {"stwat 7", 1, {0x7cc43d8c}, C_AMO, 10},
  {"stdat 7", 1, {0x7cc43dcc}, C_AMO, 10},
  {"stwat 24", 1, {0x7cc4c58c}, C_AMO, 10},
  {"stdat 24", 1, {0x7cc4c5cc}, C_AMO, 10},
  {"dadd", 1, {0xec221804}, C_DD, 24},
  {"daddq", 1, {0xfd043004}, C_QQ, 24},
  {"dadd.", 1, {0xec221805}, C_DD, 4},
  {"daddq.", 1, {0xfd043005}, C_QQ, 4},
  {"dsub", 1, {0xec221c04}, C_DD, 24},
  {"dsubq", 1, {0xfd043404}, C_QQ, 24},
  {"dsub.", 1, {0xec221c05}, C_DD, 4},
  {"dsubq.", 1, {0xfd043405}, C_QQ, 4},
  {"dmul", 1, {0xec221844}, C_DD, 24},
  {"dmulq", 1, {0xfd043044}, C_QQ, 24},
  {"dmul.", 1, {0xec221845}, C_DD, 4},
  {"dmulq.", 1, {0xfd043045}, C_QQ, 4},
  {"ddiv", 1, {0xec221c44}, C_DD, 24},
  {"ddivq", 1, {0xfd043444}, C_QQ, 24},
  {"ddiv.", 1, {0xec221c45}, C_DD, 4},
  {"ddivq.", 1, {0xfd043445}, C_QQ, 4},
  {"dqua 0", 1, {0xec221806}, C_DD, 12},
  {"dquaq 0", 1, {0xfd043006}, C_QQ, 12},
  {"drrnd 0", 1, {0xec221846}, C_ID, 12},
  {"drrndq 0", 1, {0xfd023046}, C_IQ, 12},
  {"drintx 0 0", 1, {0xec2018c6}, C_DD, 8},
  {"drintn 0 0", 1, {0xec2019c6}, C_DD, 8},
  {"drintxq 0 0", 1, {0xfd0030c6}, C_QQ, 8},
  {"drintnq 0 0", 1, {0xfd0031c6}, C_QQ, 8},
  {"drintx 1 0", 1, {0xec2118c6}, C_DD, 8},
  {"drintn 1 0", 1, {0xec2119c6}, C_DD, 8},
  {"drintxq 1 0", 1, {0xfd0130c6}, C_QQ, 8},
  {"drintnq 1 0", 1, {0xfd0131c6}, C_QQ, 8},
  {"dqua 1", 1, {0xec221a06}, C_DD, 12},
  {"dquaq 1", 1, {0xfd043206}, C_QQ, 12},
  {"drrnd 1", 1, {0xec221a46}, C_ID, 12},
  {"drrndq 1", 1, {0xfd023246}, C_IQ, 12},
  {"drintx 0 1", 1, {0xec201ac6}, C_DD, 8},
  {"drintn 0 1", 1, {0xec201bc6}, C_DD, 8},
  {"drintxq 0 1", 1, {0xfd0032c6}, C_QQ, 8},
  {"drintnq 0 1", 1, {0xfd0033c6}, C_QQ, 8},
  {"drintx 1 1", 1, {0xec211ac6}, C_DD, 8},
  {"drintn 1 1", 1, {0xec211bc6}, C_DD, 8},
  {"drintxq 1 1", 1, {0xfd0132c6}, C_QQ, 8},
  {"drintnq 1 1", 1, {0xfd0133c6}, C_QQ, 8},
  {"dqua 2", 1, {0xec221c06}, C_DD, 12},
  {"dquaq 2", 1, {0xfd043406}, C_QQ, 12},
  {"drrnd 2", 1, {0xec221c46}, C_ID, 12},
  {"drrndq 2", 1, {0xfd023446}, C_IQ, 12},
  {"drintx 0 2", 1, {0xec201cc6}, C_DD, 8},
  {"drintn 0 2", 1, {0xec201dc6}, C_DD, 8},
  {"drintxq 0 2", 1, {0xfd0034c6}, C_QQ, 8},
  {"drintnq 0 2", 1, {0xfd0035c6}, C_QQ, 8},
  {"drintx 1 2", 1, {0xec211cc6}, C_DD, 8},
  {"drintn 1 2", 1, {0xec211dc6}, C_DD, 8},
  {"drintxq 1 2", 1, {0xfd0134c6}, C_QQ, 8},
  {"drintnq 1 2", 1, {0xfd0135c6}, C_QQ, 8},
  {"dqua 3", 1, {0xec221e06}, C_DD, 12},
  {"dquaq 3", 1, {0xfd043606}, C_QQ, 12},
  {"drrnd 3", 1, {0xec221e46}, C_ID, 12},
  {"drrndq 3", 1, {0xfd023646}, C_IQ, 12},
  {"drintx 0 3", 1, {0xec201ec6}, C_DD, 8},
  {"drintn 0 3", 1, {0xec201fc6}, C_DD, 8},
  {"drintxq 0 3", 1, {0xfd0036c6}, C_QQ, 8},
  {"drintnq 0 3", 1, {0xfd0037c6}, C_QQ, 8},
  {"drintx 1 3", 1, {0xec211ec6}, C_DD, 8},
  {"drintn 1 3", 1, {0xec211fc6}, C_DD, 8},
  {"drintxq 1 3", 1, {0xfd0136c6}, C_QQ, 8},
  {"drintnq 1 3", 1, {0xfd0137c6}, C_QQ, 8},
  {"dquai 0 0", 1, {0xec201886}, C_DD, 12},
  {"dquaiq 0 0", 1, {0xfd003086}, C_QQ, 12},
  {"dquai 3 1", 1, {0xec231a86}, C_DD, 12},
  {"dquaiq 3 1", 1, {0xfd033286}, C_QQ, 12},
  {"dquai -5 2", 1, {0xec3b1c86}, C_DD, 12},
  {"dquaiq -5 2", 1, {0xfd1b3486}, C_QQ, 12},
  {"dquai 15 3", 1, {0xec2f1e86}, C_DD, 12},
  {"dquaiq 15 3", 1, {0xfd0f3686}, C_QQ, 12},
  {"dquai -16 3", 1, {0xec301e86}, C_DD, 12},
  {"dquaiq -16 3", 1, {0xfd103686}, C_QQ, 12},
  {"dquai 2 0", 1, {0xec221886}, C_DD, 12},
  {"dquaiq 2 0", 1, {0xfd023086}, C_QQ, 12},
  {"dcmpo", 1, {0xed821904}, C_DD, 16},
  {"dcmpoq", 1, {0xfd843104}, C_QQ, 16},
  {"dcmpu", 1, {0xed821d04}, C_DD, 16},
  {"dcmpuq", 1, {0xfd843504}, C_QQ, 16},
  {"dtstex", 1, {0xed821944}, C_DD, 16},
  {"dtstexq", 1, {0xfd843144}, C_QQ, 16},
  {"dtstsf", 1, {0xed821d44}, C_ID, 12},
  {"dtstsfq", 1, {0xfd823544}, C_IQ, 12},
  {"dtstsfi 0", 1, {0xed801d46}, C_DD, 6},
  {"dtstsfiq 0", 1, {0xfd803546}, C_QQ, 6},
  {"dtstsfi 1", 1, {0xed811d46}, C_DD, 6},
  {"dtstsfiq 1", 1, {0xfd813546}, C_QQ, 6},
  {"dtstsfi 7", 1, {0xed871d46}, C_DD, 6},
  {"dtstsfiq 7", 1, {0xfd873546}, C_QQ, 6},
  {"dtstsfi 16", 1, {0xed901d46}, C_DD, 6},
  {"dtstsfiq 16", 1, {0xfd903546}, C_QQ, 6},
  {"dtstsfi 34", 1, {0xeda21d46}, C_DD, 6},
  {"dtstsfiq 34", 1, {0xfda23546}, C_QQ, 6},
  {"dtstsfi 63", 1, {0xedbf1d46}, C_DD, 6},
  {"dtstsfiq 63", 1, {0xfdbf3546}, C_QQ, 6},
  {"dtstdc 63", 1, {0xed83fd84}, C_DD, 8},
  {"dtstdcq 63", 1, {0xfd86fd84}, C_QQ, 8},
  {"dtstdg 63", 1, {0xed83fdc4}, C_DD, 8},
  {"dtstdgq 63", 1, {0xfd86fdc4}, C_QQ, 8},
  {"dtstdc 32", 1, {0xed838184}, C_DD, 8},
  {"dtstdcq 32", 1, {0xfd868184}, C_QQ, 8},
  {"dtstdg 32", 1, {0xed8381c4}, C_DD, 8},
  {"dtstdgq 32", 1, {0xfd8681c4}, C_QQ, 8},
  {"dtstdc 16", 1, {0xed834184}, C_DD, 8},
  {"dtstdcq 16", 1, {0xfd864184}, C_QQ, 8},
  {"dtstdg 16", 1, {0xed8341c4}, C_DD, 8},
  {"dtstdgq 16", 1, {0xfd8641c4}, C_QQ, 8},
  {"dtstdc 8", 1, {0xed832184}, C_DD, 8},
  {"dtstdcq 8", 1, {0xfd862184}, C_QQ, 8},
  {"dtstdg 8", 1, {0xed8321c4}, C_DD, 8},
  {"dtstdgq 8", 1, {0xfd8621c4}, C_QQ, 8},
  {"dtstdc 4", 1, {0xed831184}, C_DD, 8},
  {"dtstdcq 4", 1, {0xfd861184}, C_QQ, 8},
  {"dtstdg 4", 1, {0xed8311c4}, C_DD, 8},
  {"dtstdgq 4", 1, {0xfd8611c4}, C_QQ, 8},
  {"dtstdc 2", 1, {0xed830984}, C_DD, 8},
  {"dtstdcq 2", 1, {0xfd860984}, C_QQ, 8},
  {"dtstdg 2", 1, {0xed8309c4}, C_DD, 8},
  {"dtstdgq 2", 1, {0xfd8609c4}, C_QQ, 8},
  {"dtstdc 1", 1, {0xed830584}, C_DD, 8},
  {"dtstdcq 1", 1, {0xfd860584}, C_QQ, 8},
  {"dtstdg 1", 1, {0xed8305c4}, C_DD, 8},
  {"dtstdgq 1", 1, {0xfd8605c4}, C_QQ, 8},
  {"dtstdc 21", 1, {0xed835584}, C_DD, 8},
  {"dtstdcq 21", 1, {0xfd865584}, C_QQ, 8},
  {"dtstdg 21", 1, {0xed8355c4}, C_DD, 8},
  {"dtstdgq 21", 1, {0xfd8655c4}, C_QQ, 8},
  {"diex", 1, {0xec221ec4}, C_ED, 12},
  {"diexq", 1, {0xfd0236c4}, C_EQ, 12},
  {"dxex", 1, {0xec201ac4}, C_DD, 12},
  {"dxexq", 1, {0xfc2032c4}, C_QQ, 12},
  {"dctdp", 1, {0xec201a04}, C_D32, 12},
  {"drsp", 1, {0xec201e04}, C_DD, 24},
  {"dctqpq", 1, {0xfd001a04}, C_DD, 12},
  {"drdpq", 1, {0xfd003604}, C_QQ, 24},
  {"dcffix", 1, {0xec201e44}, C_INT, 16},
  {"dcffixq", 1, {0xfd001e44}, C_INT, 12},
  {"dctfix", 1, {0xec201a44}, C_DDI, 24},
  {"dctfixq", 1, {0xfc203244}, C_QQI, 24},
  {"dcffixqq", 1, {0xfd001fc4}, C_VINT, 16},
  {"dctfixqq", 1, {0xfc8137c4}, C_QQI, 24},
  {"dscli 0", 1, {0xec230084}, C_DD, 6},
  {"dscri 0", 1, {0xec2300c4}, C_DD, 6},
  {"dscliq 0", 1, {0xfd060084}, C_QQ, 6},
  {"dscriq 0", 1, {0xfd0600c4}, C_QQ, 6},
  {"dscli 1", 1, {0xec230484}, C_DD, 6},
  {"dscri 1", 1, {0xec2304c4}, C_DD, 6},
  {"dscliq 1", 1, {0xfd060484}, C_QQ, 6},
  {"dscriq 1", 1, {0xfd0604c4}, C_QQ, 6},
  {"dscli 5", 1, {0xec231484}, C_DD, 6},
  {"dscri 5", 1, {0xec2314c4}, C_DD, 6},
  {"dscliq 5", 1, {0xfd061484}, C_QQ, 6},
  {"dscriq 5", 1, {0xfd0614c4}, C_QQ, 6},
  {"dscli 15", 1, {0xec233c84}, C_DD, 6},
  {"dscri 15", 1, {0xec233cc4}, C_DD, 6},
  {"dscliq 15", 1, {0xfd063c84}, C_QQ, 6},
  {"dscriq 15", 1, {0xfd063cc4}, C_QQ, 6},
  {"dscli 16", 1, {0xec234084}, C_DD, 6},
  {"dscri 16", 1, {0xec2340c4}, C_DD, 6},
  {"dscliq 16", 1, {0xfd064084}, C_QQ, 6},
  {"dscriq 16", 1, {0xfd0640c4}, C_QQ, 6},
  {"dscli 17", 1, {0xec234484}, C_DD, 6},
  {"dscri 17", 1, {0xec2344c4}, C_DD, 6},
  {"dscliq 17", 1, {0xfd064484}, C_QQ, 6},
  {"dscriq 17", 1, {0xfd0644c4}, C_QQ, 6},
  {"dscli 33", 1, {0xec238484}, C_DD, 6},
  {"dscri 33", 1, {0xec2384c4}, C_DD, 6},
  {"dscliq 33", 1, {0xfd068484}, C_QQ, 6},
  {"dscriq 33", 1, {0xfd0684c4}, C_QQ, 6},
  {"dscli 34", 1, {0xec238884}, C_DD, 6},
  {"dscri 34", 1, {0xec2388c4}, C_DD, 6},
  {"dscliq 34", 1, {0xfd068884}, C_QQ, 6},
  {"dscriq 34", 1, {0xfd0688c4}, C_QQ, 6},
  {"dscli 35", 1, {0xec238c84}, C_DD, 6},
  {"dscri 35", 1, {0xec238cc4}, C_DD, 6},
  {"dscliq 35", 1, {0xfd068c84}, C_QQ, 6},
  {"dscriq 35", 1, {0xfd068cc4}, C_QQ, 6},
  {"dscli 63", 1, {0xec23fc84}, C_DD, 6},
  {"dscri 63", 1, {0xec23fcc4}, C_DD, 6},
  {"dscliq 63", 1, {0xfd06fc84}, C_QQ, 6},
  {"dscriq 63", 1, {0xfd06fcc4}, C_QQ, 6},
  {"ddedpd 0", 1, {0xec201a84}, C_DD, 12},
  {"ddedpdq 0", 1, {0xfd003284}, C_QQ, 12},
  {"ddedpd 1", 1, {0xec281a84}, C_DD, 12},
  {"ddedpdq 1", 1, {0xfd083284}, C_QQ, 12},
  {"ddedpd 2", 1, {0xec301a84}, C_DD, 12},
  {"ddedpdq 2", 1, {0xfd103284}, C_QQ, 12},
  {"ddedpd 3", 1, {0xec381a84}, C_DD, 12},
  {"ddedpdq 3", 1, {0xfd183284}, C_QQ, 12},
  {"denbcd 0", 1, {0xec201e84}, C_BCD0, 12},
  {"denbcdq 0", 1, {0xfd003684}, C_BCDQ0, 12},
  {"denbcd 1", 1, {0xec301e84}, C_BCD1, 12},
  {"denbcdq 1", 1, {0xfd103684}, C_BCDQ1, 12},
  {"bcdadd. 0", 1, {0x10821c01}, C_VSS, 16},
  {"bcdsub. 0", 1, {0x10821c41}, C_VSS, 16},
  {"bcds. 0", 1, {0x10821cc1}, C_VCS, 16},
  {"bcdsr. 0", 1, {0x10821dc1}, C_VCS, 16},
  {"bcdtrunc. 0", 1, {0x10821d01}, C_VCS, 16},
  {"bcdcfn. 0", 1, {0x10871d81}, C_VNAT, 12},
  {"bcdcfsq. 0", 1, {0x10821d81}, C_VQ, 12},
  {"bcdcfz. 0", 1, {0x10861d81}, C_VZ0, 12},
  {"bcdctz. 0", 1, {0x10841d81}, C_VS16, 12},
  {"bcdsetsgn. 0", 1, {0x109f1d81}, C_VSS, 12},
  {"bcdadd. 1", 1, {0x10821e01}, C_VSS, 16},
  {"bcdsub. 1", 1, {0x10821e41}, C_VSS, 16},
  {"bcds. 1", 1, {0x10821ec1}, C_VCS, 16},
  {"bcdsr. 1", 1, {0x10821fc1}, C_VCS, 16},
  {"bcdtrunc. 1", 1, {0x10821f01}, C_VCS, 16},
  {"bcdcfn. 1", 1, {0x10871f81}, C_VNAT, 12},
  {"bcdcfsq. 1", 1, {0x10821f81}, C_VQ, 12},
  {"bcdcfz. 1", 1, {0x10861f81}, C_VZ1, 12},
  {"bcdctz. 1", 1, {0x10841f81}, C_VS16, 12},
  {"bcdsetsgn. 1", 1, {0x109f1f81}, C_VSS, 12},
  {"bcdus.", 1, {0x10821c81}, C_VCU, 16},
  {"bcdutrunc.", 1, {0x10821d41}, C_VCU, 16},
  {"bcdcpsgn.", 1, {0x10821b41}, C_VSS, 12},
  {"bcdctn.", 1, {0x10851d81}, C_VS7, 12},
  {"bcdctsq.", 1, {0x10801d81}, C_VSS, 12},
  {"amr", 5, {0x7ced02a6, 0x7cad03a6, 0x7ccd02a6, 0x38a00000, 0x7ced03a6}, C_SHOW, 1},
  {"ctrl", 1, {0x7ca822a6}, C_SHOW, 1},
  {"ppr", 6, {0x7ca0e2a6, 0x38c00001, 0x78c6a2c6, 0x7cc0e3a6, 0x7cc0e2a6, 0x7ca0e3a6}, C_SHOW, 1},
  {"ppr of no priority", 7, {0x7ce0e2a6, 0x38c00007, 0x78c69346, 0x7cc0e3a6, 0x7cc0e2a6, 0x38a00000, 0x7ce0e3a6}, C_SHOW, 1},
  {"copy and cp_abort", 3, {0x7c20260c, 0x7c00068c, 0x38a00001}, C_SHOW, 1},
  {"hashst and hashchk", 5, {0x7ca62b78, 0x7fe435a5, 0x7fe435e5, 0x38a00001, 0x38c00002}, C_SHOW, 1},
  {"hashchk of another", 3, {0x7fe435a5, 0x38c60001, 0x7fe435e5}, C_SIGNAL, 1},
  {"paste.", 1, {0x7c20270d}, C_SIGNAL, 1},
  {"scv", 1, {0x44000001}, C_SIGNAL, 1},
  {"tbegin.", 1, {0x7c00051d}, C_SIGNAL, 1},
  {"tend.", 1, {0x7c00055d}, C_SIGNAL, 1},
  {"tabort.", 1, {0x7c05071d}, C_SIGNAL, 1},
  {"rfebb", 1, {0x4c000924}, C_SIGNAL, 1},
  {"clrbhrb", 1, {0x7c00035c}, C_SIGNAL, 1},
  {"mfbhrbe", 1, {0x7ca00a5c}, C_SIGNAL, 1},
  {"mtspr of ctrl", 1, {0x7ca823a6}, C_SIGNAL, 1},
  {"mtspr of uamor", 1, {0x7cbd23a6}, C_SIGNAL, 1},
  {"hashstp", 1, {0x7fe43525}, C_SIGNAL, 1},
  {"lwat of a function that isn't", 1, {0x7ca44c8c}, C_SIGNAL, 1},
  {"lxvkq of a reserved value", 1, {0xf05f52d1}, C_SIGNAL, 1},
  {"xxaes192encp", 1, {0xf0453610}, C_SIGNAL, 1},
  {"lxvrl", 1, {0x7c442c1b}, C_SIGNAL, 1},
  {"stxvrl", 1, {0x7c442d1b}, C_SIGNAL, 1},
  {"vucmprhb", 1, {0x10821883}, C_SIGNAL, 1},
  {"xxgfmul128xts", 1, {0xf04327d7}, C_SIGNAL, 1},
  {"xxssumudm", 1, {0xec4324cf}, C_SIGNAL, 1},
  {"vupkhsntob", 1, {0x10801183}, C_SIGNAL, 1},
  {"lxvpb32x", 1, {0x7c442eda}, C_SIGNAL, 1},
  {"xsaddadduqm", 1, {0xec432307}, C_SIGNAL, 1},
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
