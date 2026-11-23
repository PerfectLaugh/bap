// What a review of the semantics of AArch64 found, as a processor without the pointer authentication and Linux have it:
//   traps: what is of EL1, or needs what Linux doesn't give EL0, is SIGILL of ILL_ILLOPC at the instruction, rather than run as at EL1
//     or what ends the run: DAIF read, written and set and cleared by immediates (SCTLR_EL1.UMA isn't set), SPSel, PAN and UAO, SP_EL0,
//     and hlt, which is UNDEFINED while halting isn't allowed. The instructions of the pointer authentication that aren't hints are
//     UNDEFINED where a processor doesn't have it, as AT_HWCAP says this one doesn't; the hints are NOPs.
//   fixed: fcvtzs and fcvtzu of half precision with 16 fraction bits, of the lanes and of the scalars, scale on the exponent rather
//     than by 2^16, which isn't a half; and what the fixed-point conversions raise is of the conversion alone: a number too large is
//     invalid, not an overflow of its scaling too. fjcvtzs and the conversions of the lanes raise what they do.
//   status: the bits of FPCR and FPSR that are RES0 read as zero. The bits of FEAT_AFP and FEAT_EBF16 and of the short vectors of
//     AArch32, which qemu's processor has and this one doesn't, aren't said.
//   sve: frecpx, fexpa, ftmad and fscale, by their tables and with what they raise.
//   tags: an address with a tag is EFAULT of a system call until the thread asks with PR_SET_TAGGED_ADDR_CTRL, which a child has from
//     it; an exclusive store through another tag than its load's goes.
// What is said is as qemu says it with `-cpu max,pauth=off`, but for the code of SIGILL, which qemu has as ILL_ILLOPN.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/prctl.h>
#include <sys/syscall.h>
#include <sys/utsname.h>
#include <sys/wait.h>
#include <ucontext.h>
#include <unistd.h>

static sigjmp_buf back;
static volatile int told, code, at;

static void handler(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  told = signal;
  code = info->si_code;
  at = (uint64_t)info->si_addr == user->uc_mcontext.pc;
  siglongjmp(back, 1);
}

static uint64_t scratch[4];

// One instruction, with x0 and x1 where it may read and write.
#define PROBE(name, word)                                                                                                            \
  do {                                                                                                                               \
    if (sigsetjmp(back, 1) == 0) {                                                                                                   \
      register uint64_t x0 __asm__("x0") = (uint64_t)scratch;                                                                        \
      register uint64_t x1 __asm__("x1") = 1;                                                                                        \
      __asm__ volatile(".inst " #word : "+r"(x0), "+r"(x1) : : "x16", "x17", "memory");                                              \
      printf("%s: runs\n", name);                                                                                                    \
    } else {                                                                                                                         \
      printf("%s: signal %d code %d at it %d\n", name, told, code, at);                                                              \
    }                                                                                                                                \
  } while (0)

static void traps(void) {
  PROBE("mrs x0, daif", 0xd53b4220);
  PROBE("msr daif, x1", 0xd51b4221);
  PROBE("msr daifset, #2", 0xd50342df);
  PROBE("msr daifclr, #1", 0xd50341ff);
  PROBE("msr spsel, #1", 0xd50041bf);
  PROBE("mrs x0, spsel", 0xd5384200);
  PROBE("msr pan, #1", 0xd500419f);
  PROBE("msr uao, #1", 0xd500417f);
  PROBE("mrs x0, sp_el0", 0xd5384100);
  PROBE("hlt #1", 0xd4400020);
  PROBE("pacga x0, x0, x1", 0x9ac13000);
  PROBE("pacia x0, x1", 0xdac10020);
  PROBE("autia x0, x1", 0xdac11020);
  PROBE("pacdza x0", 0xdac123e0);
  PROBE("xpaci x0", 0xdac143e0);
  PROBE("xpacd x0", 0xdac147e0);
  PROBE("retaa", 0xd65f0bff);
  PROBE("braaz x0", 0xd61f081f);
  PROBE("blraa x0, x1", 0xd73f0801);
  PROBE("ldraa x1, [x0]", 0xf8200401);
  PROBE("paciasp", 0xd503233f);
  PROBE("pacia1716", 0xd503211f);
  PROBE("xpaclri", 0xd50320ff);
  PROBE("nop", 0xd503201f);
}

// The routines of floating point, in assembly, as what compiles this doesn't know all of their instructions.
__asm__(".arch armv8.5-a+fp16+sve\n"
        ".text\n"
        // void fixed16(const uint16_t in[8], uint16_t out[5][8]): of the lanes and of the scalar; uint64_t fpsr after.
        ".globl fixed16\n.type fixed16, %function\nfixed16:\n"
        " msr fpsr, xzr\n ldr q1, [x0]\n"
        " fcvtzu v0.4h, v1.4h, #16\n str q0, [x1]\n"
        " fcvtzs v0.8h, v1.8h, #16\n str q0, [x1, #16]\n"
        " fcvtzu h0, h1, #16\n str q0, [x1, #32]\n"
        " fcvtzs h0, h1, #12\n str q0, [x1, #48]\n"
        " fcvtzu v0.8h, v1.8h, #15\n str q0, [x1, #64]\n"
        " mrs x0, fpsr\n ret\n"
        // uint64_t fixedx(uint64_t bits, uint64_t *fpsr): fcvtzs x, d, #10
        ".globl fixedx\n.type fixedx, %function\nfixedx:\n"
        " msr fpsr, xzr\n fmov d1, x0\n fcvtzs x0, d1, #10\n mrs x2, fpsr\n str x2, [x1]\n ret\n"
        // uint64_t fixedw(uint64_t bits, uint64_t *fpsr): fcvtzu w, d, #1
        ".globl fixedw\n.type fixedw, %function\nfixedw:\n"
        " msr fpsr, xzr\n fmov d1, x0\n fcvtzu w0, d1, #1\n mrs x2, fpsr\n str x2, [x1]\n ret\n"
        // uint64_t fixedh(uint64_t bits, uint64_t *fpsr): fcvtzs x, h, #40
        ".globl fixedh\n.type fixedh, %function\nfixedh:\n"
        " msr fpsr, xzr\n fmov h1, w0\n fcvtzs x0, h1, #40\n mrs x2, fpsr\n str x2, [x1]\n ret\n"
        // uint64_t js(uint64_t bits, uint64_t out[2]): fjcvtzs, with the flags and FPSR after
        ".globl js\n.type js, %function\njs:\n"
        " msr fpsr, xzr\n fmov d1, x0\n fjcvtzs w0, d1\n mrs x2, nzcv\n str x2, [x1]\n mrs x2, fpsr\n str x2, [x1, #8]\n ret\n"
        // uint64_t lanes(const uint64_t in[2], uint64_t out[6]): the conversions of the lanes; FPSR after each
        ".globl lanes\n.type lanes, %function\nlanes:\n"
        " ldr q1, [x0]\n"
        " msr fpsr, xzr\n fcvtzs v0.2d, v1.2d\n str q0, [x1]\n mrs x2, fpsr\n str x2, [x1, #16]\n"
        " msr fpsr, xzr\n fcvtnu v0.4s, v1.4s\n str q0, [x1, #24]\n mrs x2, fpsr\n str x2, [x1, #40]\n"
        " msr fpsr, xzr\n fcvtzu d0, d1, #64\n str d0, [x1, #48]\n mrs x2, fpsr\n str x2, [x1, #56]\n"
        " ret\n"
        // void status(uint64_t out[2]): FPCR and FPSR written with ones, as they read, and left as they were
        ".globl status\n.type status, %function\nstatus:\n"
        " mrs x3, fpcr\n mov x1, #-1\n msr fpcr, x1\n mrs x2, fpcr\n str x2, [x0]\n msr fpcr, x3\n"
        " msr fpsr, x1\n mrs x2, fpsr\n str x2, [x0, #8]\n msr fpsr, xzr\n ret\n"
        // uint64_t sve(int which, const uint64_t in[4], uint64_t out[2], uint64_t control): an operation of the two vectors of 128
        // bits at in, with FPCR as given; FPSR after
        ".globl sve\n.type sve, %function\nsve:\n"
        " mrs x9, fpcr\n msr fpcr, x3\n msr fpsr, xzr\n ptrue p0.b, vl16\n ld1d z0.d, p0/z, [x1]\n add x1, x1, #16\n ld1d z1.d, p0/z, [x1]\n"
        " cmp w0, #1\n b.eq 1f\n cmp w0, #2\n b.eq 2f\n cmp w0, #3\n b.eq 3f\n cmp w0, #4\n b.eq 4f\n cmp w0, #5\n b.eq 5f\n"
        " cmp w0, #6\n b.eq 6f\n cmp w0, #7\n b.eq 7f\n cmp w0, #8\n b.eq 8f\n cmp w0, #9\n b.eq 9f\n cmp w0, #10\n b.eq 10f\n"
        " frecpx z0.d, p0/m, z0.d\n b 0f\n"
        "1: frecpx z0.s, p0/m, z0.s\n b 0f\n"
        "2: frecpx z0.h, p0/m, z0.h\n b 0f\n"
        "3: fexpa z0.d, z0.d\n b 0f\n"
        "4: fexpa z0.s, z0.s\n b 0f\n"
        "5: fexpa z0.h, z0.h\n b 0f\n"
        "6: ftmad z0.d, z0.d, z1.d, #5\n b 0f\n"
        "7: ftmad z0.s, z0.s, z1.s, #2\n b 0f\n"
        "8: ftmad z0.h, z0.h, z1.h, #1\n b 0f\n"
        "9: fscale z0.d, p0/m, z0.d, z1.d\n b 0f\n"
        "10: fscale z0.s, p0/m, z0.s, z1.s\n"
        "0: st1d z0.d, p0, [x2]\n mrs x0, fpsr\n msr fpcr, x9\n ret\n"
        // int exclusive(uint64_t *loaded, uint64_t *stored): a load and a store, each through its own address of the same word
        ".globl exclusive\n.type exclusive, %function\nexclusive:\n"
        " ldxr x2, [x0]\n add x2, x2, #1\n stxr w3, x2, [x1]\n mov w0, w3\n ret\n");

uint64_t fixed16(const uint16_t *in, uint16_t (*out)[8]);
uint64_t fixedx(uint64_t bits, uint64_t *fpsr);
uint64_t fixedw(uint64_t bits, uint64_t *fpsr);
uint64_t fixedh(uint64_t bits, uint64_t *fpsr);
uint64_t js(uint64_t bits, uint64_t *out);
void lanes(const uint64_t *in, uint64_t *out);
void status(uint64_t *out);
uint64_t sve(int which, const uint64_t *in, uint64_t *out, uint64_t control);
int exclusive(uint64_t *loaded, uint64_t *stored);

static void fixed(void) {
  static const uint16_t halves[8] = {0x3800, 0x0001, 0x3bff, 0x0200, 0xb800, 0x7bff, 0xfbff, 0x7e00};
  uint16_t out[5][8];
  memset(out, 0, sizeof out);
  uint64_t fpsr = fixed16(halves, out);
  static const char *const names[5] = {"fcvtzu v.4h #16", "fcvtzs v.8h #16", "fcvtzu h #16", "fcvtzs h #12", "fcvtzu v.8h #15"};
  for (int row = 0; row < 5; row++) {
    printf("%s:", names[row]);
    for (int lane = 0; lane < 8; lane++) printf(" %04x", out[row][lane]);
    printf("\n");
  }
  printf("their fpsr: %llx\n", (unsigned long long)fpsr);
  static const uint64_t doubles[] = {0x7fefffffffffffffull, 0xc3e0000000000001ull, 0x41dfffffffc00000ull, 0xc1e0000000100000ull,
                                     0x3fe0000000000000ull, 0xbfe0000000000000ull, 0x0000000000000001ull, 0x7ff0000000000000ull,
                                     0x7ff4000000000000ull, 0x4059000000000000ull, 0x8000000000000000ull};
  for (unsigned index = 0; index < sizeof doubles / sizeof *doubles; index++) {
    uint64_t raised = 0, flags[2];
    uint64_t wide = fixedx(doubles[index], &raised);
    printf("fcvtzs x, d, #10 of %016llx: %016llx fpsr %llx\n", (unsigned long long)doubles[index], (unsigned long long)wide,
           (unsigned long long)raised);
    uint64_t narrow = fixedw(doubles[index], &raised);
    printf("fcvtzu w, d, #1: %08llx fpsr %llx\n", (unsigned long long)narrow, (unsigned long long)raised);
    uint64_t script = js(doubles[index], flags);
    printf("fjcvtzs: %08llx nzcv %llx fpsr %llx\n", (unsigned long long)script, (unsigned long long)flags[0],
           (unsigned long long)flags[1]);
  }
  for (int index = 0; index < 8; index++) {
    uint64_t raised = 0;
    uint64_t wide = fixedh(halves[index], &raised);
    printf("fcvtzs x, h, #40 of %04x: %016llx fpsr %llx\n", halves[index], (unsigned long long)wide, (unsigned long long)raised);
  }
  static const uint64_t pairs[][2] = {{0x3ff8000000000000ull, 0x43e0000000000000ull},
                                      {0x7ff8000000000000ull, 0xc000000000000000ull},
                                      {0x3fe00000c1200000ull, 0x4f8000007fc00000ull}};
  for (int index = 0; index < 3; index++) {
    uint64_t out[8];
    memset(out, 0, sizeof out);
    lanes(pairs[index], out);
    printf("fcvtzs v.2d: %016llx %016llx fpsr %llx\n", (unsigned long long)out[0], (unsigned long long)out[1], (unsigned long long)out[2]);
    printf("fcvtnu v.4s: %016llx %016llx fpsr %llx\n", (unsigned long long)out[3], (unsigned long long)out[4], (unsigned long long)out[5]);
    printf("fcvtzu d #64: %016llx fpsr %llx\n", (unsigned long long)out[6], (unsigned long long)out[7]);
  }
  uint64_t registers[2];
  status(registers);
  // Without Stride, Len, EBF and the bits of FEAT_AFP, which qemu's processor has.
  printf("fpcr of ones: %llx\n", (unsigned long long)(registers[0] & ~0x00372007ull));
  printf("fpsr of ones: %llx\n", (unsigned long long)registers[1]);
}

static void vectors(void) {
  static const char *const names[] = {"frecpx d", "frecpx s", "frecpx h", "fexpa d", "fexpa s", "fexpa h", "ftmad d #5",
                                      "ftmad s #2", "ftmad h #1", "fscale d", "fscale s"};
  static const uint64_t inputs[][4] = {
      {0x3ff8000000000000ull, 0x7ff4000000000000ull, 0, 0},
      {0x0000000140490fdbull, 0x7fa00000ff800000ull, 0, 0},
      {0x7d003c0000018400ull, 0xfc007e00c2000000ull, 0, 0},
      {0x00000000000ffc3full, 0x0000000000000041ull, 0, 0},
      {0x0000207f00000001ull, 0x0000003f00001fc0ull, 0, 0},
      {0x03ff001f00010000ull, 0x0020021f000a0011ull, 0, 0},
      {0x3fe0000000000000ull, 0x4000000000000000ull, 0x3fd0000000000000ull, 0xbfd0000000000000ull},
      {0x3f000000c0400000ull, 0x7fa0000040000000ull, 0x3e800000be800000ull, 0x3f8000003f800000ull},
      {0xc2003c0038004000ull, 0x7d0038003c00c000ull, 0x3400b4003400b400ull, 0x3c003c00b4003400ull},
      {0x3ff8000000000000ull, 0x0000000000000003ull, 0x0000000000000400ull, 0x0000000000000035ull},
      {0x3fc0000000000001ull, 0x7f7fffff00800000ull, 0xffffffe200000017ull, 0x00000001ffffffe9ull}};
  static const uint64_t controls[] = {0, 0x00c00000, 0x02000000, 0x01000000};
  for (int which = 0; which < 11; which++)
    for (int control = 0; control < (which >= 9 ? 4 : which >= 6 ? 3 : 1); control++) {
      uint64_t out[2] = {0, 0};
      uint64_t fpsr = sve(which, inputs[which], out, controls[control]);
      printf("%s, fpcr %llx: %016llx %016llx fpsr %llx\n", names[which], (unsigned long long)controls[control],
             (unsigned long long)out[0], (unsigned long long)out[1], (unsigned long long)fpsr);
    }
  // Every index of the tables of fexpa, as a sum of each.
  uint64_t sums[3] = {0, 0, 0};
  for (uint64_t index = 0; index < 64; index += 2) {
    uint64_t in[4] = {index, index + 1, 0, 0}, out[2];
    sve(3, in, out, 0);
    sums[0] += out[0] * (index + 3) + out[1];
    in[0] = index | (index + 1) << 32;
    in[1] = (index + 32) | (index + 33) << 32;
    sve(4, in, out, 0);
    sums[1] += out[0] * (index + 3) + out[1];
    in[0] = (index & 31) | ((index + 1) & 31) << 16 | (uint64_t)((index + 7) & 31) << 32 | (uint64_t)((index + 12) & 31) << 48;
    in[1] = ((index + 16) & 31) | ((index + 17) & 31) << 16 | (uint64_t)((index + 23) & 31) << 32 | (uint64_t)((index + 28) & 31) << 48;
    sve(5, in, out, 0);
    sums[2] += out[0] * (index + 3) + out[1];
  }
  printf("fexpa, all of it: %016llx %016llx %016llx\n", (unsigned long long)sums[0], (unsigned long long)sums[1],
         (unsigned long long)sums[2]);
}

static void said(const char *what, long result) {
  if (result < 0) printf("%s: %s\n", what, strerror(errno));
  else printf("%s: %ld\n", what, result);
}

static void tags(void) {
  static struct utsname name;
  static uint64_t word = 41;
  static char path[] = "/nowhere";
  uint64_t tag = 0x5aull << 56;
  struct utsname *tagged = (struct utsname *)((uint64_t)&name | tag);
  said("PR_GET_TAGGED_ADDR_CTRL", prctl(PR_GET_TAGGED_ADDR_CTRL, 0, 0, 0, 0));
  said("uname at a tag", syscall(SYS_uname, tagged));
  said("openat of a path at a tag", syscall(SYS_openat, AT_FDCWD, (uint64_t)path | tag, O_RDONLY));
  said("write of nothing at a tag", syscall(SYS_write, 1, (uint64_t)path | tag, 0));
  said("write of nothing", syscall(SYS_write, 1, path, 0));
  // The instructions of the program ignore the tag whatever the kernel does.
  *(uint64_t *)((uint64_t)&word | tag) += 1;
  said("a store at a tag", (long)word);
  said("an exclusive store at another tag", exclusive((uint64_t *)((uint64_t)&word | tag), (uint64_t *)((uint64_t)&word | 0x33ull << 56)));
  said("which stored", (long)word);
  said("PR_SET_TAGGED_ADDR_CTRL of what isn't", prctl(PR_SET_TAGGED_ADDR_CTRL, 1ul << 19, 0, 0, 0));
  said("PR_SET_TAGGED_ADDR_CTRL with more", prctl(PR_SET_TAGGED_ADDR_CTRL, 1, 1, 0, 0));
  said("PR_SET_TAGGED_ADDR_CTRL", prctl(PR_SET_TAGGED_ADDR_CTRL, PR_TAGGED_ADDR_ENABLE, 0, 0, 0));
  said("PR_GET_TAGGED_ADDR_CTRL", prctl(PR_GET_TAGGED_ADDR_CTRL, 0, 0, 0, 0));
  said("uname at a tag", syscall(SYS_uname, tagged));
  said("openat of a path at a tag", syscall(SYS_openat, AT_FDCWD, (uint64_t)path | tag, O_RDONLY));
  said("write of nothing at a tag", syscall(SYS_write, 1, (uint64_t)path | tag, 0));
  fflush(stdout);
  pid_t child = fork();
  if (child == 0) {
    said("PR_GET_TAGGED_ADDR_CTRL of a child", prctl(PR_GET_TAGGED_ADDR_CTRL, 0, 0, 0, 0));
    said("uname at a tag of a child", syscall(SYS_uname, tagged));
    fflush(stdout);
    _exit(0);
  }
  int status;
  waitpid(child, &status, 0);
  said("PR_SET_TAGGED_ADDR_CTRL of none", prctl(PR_SET_TAGGED_ADDR_CTRL, 0, 0, 0, 0));
  said("uname at a tag", syscall(SYS_uname, tagged));
}

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = handler;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGILL, &action, 0);
  sigaction(SIGTRAP, &action, 0);
  sigaction(SIGSEGV, &action, 0);
  sigaction(SIGBUS, &action, 0);
  traps();
  fixed();
  vectors();
  tags();
  return 0;
}
