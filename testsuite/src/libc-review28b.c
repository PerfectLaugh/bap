// What a review of the semantics of ARM and Thumb found, as the architecture and Linux have it:
//   zero: an offset of `#-0`, a subtraction of zero, of a load or a store is zero, of A32 and of T32, at a register, written back
//     before or after, and at the pc, where LLVM has it as INT32_MIN; and so is that of `sub r, pc, #0` of T32, which is ADR.
//   operands: what LLVM decodes with a warning and the architecture defines runs: the pc as the register that A32 shifts by an
//     immediate, which reads as the instruction's address plus 8, and the stack pointer as an operand of T32, in an IT block too, or
//     as the shifted register of A32, which ARMv8 defines.
//   traps: the undefined instructions that Linux takes as breakpoints (`arch/arm/kernel/ptrace.c`), 0xe7f001f0 of ARM and 0xde01
//     and 0xf7f0a000 of Thumb, are SIGTRAP of TRAP_BRKPT at them, and every other one SIGILL of ILL_ILLOPC: udf, and what is
//     UNDEFINED in the user mode, smc, hlt, the system registers of the floating point that aren't FPSCR, rfe and srs, and
//     `blx pc` of Thumb, which is UNPREDICTABLE, rather than what ends the run.
//   nothing: cps of 16 bits, which does nothing in the user mode, and pldw.
//   lanes: vmaxnm and vminnm of NEON.
// What is said is as qemu says it, but for the code of SIGILL, which qemu has as ILL_ILLOPN and Linux's `do_undefinstr` as
// ILL_ILLOPC, and for `blx pc`, which qemu branches by, to where isn't aligned here, and which is taken as UNDEFINED, one of what
// the architecture lets what is UNPREDICTABLE be.
#define _GNU_SOURCE
#include <setjmp.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <ucontext.h>

static sigjmp_buf back;
static volatile int told, code, at;

static void handler(int signal, siginfo_t *info, void *context) {
  ucontext_t *user = context;
  told = signal;
  code = info->si_code;
  at = (uint32_t)info->si_addr == user->uc_mcontext.arm_pc;
  siglongjmp(back, 1);
}

__asm__(".syntax unified\n.arch armv8-a\n.arch_extension sec\n.fpu neon-fp-armv8\n.text\n"
        // void zero_arm(uint32_t *words, uint32_t *out): `#-0` of A32. r4 is the base as it was, r9 the base, r8 the output.
        ".arm\n.globl zero_arm\n.type zero_arm, %function\nzero_arm:\n"
        " push {r4-r11, lr}\n mov r4, r0\n mov r9, r0\n mov r8, r1\n"
        " .inst 0xe519a000\n str r10, [r8], #4\n"                      // ldr r10, [r9, #-0]
        " .inst 0xe559a000\n str r10, [r8], #4\n"                      // ldrb r10, [r9, #-0]
        " mov r0, #0x5a\n .inst 0xe5690000\n"                          // strb r0, [r9, #-0]!
        " ldr r10, [r4]\n str r10, [r8], #4\n sub r10, r9, r4\n str r10, [r8], #4\n"
        " mov r9, r4\n .inst 0xe539a000\n str r10, [r8], #4\n"         // ldr r10, [r9, #-0]!
        " sub r10, r9, r4\n str r10, [r8], #4\n"
        " ldr r0, =0x11223344\n mov r9, r4\n .inst 0xe5090000\n"       // str r0, [r9, #-0]
        " ldr r10, [r4]\n str r10, [r8], #4\n"
        " .inst 0xe51fa000\n b 1f\n .word 0xcafe0001\n1: str r10, [r8], #4\n"  // ldr r10, [pc, #-0]
        " .inst 0xe55fa000\n b 1f\n .word 0x000000a7\n1: str r10, [r8], #4\n"  // ldrb r10, [pc, #-0]
        " mov r9, r4\n .inst 0xe419a000\n str r10, [r8], #4\n"         // ldr r10, [r9], #-0
        " sub r10, r9, r4\n str r10, [r8], #4\n"
        " .inst 0xe159a0b0\n str r10, [r8], #4\n"                      // ldrh r10, [r9, #-0]
        " .inst 0xf559f000\n .inst 0xf519f000\n"                       // pld [r9, #-0], pldw [r9, #-0]
        " pop {r4-r11, pc}\n.ltorg\n"
        // void zero_thumb(uint32_t *words, uint32_t *out): `#-0` of T32.
        ".thumb\n.globl zero_thumb\n.type zero_thumb, %function\n.thumb_func\nzero_thumb:\n"
        " push {r4-r11, lr}\n mov r4, r0\n mov r9, r0\n mov r8, r1\n"
        " .inst.w 0xf859ac00\n str r10, [r8], #4\n"                    // ldr r10, [r9, #-0]
        " .inst.w 0xf819ac00\n str r10, [r8], #4\n"                    // ldrb r10, [r9, #-0]
        " .inst.w 0xf939ac00\n str r10, [r8], #4\n"                    // ldrsh r10, [r9, #-0]
        " ldr r0, =0x55667788\n .inst.w 0xf8490c00\n"                  // str r0, [r9, #-0]
        " ldr r10, [r4]\n str r10, [r8], #4\n"
        " .inst.w 0xf859ad00\n str r10, [r8], #4\n"                    // ldr r10, [r9, #-0]!
        " sub r10, r9, r4\n str r10, [r8], #4\n"
        " mov r9, r4\n .inst.w 0xe959ab00\n str r10, [r8], #4\n str r11, [r8], #4\n"  // ldrd r10, r11, [r9, #-0]
        " .inst.w 0xf859a900\n str r10, [r8], #4\n"                    // ldr r10, [r9], #-0
        " sub r10, r9, r4\n str r10, [r8], #4\n"
        " mov r9, r4\n .inst.w 0xe879ab00\n str r11, [r8], #4\n"       // ldrd r10, r11, [r9], #-0
        " sub r10, r9, r4\n str r10, [r8], #4\n"
        " mov r9, r4\n ldr r0, =0x0badf00d\n .inst.w 0xf8290900\n"     // strh r0, [r9], #-0
        " ldr r10, [r4]\n str r10, [r8], #4\n sub r10, r9, r4\n str r10, [r8], #4\n"
        // Of the pc, what is loaded is the instruction after, a wide nop, as the pc is aligned.
        " .balign 4\n .inst.w 0xf85fa000\n nop.w\n str r10, [r8], #4\n"              // ldr.w r10, [pc, #-0]
        " .balign 4\n .inst.w 0xf81fa000\n nop.w\n str r10, [r8], #4\n"              // ldrb.w r10, [pc, #-0]
        " .balign 4\n .inst.w 0xe95fab00\n nop.w\n nop.w\n str r10, [r8], #4\n str r11, [r8], #4\n"  // ldrd r10, r11, [pc, #-0]
        " .balign 4\n1: .inst.w 0xf2af0a00\n adr r11, 1b\n sub r10, r10, r11\n str r10, [r8], #4\n"  // sub r10, pc, #0
        " nop\n1: .inst.w 0xf2af0a00\n adr r11, 1b\n sub r10, r10, r11\n str r10, [r8], #4\n"        // and where it isn't aligned
        " pop {r4-r11, pc}\n.ltorg\n"
        // void operands_arm(uint32_t *out): the pc and the stack pointer as what A32 shifts; each as it is less what it should be.
        ".arm\n.globl operands_arm\n.type operands_arm, %function\noperands_arm:\n"
        " push {r4-r11, lr}\n mov r8, r0\n mvn r4, #0\n"
        "1: .inst 0xe004a12f\n adr r11, 1b\n add r11, r11, #8\n lsr r11, r11, #2\n sub r10, r10, r11\n str r10, [r8], #4\n"  // and r10, r4, pc, lsr #2
        "1: .inst 0xe08fa08f\n adr r11, 1b\n add r11, r11, #8\n add r11, r11, r11, lsl #1\n sub r10, r10, r11\n str r10, [r8], #4\n"  // add r10, pc, pc, lsl #1
        "1: .inst 0xe1b0a08f\n adr r11, 1b\n add r11, r11, #8\n lsl r11, r11, #1\n sub r10, r10, r11\n str r10, [r8], #4\n"  // movs r10, pc, lsl #1
        " mov r4, #7\n .inst 0xe084a08d\n mov r11, sp\n lsl r11, r11, #1\n add r11, r11, r4\n sub r10, r10, r11\n str r10, [r8], #4\n"  // add r10, r4, sp, lsl #1
        " pop {r4-r11, pc}\n"
        // void operands_thumb(uint32_t *words, uint32_t *out): the stack pointer as an operand of T32.
        ".thumb\n.globl operands_thumb\n.type operands_thumb, %function\n.thumb_func\noperands_thumb:\n"
        " push {r4-r11, lr}\n mov r4, r0\n mov r8, r1\n ldr r5, =0x12345678\n"
        " mov r6, r8\n mov r8, r5\n .inst.w 0xeba80a0d\n mov r8, r6\n"                // sub.w r10, r8, sp
        " mov r11, sp\n sub r11, r5, r11\n sub r10, r10, r11\n str r10, [r8], #4\n"
        " .inst.w 0xf04d0a01\n mov r11, sp\n orr r11, r11, #1\n sub r10, r10, r11\n str r10, [r8], #4\n"  // orr.w r10, sp, #1
        " .inst.w 0xfa0ffa8d\n mov r11, sp\n sxth r11, r11\n sub r10, r10, r11\n str r10, [r8], #4\n"     // sxth.w r10, sp
        " mov r11, sp\n sub r9, r4, r11\n .inst.w 0xf859a00d\n str r10, [r8], #4\n"  // ldr.w r10, [r9, sp]
        // In an IT block, taken and not.
        " mov r6, r8\n mov r8, r5\n mov r10, #0\n cmp r0, r0\n it eq\n .inst.w 0xeba80a0d\n mov r8, r6\n"
        " mov r11, sp\n sub r11, r5, r11\n sub r10, r10, r11\n str r10, [r8], #4\n"
        " mov r6, r8\n mov r8, r5\n mov r10, #99\n cmp r0, r0\n ite ne\n .inst.w 0xeba80a0d\n nopeq\n mov r8, r6\n"
        " str r10, [r8], #4\n"
        " pop {r4-r11, pc}\n.ltorg\n"
        // Each instruction that may trap, and a return.
        ".arm\n"
        ".globl a_break\n.type a_break, %function\na_break: .inst 0xe7f001f0\n bx lr\n"
        ".globl a_udf\n.type a_udf, %function\na_udf: .inst 0xe7f00fff\n bx lr\n"
        ".globl a_smc\n.type a_smc, %function\na_smc: smc #0\n bx lr\n"
        ".globl a_hlt\n.type a_hlt, %function\na_hlt: .inst 0xe1000071\n bx lr\n"
        ".globl a_fpsid\n.type a_fpsid, %function\na_fpsid: vmrs r0, fpsid\n bx lr\n"
        ".globl a_mvfr0\n.type a_mvfr0, %function\na_mvfr0: vmrs r0, mvfr0\n bx lr\n"
        ".globl a_fpexc\n.type a_fpexc, %function\na_fpexc: vmrs r0, fpexc\n bx lr\n"
        ".globl a_setexc\n.type a_setexc, %function\na_setexc: vmsr fpexc, r0\n bx lr\n"
        ".globl a_rfe\n.type a_rfe, %function\na_rfe: rfeia r0\n bx lr\n"
        ".globl a_srs\n.type a_srs, %function\na_srs: srsdb sp, #19\n bx lr\n"
        ".globl a_fpscr\n.type a_fpscr, %function\na_fpscr: vmrs r0, fpscr\n bx lr\n"
        ".globl a_pldw\n.type a_pldw, %function\na_pldw: pldw [r0, #4]\n pldw [r0, r0]\n bx lr\n"
        ".globl a_cps\n.type a_cps, %function\na_cps: cpsid i\n bx lr\n"
        ".thumb\n"
        ".globl t_break\n.type t_break, %function\n.thumb_func\nt_break: .inst.n 0xde01\n bx lr\n"
        ".globl t_break2\n.type t_break2, %function\n.thumb_func\nt_break2: .inst.w 0xf7f0a000\n bx lr\n"
        ".globl t_udf\n.type t_udf, %function\n.thumb_func\nt_udf: .inst.n 0xdeff\n bx lr\n"
        ".globl t_udf2\n.type t_udf2, %function\n.thumb_func\nt_udf2: .inst.w 0xf7f1a000\n bx lr\n"
        ".globl t_smc\n.type t_smc, %function\n.thumb_func\nt_smc: smc #0\n bx lr\n"
        ".globl t_hlt\n.type t_hlt, %function\n.thumb_func\nt_hlt: .inst.n 0xba81\n bx lr\n"
        ".globl t_blxpc\n.type t_blxpc, %function\n.thumb_func\nt_blxpc: .inst.n 0x47f8\n bx lr\n"
        ".globl t_fpexc\n.type t_fpexc, %function\n.thumb_func\nt_fpexc: vmrs r0, fpexc\n bx lr\n"
        ".globl t_rfe\n.type t_rfe, %function\n.thumb_func\nt_rfe: rfeia r0\n bx lr\n"
        ".globl t_srs\n.type t_srs, %function\n.thumb_func\nt_srs: srsdb sp, #19\n bx lr\n"
        ".globl t_cps\n.type t_cps, %function\n.thumb_func\nt_cps: cpsid i\n cpsie i\n bx lr\n"
        ".globl t_pldw\n.type t_pldw, %function\n.thumb_func\nt_pldw: pldw [r0, #4]\n bx lr\n"
        // void lanes(const float *in, float *out): vmaxnm and vminnm of four lanes, and of two.
        ".arm\n.globl lanes\n.type lanes, %function\nlanes:\n"
        " vld1.32 {q1}, [r0]!\n vld1.32 {q2}, [r0]\n"
        " vmaxnm.f32 q0, q1, q2\n vst1.32 {q0}, [r1]!\n vminnm.f32 q0, q1, q2\n vst1.32 {q0}, [r1]!\n"
        " vmaxnm.f32 d0, d2, d4\n vst1.32 {d0}, [r1]!\n vminnm.f32 d0, d3, d5\n vst1.32 {d0}, [r1]!\n bx lr\n");

void zero_arm(uint32_t *words, uint32_t *out);
void zero_thumb(uint32_t *words, uint32_t *out);
void operands_arm(uint32_t *out);
void operands_thumb(uint32_t *words, uint32_t *out);
void a_break(void), a_udf(void), a_smc(void), a_hlt(void), a_fpsid(void), a_mvfr0(void), a_fpexc(void), a_setexc(void), a_rfe(void),
    a_srs(void), a_fpscr(void), a_pldw(void *), a_cps(void);
void t_break(void), t_break2(void), t_udf(void), t_udf2(void), t_smc(void), t_hlt(void), t_blxpc(void), t_fpexc(void), t_rfe(void),
    t_srs(void), t_cps(void), t_pldw(void *);
void lanes(const float *in, float *out);

static uint32_t words[8];

static void fill(void) {
  for (int index = 0; index < 8; index++) words[index] = 0x80c0e0f1u + 0x01020304u * (uint32_t)index;
}

static void show(const char *name, const uint32_t *out, int count) {
  printf("%s:", name);
  for (int index = 0; index < count; index++) printf(" %08x", out[index]);
  printf("\n");
}

#define PROBE(name, call)                                                                                                            \
  do {                                                                                                                               \
    if (sigsetjmp(back, 1) == 0) {                                                                                                   \
      call;                                                                                                                          \
      printf("%s: runs\n", name);                                                                                                    \
    } else {                                                                                                                         \
      printf("%s: signal %d code %d at it %d\n", name, told, code, at);                                                              \
    }                                                                                                                                \
  } while (0)

int main(void) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_sigaction = handler;
  action.sa_flags = SA_SIGINFO;
  sigaction(SIGILL, &action, 0);
  sigaction(SIGTRAP, &action, 0);
  sigaction(SIGSEGV, &action, 0);
  sigaction(SIGBUS, &action, 0);
  uint32_t out[24];
  memset(out, 0, sizeof out);
  fill();
  PROBE("#-0 of ARM", zero_arm(words + 4, out));
  show("which loads", out, 12);
  memset(out, 0, sizeof out);
  fill();
  PROBE("#-0 of Thumb", zero_thumb(words + 4, out));
  show("which loads", out, 20);
  memset(out, 0xff, sizeof out);
  PROBE("the pc and sp that ARM shifts", operands_arm(out));
  show("off by", out, 4);
  memset(out, 0xff, sizeof out);
  fill();
  PROBE("sp of Thumb", operands_thumb(words + 4, out));
  show("off by", out, 6);
  PROBE("ARM 0xe7f001f0", a_break());
  PROBE("ARM udf #255", a_udf());
  PROBE("ARM smc", a_smc());
  PROBE("ARM hlt", a_hlt());
  PROBE("ARM vmrs fpsid", a_fpsid());
  PROBE("ARM vmrs mvfr0", a_mvfr0());
  PROBE("ARM vmrs fpexc", a_fpexc());
  PROBE("ARM vmsr fpexc", a_setexc());
  PROBE("ARM rfeia", a_rfe());
  PROBE("ARM srsdb", a_srs());
  PROBE("ARM vmrs fpscr", a_fpscr());
  PROBE("ARM pldw", a_pldw(words));
  PROBE("ARM cpsid", a_cps());
  PROBE("Thumb 0xde01", t_break());
  PROBE("Thumb 0xf7f0a000", t_break2());
  PROBE("Thumb udf #255", t_udf());
  PROBE("Thumb udf.w #1", t_udf2());
  PROBE("Thumb smc", t_smc());
  PROBE("Thumb hlt", t_hlt());
  PROBE("Thumb blx pc", t_blxpc());
  PROBE("Thumb vmrs fpexc", t_fpexc());
  PROBE("Thumb rfeia", t_rfe());
  PROBE("Thumb srsdb", t_srs());
  PROBE("Thumb cpsid, cpsie", t_cps());
  PROBE("Thumb pldw", t_pldw(words));
  static const uint32_t in[8] = {0x3f800000, 0x7fc00000, 0x80000000, 0x7fa00000, 0x7fc00001, 0x40000000, 0x00000000, 0x3f800000};
  uint32_t result[12];
  memset(result, 0, sizeof result);
  PROBE("vmaxnm, vminnm", lanes((const float *)in, (float *)result));
  show("which are", result, 12);
  return 0;
}
