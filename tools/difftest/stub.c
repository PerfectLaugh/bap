// The hardware's side of the differential test: reads records of an instruction, the registers and a window of memory from
// the standard input, runs each, and writes the registers and the window it ends with. No libc, so that one source runs
// natively on x86 and under qemu-user on the rest. See difftest.py, which has the layout of a record.
//
// The instruction is put in `slot`, at the same address each time, so a pc-relative result is comparable. A falling through
// program ends at slot+32, a taken branch is aimed at slot+0x40. No register is reserved: the first saved register goes where
// the instruction can't see it (TPIDR_EL0, TPIDRURW, a floating point register, TAR or VRSAVE), and x86 has absolute addresses.

#define SLOT 32
#define WINDOW 512

#if defined(__x86_64__)
#define WORD unsigned long long
#define NGPR 16
#define NEXTRA 1
#define VECBYTES (16 * 32 + 8 * 8)
#elif defined(__i386__)
#define WORD unsigned int
#define NGPR 8
#define NEXTRA 1
#define VECBYTES (8 * 32 + 8 * 8)
#elif defined(__aarch64__)
#define WORD unsigned long long
#define NGPR 32
#define NEXTRA 2
// the V registers, which are the Z registers at a vector length of 128 bits, P0 to P15, FFR, and padding
#define VECBYTES (32 * 16 + 40)
#elif defined(__arm__)
#define WORD unsigned int
#define NGPR 16
#define NEXTRA 2
#define VECBYTES (32 * 8)
#elif defined(__riscv)
#define WORD unsigned long
#define NGPR 32
#define NEXTRA 0
#define VECBYTES (32 * 8)
#elif defined(__mips__)
#define WORD unsigned long
#define NGPR 32
#define NEXTRA 3 // HI, LO, FCSR
#if __mips_isa_rev >= 6
#define VECBYTES (32 * 8)
#else
#define VECBYTES (32 * sizeof(WORD))
#endif
#elif defined(__powerpc__)
#define WORD unsigned long
#define NGPR 32
#define NEXTRA 4
#define VECBYTES (32 * 8 + 32 * 16)
#endif

#define STATE (sizeof(WORD) * (NGPR + NEXTRA) + VECBYTES)

unsigned char st_in[STATE + 64] __attribute__((aligned(4096)));
unsigned char st_out[STATE + 64] __attribute__((aligned(64)));
unsigned char window[WINDOW] __attribute__((aligned(4096)));
unsigned long long marker;
WORD host_sp;
static unsigned char altstack[65536] __attribute__((aligned(4096)));
static unsigned char buffer[STATE + WINDOW + SLOT + 8 + 64] __attribute__((aligned(16)));

extern unsigned char slot[], taken[];
void enter(void);
void recover(void) __attribute__((noreturn));

// System calls.
#if defined(__x86_64__)
enum { SYS_read = 0, SYS_write = 1, SYS_exit = 60, SYS_sigaction = 13, SYS_altstack = 131 };
static long sys3(long n, long a, long b, long c, long d) {
  long r;
  register long r10 __asm__("r10") = d;
  __asm__ volatile("syscall" : "=a"(r) : "a"(n), "D"(a), "S"(b), "d"(c), "r"(r10) : "rcx", "r11", "memory");
  return r;
}
#elif defined(__i386__)
enum { SYS_read = 3, SYS_write = 4, SYS_exit = 1, SYS_sigaction = 174, SYS_altstack = 186 };
static long sys3(long n, long a, long b, long c, long d) {
  long r;
  __asm__ volatile("int $0x80" : "=a"(r) : "a"(n), "b"(a), "c"(b), "d"(c), "S"(d) : "memory");
  return r;
}
#elif defined(__aarch64__) || defined(__riscv)
enum { SYS_read = 63, SYS_write = 64, SYS_exit = 93, SYS_sigaction = 134, SYS_altstack = 132 };
static long sys3(long n, long a, long b, long c, long d) {
#if defined(__aarch64__)
  register long x8 __asm__("x8") = n;
  register long x0 __asm__("x0") = a;
  register long x1 __asm__("x1") = b;
  register long x2 __asm__("x2") = c;
  register long x3 __asm__("x3") = d;
  __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2), "r"(x3) : "memory");
  return x0;
#else
  register long a7 __asm__("a7") = n;
  register long a0 __asm__("a0") = a;
  register long a1 __asm__("a1") = b;
  register long a2 __asm__("a2") = c;
  register long a3 __asm__("a3") = d;
  __asm__ volatile("ecall" : "+r"(a0) : "r"(a7), "r"(a1), "r"(a2), "r"(a3) : "memory");
  return a0;
#endif
}
#elif defined(__arm__)
enum { SYS_read = 3, SYS_write = 4, SYS_exit = 1, SYS_sigaction = 174, SYS_altstack = 186 };
static long sys3(long n, long a, long b, long c, long d) {
  register long r7 __asm__("r7") = n;
  register long r0 __asm__("r0") = a;
  register long r1 __asm__("r1") = b;
  register long r2 __asm__("r2") = c;
  register long r3 __asm__("r3") = d;
  __asm__ volatile("svc 0" : "+r"(r0) : "r"(r7), "r"(r1), "r"(r2), "r"(r3) : "memory");
  return r0;
}
#elif defined(__mips__)
#if _MIPS_SIM == _ABIO32
enum { SYS_read = 4003, SYS_write = 4004, SYS_exit = 4001, SYS_sigaction = 4194, SYS_altstack = 4206 };
#define MIPS_CLOBBER "$8", "$9", "$10", "$11", "$12", "$13", "$14", "$15", "$24", "$25", "$31"
#else
enum { SYS_read = 5000, SYS_write = 5001, SYS_exit = 5058, SYS_sigaction = 5013, SYS_altstack = 5129 };
#define MIPS_CLOBBER "$8", "$9", "$10", "$11", "$12", "$13", "$14", "$15", "$24", "$25", "$31"
#endif
static long sys3(long n, long a, long b, long c, long d) {
  register long v0 __asm__("$2") = n;
  register long a0 __asm__("$4") = a;
  register long a1 __asm__("$5") = b;
  register long a2 __asm__("$6") = c;
  register long a3 __asm__("$7") = d;
  __asm__ volatile("syscall" : "+r"(v0), "+r"(a3) : "r"(a0), "r"(a1), "r"(a2) : "$1", "$3", MIPS_CLOBBER, "hi", "lo", "memory");
  return v0;
}
#elif defined(__powerpc__)
enum { SYS_read = 3, SYS_write = 4, SYS_exit = 1, SYS_sigaction = 173, SYS_altstack = 185 };
static long sys3(long n, long a, long b, long c, long d) {
  register long r0 __asm__("r0") = n;
  register long r3 __asm__("r3") = a;
  register long r4 __asm__("r4") = b;
  register long r5 __asm__("r5") = c;
  register long r6 __asm__("r6") = d;
  __asm__ volatile("sc" : "+r"(r3) : "r"(r0), "r"(r4), "r"(r5), "r"(r6)
                   : "r7", "r8", "r9", "r10", "r11", "r12", "cr0", "ctr", "memory");
  return r3;
}
#endif

static void copy(unsigned char *to, const unsigned char *from, unsigned long size) {
  for (unsigned long i = 0; i < size; i++)
    ((volatile unsigned char *)to)[i] = from[i];
}

static long read_all(unsigned char *to, long size) {
  long got = 0;
  while (got < size) {
    long r = sys3(SYS_read, 0, (long)(to + got), size - got, 0);
    if (r <= 0)
      return got;
    got += r;
  }
  return got;
}

static void write_all(const unsigned char *from, long size) {
  long done = 0;
  while (done < size) {
    long r = sys3(SYS_write, 1, (long)(from + done), size - done, 0);
    if (r <= 0)
      sys3(SYS_exit, 3, 0, 0, 0);
    done += r;
  }
}

// A fault is an outcome, not the end: the handler doesn't return, it goes back to the driver as the instruction would have.
__attribute__((used)) void on_signal(int number) {
  marker = 2 | ((unsigned long long)number << 8);
  recover();
}

#define SA_ONSTACK_ 0x08000000ul
#define SA_NODEFER_ 0x40000000ul

static void restorer(void) {}

static void install(int number) {
#if defined(__mips__)
  struct {
    unsigned int flags;
    void *handler;
    unsigned long mask[16 / sizeof(unsigned long)];
  } action = {0x08000000u | 0x40000000u, (void *)on_signal, {0}};
  sys3(SYS_sigaction, number, (long)&action, 0, 16);
#else
  // the targets without a restorer have the mask where this has it, which has to be zero
#if defined(__x86_64__) || defined(__i386__) || defined(__arm__)
  void *back = (void *)restorer;
  unsigned long extra = 0x04000000ul;
#else
  void *back = 0;
  unsigned long extra = 0;
#endif
  struct {
    void *handler;
    unsigned long flags;
    void *restorer;
    unsigned long mask[2];
  } action = {(void *)on_signal, SA_ONSTACK_ | SA_NODEFER_ | extra, back, {0, 0}};
  sys3(SYS_sigaction, number, (long)&action, 0, 8);
#endif
}

__attribute__((used)) void cmain(void) {
#if defined(__mips__)
  struct { void *sp; unsigned long size; int flags; } stack = {altstack, sizeof altstack, 0};
#else
  struct { void *sp; int flags; unsigned long size; } stack = {altstack, 0, sizeof altstack};
#endif
  sys3(SYS_altstack, (long)&stack, 0, 0, 0);
  // SIGILL, SIGTRAP, SIGBUS, SIGFPE, SIGSEGV on the targets but MIPS, where SIGBUS is 10
  install(4); install(5); install(7); install(8); install(10); install(11);
  unsigned long long header[8] = {0xd1ff7e57, (unsigned long)slot, (unsigned long)taken, (unsigned long)window, WINDOW,
                                  STATE, sizeof(WORD), 0};
  write_all((unsigned char *)header, sizeof header);
  for (;;) {
    long size = SLOT + STATE + WINDOW;
    if (read_all(buffer, size) != size)
      sys3(SYS_exit, 0, 0, 0, 0);
    // the same instruction stays, as under qemu-user a write to the code retranslates it
    for (int i = 0; i < SLOT; i++)
      if (slot[i] != buffer[i]) {
        copy(slot, buffer, SLOT);
        break;
      }
    copy(st_in, buffer + SLOT, STATE);
    copy(window, buffer + SLOT + STATE, WINDOW);
    for (unsigned long i = 0; i < STATE; i++)
      ((volatile unsigned char *)st_out)[i] = 0;
    marker = 0;
    enter();
    // the marker, then what it ended with
    copy(buffer, (unsigned char *)&marker, 8);
    copy(buffer + 8, st_out, STATE);
    copy(buffer + 8 + STATE, window, WINDOW);
    write_all(buffer, 8 + STATE + WINDOW);
  }
}

#if defined(__x86_64__)
__asm__(R"ASM(
  .text
  .globl _start
_start:
  and $-16, %rsp
  call cmain
  .globl enter, recover
enter:
  push %rbx; push %rbp; push %r12; push %r13; push %r14; push %r15
  mov %rsp, host_sp
  mov $st_in+128, %rsp
  popfq
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
  vmovdqu st_in+136+32*\r, %ymm\r
  .endr
  .irp r,0,1,2,3,4,5,6,7
  movq st_in+648+8*\r, %mm\r
  .endr
  mov st_in+0, %rax; mov st_in+8, %rcx; mov st_in+16, %rdx; mov st_in+24, %rbx
  mov st_in+32, %rsp; mov st_in+40, %rbp; mov st_in+48, %rsi; mov st_in+56, %rdi
  .irp r,8,9,10,11,12,13,14,15
  mov st_in+8*\r, %r\r
  .endr
  jmp slot
  .macro SAVE
  mov %rax, st_out+0; mov %rcx, st_out+8; mov %rdx, st_out+16; mov %rbx, st_out+24
  mov %rsp, st_out+32; mov %rbp, st_out+40; mov %rsi, st_out+48; mov %rdi, st_out+56
  .irp r,8,9,10,11,12,13,14,15
  mov %r\r, st_out+8*\r
  .endr
  mov $st_out+136, %rsp
  pushfq
  cld
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
  vmovdqu %ymm\r, st_out+136+32*\r
  .endr
  .irp r,0,1,2,3,4,5,6,7
  movq %mm\r, st_out+648+8*\r
  .endr
  emms
  .endm
fall_save:
  SAVE
  movq $0, marker
  jmp recover
taken_save:
  SAVE
  movq $1, marker
recover:
  cld
  mov host_sp, %rsp
  pop %r15; pop %r14; pop %r13; pop %r12; pop %rbp; pop %rbx
  ret
  .balign 4096
  .globl slot, taken
slot:
  .fill 32, 1, 0x90
  jmp fall_save
  .balign 64
taken:
  jmp taken_save
  .balign 4096
)ASM");
#elif defined(__i386__)
__asm__(R"ASM(
  .text
  .globl _start
_start:
  and $-16, %esp
  call cmain
  .globl enter, recover
enter:
  push %ebx; push %ebp; push %esi; push %edi
  mov %esp, host_sp
  mov $st_in+32, %esp
  popfl
  .irp r,0,1,2,3,4,5,6,7
  vmovdqu st_in+36+32*\r, %ymm\r
  .endr
  .irp r,0,1,2,3,4,5,6,7
  movq st_in+292+8*\r, %mm\r
  .endr
  mov st_in+0, %eax; mov st_in+4, %ecx; mov st_in+8, %edx; mov st_in+12, %ebx
  mov st_in+16, %esp; mov st_in+20, %ebp; mov st_in+24, %esi; mov st_in+28, %edi
  jmp slot
  .macro SAVE
  mov %eax, st_out+0; mov %ecx, st_out+4; mov %edx, st_out+8; mov %ebx, st_out+12
  mov %esp, st_out+16; mov %ebp, st_out+20; mov %esi, st_out+24; mov %edi, st_out+28
  mov $st_out+36, %esp
  pushfl
  cld
  .irp r,0,1,2,3,4,5,6,7
  vmovdqu %ymm\r, st_out+36+32*\r
  .endr
  .irp r,0,1,2,3,4,5,6,7
  movq %mm\r, st_out+292+8*\r
  .endr
  emms
  .endm
fall_save:
  SAVE
  movl $0, marker
  movl $0, marker+4
  jmp recover
taken_save:
  SAVE
  movl $1, marker
  movl $0, marker+4
recover:
  cld
  mov host_sp, %esp
  pop %edi; pop %esi; pop %ebp; pop %ebx
  ret
  .balign 4096
  .globl slot, taken
slot:
  .fill 32, 1, 0x90
  jmp fall_save
  .balign 64
taken:
  jmp taken_save
  .balign 4096
)ASM");
#elif defined(__aarch64__)
__asm__(R"ASM(
  .arch_extension sve
  .text
  .globl _start
_start:
  mov x0, sp
  and x0, x0, #-16
  mov sp, x0
  bl cmain
  .globl enter, recover
enter:
  stp x19, x20, [sp, #-96]!
  stp x21, x22, [sp, #16]
  stp x23, x24, [sp, #32]
  stp x25, x26, [sp, #48]
  stp x27, x28, [sp, #64]
  stp x29, x30, [sp, #80]
  adrp x0, host_sp
  add x0, x0, :lo12:host_sp
  mov x1, sp
  str x1, [x0]
  adrp x30, st_in
  add x30, x30, :lo12:st_in
  add x0, x30, #272
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
  ldr q\r, [x0], #16
  .endr
  add x1, x0, #32
  ldr p0, [x1]
  wrffr p0.b
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
  ldr p\r, [x0]
  add x0, x0, #2
  .endr
  ldr x0, [x30, #256]
  msr nzcv, x0
  ldr x0, [x30, #248]
  mov sp, x0
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29
  ldr x\r, [x30, #8*\r]
  .endr
  ldr x30, [x30, #240]
  b slot
  .macro SAVE
  msr tpidr_el0, x30
  adrp x30, st_out
  add x30, x30, :lo12:st_out
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29
  str x\r, [x30, #8*\r]
  .endr
  mrs x0, tpidr_el0
  str x0, [x30, #240]
  mov x0, sp
  str x0, [x30, #248]
  mrs x0, nzcv
  str x0, [x30, #256]
  add x0, x30, #272
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31
  str q\r, [x0], #16
  .endr
  .irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
  str p\r, [x0]
  add x0, x0, #2
  .endr
  rdffr p0.b
  str p0, [x0]
  .endm
fall_save:
  SAVE
  mov x1, #0
  b done
taken_save:
  SAVE
  mov x1, #1
done:
  adrp x0, marker
  add x0, x0, :lo12:marker
  str x1, [x0]
recover:
  adrp x0, host_sp
  add x0, x0, :lo12:host_sp
  ldr x1, [x0]
  mov sp, x1
  ldp x21, x22, [sp, #16]
  ldp x23, x24, [sp, #32]
  ldp x25, x26, [sp, #48]
  ldp x27, x28, [sp, #64]
  ldp x29, x30, [sp, #80]
  ldp x19, x20, [sp], #96
  ret
  .balign 4096
  .globl slot, taken
slot:
  .fill 8, 4, 0xd503201f
  b fall_save
  .balign 64
taken:
  b taken_save
  .balign 4096
)ASM");
#elif defined(__arm__)
#ifdef __thumb__
#define ARM_PRELUDE ".macro MODE\n.thumb\n.endm\n.macro FUNC\n.thumb_func\n.endm\n"
#else
#define ARM_PRELUDE ".macro MODE\n.arm\n.endm\n.macro FUNC\n.endm\n"
#endif
__asm__(ARM_PRELUDE R"ASM(
  .text
  .syntax unified
  .arch armv7-a
  .fpu neon-vfpv4
  MODE
  .globl _start
  FUNC
_start:
  mov r0, sp
  bic r0, r0, #7
  mov sp, r0
  bl cmain
  .globl enter, recover
  FUNC
enter:
  push {r4-r11, lr}
  ldr r0, =host_sp
  str sp, [r0]
  ldr r12, =st_in
  add r0, r12, #72
  vldm r0!, {d0-d15}
  vldm r0, {d16-d31}
  ldr r0, [r12, #64]
  msr apsr_nzcvqg, r0
  ldm r12, {r0-r11}
  ldr sp, [r12, #52]
  ldr lr, [r12, #56]
  ldr r12, [r12, #48]
  b.w slot
  .ltorg
  .macro SAVE
  mcr p15, 0, r12, c13, c0, 2
  ldr r12, =st_out
  stm r12, {r0-r11}
  mrc p15, 0, r0, c13, c0, 2
  str r0, [r12, #48]
  str sp, [r12, #52]
  str lr, [r12, #56]
  mrs r0, apsr
  str r0, [r12, #64]
  add r0, r12, #72
  vstm r0!, {d0-d15}
  vstm r0, {d16-d31}
  .endm
  FUNC
fall_save:
  SAVE
  mov r1, #0
  b.w done
  .ltorg
  FUNC
taken_save:
  SAVE
  mov r1, #1
  b.w done
  .ltorg
  FUNC
done:
  ldr r0, =marker
  str r1, [r0]
  FUNC
recover:
  ldr r0, =host_sp
  ldr sp, [r0]
  pop {r4-r11, pc}
  .ltorg
  .balign 4096
  .globl slot, taken
slot:
  .fill 32, 1, 0
  b.w fall_save
  .balign 64
taken:
  b.w taken_save
  .balign 4096
)ASM");
#elif defined(__riscv)
#if __riscv_xlen == 64
#define L "ld"
#define S "sd"
#define MOVETO "fmv.d.x"
#define MOVEFROM "fmv.x.d"
#define W "8"
#else
#define L "lw"
#define S "sw"
#define MOVETO "fmv.w.x"
#define MOVEFROM "fmv.x.w"
#define W "4"
#endif
__asm__(".macro FLOAD a, b\n fld \\a, \\b\n.endm\n.macro FSTORE a, b\n fsd \\a, \\b\n.endm\n.text\n.option push\n.option norelax\n.option norvc\n"
  ".globl _start\n_start:\n andi sp, sp, -16\n call cmain\n"
  ".globl enter, recover\nenter:\n addi sp, sp, -208\n"
  ".irp r,1,8,9,18,19,20,21,22,23,24,25,26,27\n " S " x\\r, " W "*\\r(sp)\n.endr\n"
  " lla t0, host_sp\n " S " sp, 0(t0)\n lla x1, st_in\n addi x2, x1, 32*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30\n FLOAD f\\r, 8*\\r(x2)\n.endr\n"
  ".irp r,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " L " x\\r, " W "*\\r(x1)\n.endr\n"
  " " L " x1, " W "(x1)\n j slot\n"
  ".macro SAVE\n " MOVETO " f31, x1\n lla x1, st_out\n"
  ".irp r,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " S " x\\r, " W "*\\r(x1)\n.endr\n"
  " " MOVEFROM " x2, f31\n " S " x2, " W "(x1)\n addi x2, x1, 32*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30\n FSTORE f\\r, 8*\\r(x2)\n.endr\n.endm\n"
  "fall_save:\n SAVE\n li t1, 0\n j done\n"
  "taken_save:\n SAVE\n li t1, 1\n"
  "done:\n lla t0, marker\n sw t1, 0(t0)\n sw x0, 4(t0)\n"
  "recover:\n lla t0, host_sp\n " L " sp, 0(t0)\n"
  ".irp r,1,8,9,18,19,20,21,22,23,24,25,26,27\n " L " x\\r, " W "*\\r(sp)\n.endr\n"
  " addi sp, sp, 208\n ret\n"
  ".balign 4096\n.globl slot, taken\nslot:\n .fill 8, 4, 0x13\n j fall_save\n.balign 64\ntaken:\n j taken_save\n.balign 4096\n"
  ".option pop\n");
#elif defined(__mips__)
#if _MIPS_SIM == _ABIO32
#define L "lw"
#define S "sw"
#define MOVETO "mtc1"
#define MOVEFROM "mfc1"
#define W "4"
#define FL "lwc1"
#define FS "swc1"
#define ADDSP "addiu"
#define MIPSSET ".set mips32r2\n"
#else
#define L "ld"
#define S "sd"
#define MOVETO "dmtc1"
#define MOVEFROM "dmfc1"
#define W "8"
#define FL "ldc1"
#define FS "sdc1"
#define ADDSP "daddiu"
#define MIPSSET ".set mips64r2\n"
#endif
#if __mips_isa_rev >= 6
#undef FL
#undef FS
#define FL "ldc1"
#define FS "sdc1"
#define FW "8"
#else
#define FW W
#endif
#if __mips_isa_rev >= 6
#undef MIPSSET
#define MIPSSET
#define HILO_IN
#define HILO_OUT
#else
#define HILO_IN " " L " $2, 32*" W "($1)\n mthi $2\n " L " $2, 33*" W "($1)\n mtlo $2\n"
#define HILO_OUT " mfhi $2\n " S " $2, 32*" W "($1)\n mflo $2\n " S " $2, 33*" W "($1)\n"
#endif
__asm__(".text\n.set noreorder\n.set noat\n.set hardfloat\n" MIPSSET
  ".globl _start\n.ent _start\n_start:\n li $2, -16\n and $29, $29, $2\n " ADDSP " $29, $29, -64\n"
  " lui $25, %hi(cmain)\n addiu $25, $25, %lo(cmain)\n jalr $25\n nop\n.end _start\n"
  ".globl enter, recover\n.ent enter\nenter:\n " ADDSP " $29, $29, -256\n"
  ".irp r,16,17,18,19,20,21,22,23,28,30,31\n " S " $\\r, " W "*\\r($29)\n.endr\n"
  " lui $1, %hi(host_sp)\n " S " $29, %lo(host_sp)($1)\n"
  " lui $1, %hi(st_in)\n addiu $1, $1, %lo(st_in)\n" HILO_IN " addiu $2, $1, 35*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30\n " FL " $f\\r, " FW "*\\r($2)\n.endr\n"
  " " L " $2, 34*" W "($1)\n ctc1 $2, $31\n"
  ".irp r,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " L " $\\r, " W "*\\r($1)\n.endr\n"
  " " L " $1, " W "($1)\n j slot\n nop\n"
  ".macro SAVE\n " MOVETO " $1, $f31\n lui $1, %hi(st_out)\n addiu $1, $1, %lo(st_out)\n"
  ".irp r,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " S " $\\r, " W "*\\r($1)\n.endr\n"
  " " MOVEFROM " $2, $f31\n " S " $2, " W "($1)\n" HILO_OUT " cfc1 $2, $31\n " S " $2, 34*" W "($1)\n addiu $2, $1, 35*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30\n " FS " $f\\r, " FW "*\\r($2)\n.endr\n.endm\n"
  "fall_save:\n SAVE\n li $3, 0\n j done\n nop\n"
  "taken_save:\n SAVE\n li $3, 1\n"
  "done:\n lui $2, %hi(marker)\n addiu $2, $2, %lo(marker)\n sw $0, 0($2)\n sw $0, 4($2)\n"
#ifdef __MIPSEB__
  " sw $3, 4($2)\n"
#else
  " sw $3, 0($2)\n"
#endif
  "recover:\n lui $1, %hi(host_sp)\n " L " $29, %lo(host_sp)($1)\n"
  ".irp r,16,17,18,19,20,21,22,23,28,30,31\n " L " $\\r, " W "*\\r($29)\n.endr\n"
  " jr $31\n " ADDSP " $29, $29, 256\n.end enter\n"
  ".balign 4096\n.globl slot, taken\nslot:\n .fill 8, 4, 0\n j fall_save\n nop\n.balign 64\ntaken:\n j taken_save\n nop\n.balign 4096\n"
  ".set at\n.set reorder\n");
#elif defined(__powerpc__)
#if defined(__powerpc64__)
#define L "ld"
#define S "std"
#define W "8"
#define HOLD "815"
#define START_ALIGN " rldicr 1, 1, 0, 59\n stdu 1, -64(1)\n"
#define PUSH " stdu 1, -512(1)\n"
#define START_TOC " lis 2, .TOC.@ha\n addi 2, 2, .TOC.@l\n"
#else
#define L "lwz"
#define S "stw"
#define W "4"
#define HOLD "256"
#define START_ALIGN " clrrwi 1, 1, 4\n stwu 1, -64(1)\n"
#define PUSH " stwu 1, -512(1)\n"
#define START_TOC
#endif
__asm__(".machine altivec\n.text\n.globl _start\n_start:\n" START_TOC START_ALIGN " bl cmain\n"
  ".globl enter, recover\nenter:\n" PUSH " mflr 0\n " S " 0, 8*" W "(1)\n mfcr 0\n " S " 0, 9*" W "(1)\n " S " 2, 10*" W "(1)\n"
  ".irp r,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " S " \\r, " W "*\\r(1)\n.endr\n"
  " lis 3, host_sp@ha\n " S " 1, host_sp@l(3)\n"
  " lis 3, st_in@ha\n addi 3, 3, st_in@l\n"
  " addi 4, 3, 36*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n lfd \\r, 8*\\r(4)\n.endr\n"
  " addi 4, 4, 256\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n li 5, 16*\\r\n lvx \\r, 4, 5\n.endr\n"
  " " L " 0, 32*" W "(3)\n mtcrf 255, 0\n " L " 0, 33*" W "(3)\n mtxer 0\n " L " 0, 34*" W "(3)\n mtlr 0\n " L " 0, 35*" W "(3)\n mtctr 0\n"
  " " L " 0, 0(3)\n"
  ".irp r,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " L " \\r, " W "*\\r(3)\n.endr\n"
  " " L " 3, 3*" W "(3)\n b slot\n"
  ".macro SAVE\n mtspr " HOLD ", 3\n lis 3, st_out@ha\n addi 3, 3, st_out@l\n"
  ".irp r,0,1,2,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " S " \\r, " W "*\\r(3)\n.endr\n"
  " mfspr 0, " HOLD "\n " S " 0, 3*" W "(3)\n mfcr 0\n " S " 0, 32*" W "(3)\n mfxer 0\n " S " 0, 33*" W "(3)\n mflr 0\n " S " 0, 34*" W "(3)\n mfctr 0\n " S " 0, 35*" W "(3)\n addi 4, 3, 36*" W "\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n stfd \\r, 8*\\r(4)\n.endr\n"
  " addi 4, 4, 256\n"
  ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n li 5, 16*\\r\n stvx \\r, 4, 5\n.endr\n.endm\n"
  "fall_save:\n SAVE\n li 4, 0\n b done\n"
  "taken_save:\n SAVE\n li 4, 1\n"
  "done:\n lis 3, marker@ha\n addi 3, 3, marker@l\n li 0, 0\n stw 0, 0(3)\n stw 0, 4(3)\n"
#ifdef __BIG_ENDIAN__
  " stw 4, 4(3)\n"
#else
  " stw 4, 0(3)\n"
#endif
  "recover:\n lis 3, host_sp@ha\n " L " 1, host_sp@l(3)\n"
  " " L " 0, 8*" W "(1)\n mtlr 0\n " L " 0, 9*" W "(1)\n mtcrf 255, 0\n " L " 2, 10*" W "(1)\n"
  ".irp r,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31\n " L " \\r, " W "*\\r(1)\n.endr\n"
  " addi 1, 1, 512\n blr\n"
  ".balign 4096\n.globl slot, taken\nslot:\n .fill 8, 4, 0x60000000\n b fall_save\n.balign 64\ntaken:\n b taken_save\n.balign 4096\n");
#endif
