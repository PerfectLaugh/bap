/* SME and SME2 as Linux has them for a program, which prints what it finds, as qemu does, see testsuite/data/aarch64-sme.out:
   outer products and moves of ZA, a system call in the streaming mode, which leaves it with ZA kept, and a fault in the streaming
   mode with ZA on, whose handler has neither and TPIDR2_EL0 zero, and which all come back as it returns. A call out of the
   streaming mode leaves P1 zero, as Linux's sve_user_discard does, which qemu-user doesn't, so that the line of it in the .out is
   Linux's, 0, where qemu prints ffff.

   clang --target=aarch64-linux-gnu -fuse-ld=lld -static -nostdlib -ffreestanding -fno-builtin -O1 -fno-pic -march=armv8-a \
     -Wl,-e,_start aarch64-sme.c -o ../bin/aarch64-linux-none-sme
   qemu-aarch64 -cpu max,sve-max-vq=1 ../bin/aarch64-linux-none-sme \
     | sed 's/^p1 after a call .*/p1 after a call 0000000000000000/' > ../data/aarch64-sme.out */

typedef unsigned long u64;

static long sys(long n, long a, long b, long c, long d) {
  register long x8 __asm__("x8") = n;
  register long x0 __asm__("x0") = a;
  register long x1 __asm__("x1") = b;
  register long x2 __asm__("x2") = c;
  register long x3 __asm__("x3") = d;
  __asm__ volatile("svc 0" : "+r"(x0) : "r"(x8), "r"(x1), "r"(x2), "r"(x3) : "memory");
  return x0;
}

static void put(const char *s) {
  long n = 0;
  while (s[n]) n++;
  sys(64, 1, (long)s, n, 0);
}

static void hex(const char *name, u64 x) {
  char line[64];
  int i = 0;
  while (*name) line[i++] = *name++;
  line[i++] = ' ';
  for (int s = 60; s >= 0; s -= 4) line[i++] = "0123456789abcdef"[(x >> s) & 15];
  line[i++] = '\n';
  line[i] = 0;
  put(line);
}

static u64 mix(const u64 *p, int n) {
  u64 h = 0xcbf29ce484222325;
  for (int i = 0; i < n; i++) h = (h ^ p[i]) * 0x100000001b3;
  return h;
}

static u64 inputs[16] = {0x3f8000004000c000, 0x4040000040800000, 0x0102030405060708, 0xf1f2f3f4f5f6f7f8,
                         0x0011223344556677, 0x8899aabbccddeeff, 0x3c003c0040004200, 0xbc00c0004400c400,
                         0x7fff80000001ffff, 0x0000000100000002, 0x0123456789abcdef, 0xfedcba9876543210,
                         0x4049000040490000, 0xc0490000c0490000, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa};
static u64 table[8] = {0x1111111122222222, 0x3333333344444444, 0x5555555566666666, 0x7777777788888888,
                       0x99999999aaaaaaaa, 0xbbbbbbbbcccccccc, 0xddddddddeeeeeeee, 0xffffffff00000000};
static u64 za[32], out[32], svcr_after_call, svcr_in_handler, tpidr2_in_handler, svcr_after_handler, tpidr2_after_handler;
static u64 z0_after_handler[2], za_after_handler[2];

static void products(void) {
  __asm__ volatile(
      ".arch_extension sme2\n"
      "smstart\n"
      "ptrue p0.b\n"
      "ldr z0, [%[in]]\n"
      "ldr z1, [%[in], #1, mul vl]\n"
      "ldr z2, [%[in], #2, mul vl]\n"
      "ldr z3, [%[in], #3, mul vl]\n"
      "ldr z4, [%[in], #4, mul vl]\n"
      "ldr z5, [%[in], #5, mul vl]\n"
      "ldr z6, [%[in], #6, mul vl]\n"
      "ldr z7, [%[in], #7, mul vl]\n"
      "ldr zt0, [%[table]]\n"
      "zero {za}\n"
      "fmopa za0.s, p0/m, p0/m, z0.s, z1.s\n"
      "smopa za1.s, p0/m, p0/m, z2.b, z3.b\n"
      "umops za2.s, p0/m, p0/m, z4.b, z5.b\n"
      "fmopa za3.s, p0/m, p0/m, z6.h, z7.h\n"
      "mov w12, #1\n"
      "mov w9, #1\n"
      "addha za1.s, p0/m, p0/m, z2.s\n"
      "mov za2v.s[w12, 2], p0/m, z3.s\n"
      "sdot za.s[w9, 0, vgx2], {z2.b, z3.b}, z4.b\n"
      "fmla za.s[w9, 4, vgx2], {z0.s, z1.s}, z6.s[1]\n"
      "smlall za.s[w9, 4:7], z2.b, z5.b\n"
      "mov w13, #0\n"
      ".irp r,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15\n"
      "str za[w13, \\r], [%[za], #\\r, mul vl]\n"
      ".endr\n"
      "luti4 {z8.h - z9.h}, zt0, z2[0]\n"
      "mov {z10.s, z11.s}, za1h.s[w12, 2:3]\n"
      "sclamp {z12.b, z13.b}, z4.b, z5.b\n"
      "sqcvtn z14.h, {z2.s, z3.s}\n"
      "whilelo {p2.s, p3.s}, xzr, %[n]\n"
      "uzp {z16.s - z19.s}, {z0.s - z3.s}\n"
      "str z8, [%[out]]\n"
      "str z9, [%[out], #1, mul vl]\n"
      "str z10, [%[out], #2, mul vl]\n"
      "str z11, [%[out], #3, mul vl]\n"
      "str z12, [%[out], #4, mul vl]\n"
      "str z13, [%[out], #5, mul vl]\n"
      "str z14, [%[out], #6, mul vl]\n"
      "str p2, [%[out], #56, mul vl]\n"
      "str p3, [%[out], #57, mul vl]\n"
      "str z16, [%[out], #8, mul vl]\n"
      "str z17, [%[out], #9, mul vl]\n"
      "str z18, [%[out], #10, mul vl]\n"
      "str z19, [%[out], #11, mul vl]\n"
      // a call, which leaves the streaming mode and keeps ZA
      "mov x8, #172\n"
      "svc 0\n"
      "mrs x0, svcr\n"
      "str x0, [%[call]]\n"
      "smstop\n"
      :
      : [in] "r"(inputs), [table] "r"(table), [za] "r"(za), [out] "r"(out), [n] "r"(5L), [call] "r"(&svcr_after_call)
      : "x0", "x8", "x9", "x12", "x13", "memory", "cc");
}

static u64 p1_after_call;

static void discard(void) {
  // a call out of the streaming mode, after which the predicates are zeros
  __asm__ volatile(
      ".arch_extension sve\n"
      "ptrue p1.b\n"
      "mov x8, #172\n"
      "svc 0\n"
      "str p1, [%[p]]\n"
      :
      : [p] "r"(&p1_after_call)
      : "x0", "x8", "p1", "memory");
}

static void handler(int signal, void *info, void *context) {
  (void)signal;
  (void)info;
  u64 x;
  __asm__ volatile(".arch_extension sme2\nmrs %0, svcr" : "=r"(x));
  svcr_in_handler = x;
  __asm__ volatile(".arch_extension sme2\nmrs %0, tpidr2_el0" : "=r"(x));
  tpidr2_in_handler = x;
  // past the instruction that faulted
  *(u64 *)((char *)context + 440) += 4;
}

static void fault(void) {
  __asm__ volatile(
      ".arch_extension sme2\n"
      "smstart\n"
      "mov x0, #5\n"
      "msr tpidr2_el0, x0\n"
      "ldr z0, [%[in]]\n"
      "ldr z1, [%[in], #1, mul vl]\n"
      "mov w9, #3\n"
      "mov za.d[w9, 0, vgx2], {z0.d, z1.d}\n"
      "udf #1\n"
      "mrs x0, svcr\n"
      "str x0, [%[svcr]]\n"
      "mrs x0, tpidr2_el0\n"
      "str x0, [%[tpidr2]]\n"
      "str z0, [%[z0]]\n"
      "mov {z2.d, z3.d}, za.d[w9, 0, vgx2]\n"
      "str z3, [%[za]]\n"
      "smstop\n"
      :
      : [in] "r"(inputs + 4), [svcr] "r"(&svcr_after_handler), [tpidr2] "r"(&tpidr2_after_handler), [z0] "r"(z0_after_handler),
        [za] "r"(za_after_handler)
      : "x0", "x9", "memory", "cc");
}

void cmain(void) {
  // PR_SME_SET_VL: a streaming vector of 128 bits, which is what the machine has
  sys(167, 63, 16, 0, 0);
  products();
  hex("za", mix(za, 32));
  for (int i = 0; i < 12; i++) hex("z", out[2 * i] ^ out[2 * i + 1]);
  hex("p", out[14] & 0xffffffff);
  hex("svcr after a call", svcr_after_call);
  discard();
  hex("p1 after a call", p1_after_call & 0xffff);
  struct {
    void *handler;
    u64 flags;
    void *restorer;
    u64 mask;
  } action = {(void *)handler, 0x4 /* SA_SIGINFO */, 0, 0};
  sys(134, 4, (long)&action, 0, 8);
  fault();
  hex("svcr in the handler", svcr_in_handler);
  hex("tpidr2 in the handler", tpidr2_in_handler);
  hex("svcr after it", svcr_after_handler);
  hex("tpidr2 after it", tpidr2_after_handler);
  hex("z0 after it", z0_after_handler[0] ^ z0_after_handler[1]);
  hex("za after it", za_after_handler[0] ^ za_after_handler[1]);
  sys(93, 0, 0, 0, 0);
}

__asm__(".globl _start\n_start:\n mov x0, sp\n and x0, x0, #-16\n mov sp, x0\n bl cmain\n");
