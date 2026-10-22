/* The odd cases of the backward slice on ARM, in A32 and in Thumb,
   each of which returns its result in r0, at the label, that ends with
   _ret, so that the slice of R0 there is known, see emu/arm-slice. The
   labels are functions, so that they are symbols of the emulator. The
   binary links the stand-in libc of stub-libc.c, see thumb-crc-loop.c,
   whose memcpy Primus replaces with its stub:

   T="--target=armv7a-linux-gnueabihf -fuse-ld=lld -nostdlib -O0 \
      -fno-builtin -fno-unwind-tables -fno-exceptions \
      -fno-asynchronous-unwind-tables"
   clang $T -marm -fno-pie -no-pie \
     -Wl,--dynamic-linker=/lib/ld-linux-armhf.so.3 \
     arm-slice-weird.c libc.so.6 -o ../bin/arm-linux-gnueabihf-slice-weird */

#define CASE(mode, name, body)                                                 \
    __asm__(".text\n." #mode "\n.globl " #name "\n.type " #name           \
            ", %function\n.globl " #name "_ret\n.type " #name                 \
            "_ret, %function\n" #name ":\n" body "\n" #name "_ret:\nbx lr\n"); \
    int name(int, int, int, int);

/* the move doesn't happen, so r0 keeps r1, and depends on the flags */
CASE(arm, a_cond_no, "mov r0, r1\n cmp r2, r2\n movne r0, r3")
/* the move happens */
CASE(arm, a_cond_yes, "mov r0, r1\n cmp r2, r3\n movne r0, r3")
/* the registers go through the stack, crossed */
CASE(arm, a_ldm, "push {r1, r2}\n pop {r0, r3}")
/* the constant of the literal pool, which the pc addresses */
CASE(arm, a_pool, "ldr r0, =0x12345678\n b 1f\n .ltorg\n 1:")
/* the shifted operand */
CASE(arm, a_shift, "add r0, r1, r2, lsl #2")
/* the high word of the product, not the low one */
CASE(arm, a_umull, "umull r3, r0, r1, r2")
/* the byte overwrites the second byte of the word */
CASE(arm, a_bytes, "sub sp, sp, #8\n str r1, [sp]\n strb r2, [sp, #1]\n"
                   " ldr r0, [sp]\n add sp, sp, #8")
/* the exclusive store, that succeeds, and its status */
CASE(arm, a_strex, "sub sp, sp, #8\n str r1, [sp]\n mov r12, sp\n"
                   " ldrex r3, [r12]\n strex r0, r2, [r12]\n ldr r0, [sp]\n"
                   " add sp, sp, #8")
/* the return address is a constant */
CASE(arm, a_link, "push {lr}\n bl 1f\n 1: mov r0, lr\n pop {lr}")
/* the flags of the carry go to the sum */
CASE(arm, a_carry, "adds r3, r1, r2\n adc r0, r3, #0")
/* the if-then-else of Thumb */
CASE(thumb, t_ite, "cmp r1, r2\n ite eq\n moveq r0, r3\n movne r0, r1")
/* the Thumb code, that the A32 code calls, and returns to it */
CASE(thumb, t_add, "adds r0, r1, r2")
CASE(arm, a_interwork, "push {lr}\n blx t_add\n pop {lr}")
/* the loop of Thumb */
CASE(thumb, t_loop, "movs r0, #0\n movs r3, #5\n 1: adds r0, r0, r1\n"
                    " subs r3, r3, #1\n bne 1b")
/* the Thumb code reads the stack by its pc relative pool too */
CASE(thumb, t_pool, "ldr r0, 2f\n add r0, r0, r1\n b 1f\n .align 2\n"
                    " 2: .word 0x1234\n 1:")

/* the single registers of VFP are the halves of the double ones */
CASE(arm, a_vfp, "vmov s0, r1\n vmov s1, r2\n vmov r0, r3, d0")
/* the double word goes through the stack, its high word */
CASE(arm, a_ldrd, "sub sp, sp, #8\n strd r2, r3, [sp]\n ldrd r0, r1, [sp]\n"
                  " mov r0, r1\n add sp, sp, #8")
/* the frame saves many registers, of which one comes back to r0 */
CASE(arm, a_frame, "push {r1, r2, r3, r4, r5, lr}\n ldr r0, [sp, #8]\n"
                   " pop {r1, r2, r3, r4, r5, lr}")
/* the load doesn't happen, so r0 keeps r1 */
CASE(arm, a_ldrne, "push {r2}\n mov r0, r1\n cmp r1, r1\n ldrne r0, [sp]\n"
                   " add sp, sp, #4")
/* the load updates its base, which is the result */
CASE(arm, a_wback, "push {r1, r2}\n mov r3, sp\n ldr r1, [r3, #4]!\n"
                   " mov r0, r3\n add sp, sp, #8")
/* the flags go to the register */
CASE(arm, a_mrs, "cmp r1, r2\n mrs r0, apsr")
/* the frame of Thumb */
CASE(thumb, t_frame, "push {r1, r2, r4, lr}\n ldr r0, [sp, #4]\n"
                     " pop {r1, r2, r4, lr}")
/* the hook writes r0 at the label, see emu/arm-slice */
CASE(arm, a_hooked, "mov r0, r1\n .globl a_hooked_at\n"
                    " .type a_hooked_at, %function\n a_hooked_at: nop\n"
                    " add r0, r0, r2")
/* through memcpy, which Primus runs, so the slice has a gap */
void *memcpy(void *, const void *, unsigned);
int copied(int x) {
    int src[2] = {x, x + 1}, dst[2];
    volatile unsigned n = sizeof(src);
    memcpy(dst, src, n);
    return dst[1];
}
CASE(arm, a_copied, "push {lr}\n mov r0, r1\n bl copied\n pop {lr}")

int sink;

int main(int argc, char **argv) {
    int a = argc, b = argc + 1, c = argc + 2, d = argc + 3;
    sink += a_cond_no(a, b, c, d);
    sink += a_cond_yes(a, b, c, d);
    sink += a_ldm(a, b, c, d);
    sink += a_pool(a, b, c, d);
    sink += a_shift(a, b, c, d);
    sink += a_umull(a, b, c, d);
    sink += a_bytes(a, b, c, d);
    sink += a_strex(a, b, c, d);
    sink += a_link(a, b, c, d);
    sink += a_carry(a, b, c, d);
    sink += t_ite(a, b, c, d);
    sink += a_interwork(a, b, c, d);
    sink += t_loop(a, b, c, d);
    sink += t_pool(a, b, c, d);
    sink += a_vfp(a, b, c, d);
    sink += a_ldrd(a, b, c, d);
    sink += a_frame(a, b, c, d);
    sink += a_ldrne(a, b, c, d);
    sink += a_wback(a, b, c, d);
    sink += a_mrs(a, b, c, d);
    sink += t_frame(a, b, c, d);
    sink += a_hooked(a, b, c, d);
    sink += a_copied(a, b, c, d);
    return sink & 0x7f;
}

int __libc_start_main(int (*)(int, char **, char **), int, char **,
                      void (*)(void), void (*)(void), void (*)(void), void *);

void _start(void) { __libc_start_main((void *)main, 3, 0, 0, 0, 0, 0); }
