/* The odd cases of the backward slice, each of which returns its
   result in RAX, at the label, that ends with _ret, so that the slice
   of RAX there is known, see emu/slice. The labels are functions, so
   that they are symbols of the emulator:

   gcc -O0 -no-pie -fcf-protection=none slice-weird.c -o ../bin/x86_64-linux-gnu-slice-weird */

#include <string.h>

#define CASE(name, body)                                                       \
    __asm__(".text\n.globl " #name "\n.type " #name ", @function\n"          \
            ".globl " #name "_ret\n.type " #name "_ret, @function\n" #name    \
            ":\n" body "\n" #name "_ret:\nret\n");                            \
    long name(long, long, long, long);

__asm__(".intel_syntax noprefix");

/* the result doesn't depend on rdi, which is zeroed by the idiom */
CASE(s_zero, "mov rax, rdi\n xor eax, eax\n add rax, rsi")
/* the upper bytes come from rdi, the lowest from rsi */
CASE(s_partial, "mov rax, rdi\n mov al, sil")
/* the 32-bit move zeroes the upper half */
CASE(s_kill32, "mov rax, rsi\n mov eax, edi")
/* the byte overwrites the second byte of the word */
CASE(s_bytes, "sub rsp, 16\n mov [rsp], rdi\n mov [rsp+1], sil\n"
              " mov rax, [rsp]\n add rsp, 16")
/* the word overwrites the byte */
CASE(s_bytekill, "sub rsp, 16\n mov [rsp+1], sil\n mov [rsp], rdi\n"
                 " mov rax, [rsp]\n add rsp, 16")
/* the bytes 1..2 come from both of the stores */
CASE(s_overlap, "sub rsp, 16\n mov [rsp], edi\n mov [rsp+2], esi\n"
                " movzx eax, word ptr [rsp+1]\n add rsp, 16")
/* the move doesn't happen, so rax keeps rdi */
CASE(s_cmov_no, "mov rax, rdi\n cmp rsi, rsi\n cmovne rax, rcx")
/* the move happens */
CASE(s_cmov_yes, "mov rax, rdi\n cmp rsi, rdx\n cmovne rax, rcx")
/* the stack slot is swapped, so the push doesn't flow */
CASE(s_xchg, "push rdi\n xchg [rsp], rsi\n pop rax")
/* the bytes are copied by each of the iterations */
CASE(s_rep, "sub rsp, 32\n mov [rsp], rdi\n lea rsi, [rsp]\n"
            " lea rdi, [rsp+16]\n mov ecx, 8\n rep movsb\n"
            " mov rax, [rsp+16]\n add rsp, 32")
/* the flags go through the stack */
CASE(s_pushf, "cmp rdi, rsi\n pushfq\n pop rax")
/* the return address is the data, a constant */
CASE(s_callpop, "call 1f\n 1: pop rax")
/* through the vector registers */
CASE(s_sse, "movq xmm0, rdi\n paddq xmm0, xmm0\n movq rax, xmm0")
/* the quotient depends on rdx:rax, and the divisor */
CASE(s_div, "mov rax, rdi\n xor edx, edx\n mov rcx, rsi\n div rcx")
/* the flag goes to the lowest byte */
CASE(s_setcc, "xor eax, eax\n cmp rdi, rsi\n setl al")
/* the memory goes through the stack by the push of the memory */
CASE(s_pushmem, "sub rsp, 16\n mov [rsp], rdi\n push qword ptr [rsp]\n"
                " pop rax\n add rsp, 16")
/* each of the iterations adds rdi */
CASE(s_loop, "xor eax, eax\n mov ecx, 5\n 1: add rax, rdi\n dec ecx\n jnz 1b")
/* the stored value is rsi, as the slot is rax */
CASE(s_cmpxchg, "sub rsp, 16\n mov [rsp], rdi\n mov rax, rdi\n"
                " lock cmpxchg [rsp], rsi\n mov rax, [rsp]\n add rsp, 16")
/* the exchange fails, so the slot keeps rdi */
CASE(s_cmpxchg_fail, "sub rsp, 16\n mov [rsp], rdi\n mov rax, rsi\n"
                     " lock cmpxchg [rsp], rdx\n mov rax, [rsp]\n add rsp, 16")
/* the hook writes rax at the label, see emu/slice */
CASE(s_hooked, "mov rax, rdi\n .globl s_hooked_at\n .type s_hooked_at, @function\n s_hooked_at: nop\n add rax, rsi")
/* the script writes the memory between the runs, see emu/slice */
CASE(s_written, "sub rsp, 16\n mov [rsp], rdi\n .globl s_written_at\n"
                " .type s_written_at, @function\n s_written_at: mov rax, [rsp]\n add rsp, 16")

/* the code patches itself, from rdi to rsi, between the runs of the
   move, so the result is rdi + rsi, and the first run is of the old
   bytes */
__asm__(".section .wtext, \"awx\", @progbits\n"
        ".globl s_smc\n.type s_smc, @function\n"
        ".globl s_smc_ret\n.type s_smc_ret, @function\n"
        "s_smc: xor edx, edx\n 1: mov rcx, rdi\n test edx, edx\n jnz 2f\n"
        " mov rax, rcx\n mov byte ptr [rip + 1b + 2], 0xf1\n inc edx\n"
        " jmp 1b\n 2: add rax, rcx\n"
        "s_smc_ret: ret\n"
        ".text");
long s_smc(long, long, long, long);

__asm__(".att_syntax");

/* through the frames of the recursion */
long fact(long n) { return n <= 1 ? 1 : n * fact(n - 1); }

/* through memcpy, which Primus runs, so the slice has a gap */
long copied(long x) {
    long src[2] = {x, x + 1}, dst[2];
    volatile size_t n = sizeof(src);
    memcpy(dst, src, n);
    return dst[1];
}

__asm__(".intel_syntax noprefix");
CASE(s_fact, "sub rsp, 8\n call fact\n add rsp, 8")
CASE(s_copied, "sub rsp, 8\n call copied\n add rsp, 8")
__asm__(".att_syntax");

long sink;

int main(int argc, char **argv) {
    long a = argc, b = argc + 1, c = argc + 2, d = argc + 3;
    sink += s_zero(a, b, c, d);
    sink += s_partial(a, b, c, d);
    sink += s_kill32(a, b, c, d);
    sink += s_bytes(a, b, c, d);
    sink += s_bytekill(a, b, c, d);
    sink += s_overlap(a, b, c, d);
    sink += s_cmov_no(a, b, c, d);
    sink += s_cmov_yes(a, b, c, d);
    sink += s_xchg(a, b, c, d);
    sink += s_rep(a, b, c, d);
    sink += s_pushf(a, b, c, d);
    sink += s_callpop(a, b, c, d);
    sink += s_sse(a, b, c, d);
    sink += s_div(a, b, c, d);
    sink += s_setcc(a, b, c, d);
    sink += s_pushmem(a, b, c, d);
    sink += s_loop(a, b, c, d);
    sink += s_cmpxchg(a, b, c, d);
    sink += s_cmpxchg_fail(a, b, c, d);
    sink += s_smc(a, b, c, d);
    sink += s_hooked(a, b, c, d);
    sink += s_written(a, b, c, d);
    sink += s_fact(a + 3, b, c, d);
    sink += s_copied(a, b, c, d);
    return (int)(sink & 0x7f);
}
