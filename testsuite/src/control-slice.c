/* Deterministic control-dependence cases for emu/control-slice.

   gcc -O0 -no-pie -fcf-protection=none control-slice.c \
     -o ../bin/x86_64-linux-gnu-control-slice */

__asm__(".intel_syntax noprefix");

__asm__(".text\n"
        ".globl control_sites\n.type control_sites, @function\n"
        "control_sites:\n"
        ".quad .Lflag_write, .Lflag_load, .Lcomparison, .Lbranch\n"
        ".quad .Lnormal_producer, .Learly_producer, .Lpost_join\n"
        ".quad .Lloop_branch, .Louter_branch\n"
        ".quad control_result, control_flag\n");

__asm__(".globl c_select\n.type c_select, @function\n"
        "c_select:\n"
        ".Lflag_write: mov qword ptr [rip + control_flag], rdi\n"
        ".Lflag_load: mov rax, qword ptr [rip + control_flag]\n"
        ".Lcomparison: test rax, rax\n"
        ".Lbranch: jz .Learly_producer\n"
        ".Lnormal_producer: mov qword ptr [rip + control_result], 0x1111\n"
        "ret\n"
        ".Learly_producer: mov qword ptr [rip + control_result], 0x2222\n"
        "ret\n");

__asm__(".globl c_post\n.type c_post, @function\n"
        "c_post:\n"
        "test rdi, rdi\n"
        "jz .Lpost_other\n"
        "mov qword ptr [rip + control_result], 0x1111\n"
        "jmp .Lpost_join\n"
        ".Lpost_other: mov qword ptr [rip + control_result], 0x2222\n"
        ".Lpost_join: mov qword ptr [rip + control_result], 0x3333\n"
        "ret\n");

__asm__(".globl c_conditional\n.type c_conditional, @function\n"
        "c_conditional:\n"
        "mov rax, rdi\n"
        "cmp rsi, rdx\n"
        "cmovne rax, rcx\n"
        "mov qword ptr [rip + control_result], rax\n"
        "ret\n");

__asm__(".globl c_loop\n.type c_loop, @function\n"
        "c_loop:\n"
        "xor ecx, ecx\n"
        ".Lloop: mov qword ptr [rip + control_result], rcx\n"
        "inc ecx\n"
        "cmp ecx, 3\n"
        ".Lloop_branch: jne .Lloop\n"
        "ret\n");

__asm__(".globl c_middle\n.type c_middle, @function\n"
        "c_middle: call c_select\n"
        "ret\n"
        ".globl c_outer\n.type c_outer, @function\n"
        "c_outer:\n"
        "test rsi, rsi\n"
        ".Louter_branch: jz .Louter_skip\n"
        "call c_middle\n"
        ".Louter_skip: ret\n");

__asm__(".att_syntax");

__asm__(".bss\n"
        ".globl control_result\n.type control_result, @function\n"
        "control_result: .zero 8\n"
        ".globl control_flag\n.type control_flag, @function\n"
        "control_flag: .zero 8\n"
        ".text\n");

int main(void) { return 0; }
