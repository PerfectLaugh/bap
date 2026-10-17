/* runs the code at the address in rsi with the machine state at rdi:
   16 general purpose registers in the order of their numbers, rflags at
   128, and 16 xmm registers at 144; the code jumps back to run_back */
        .text
        .globl run_code, run_back
run_code:
        push %rbx; push %rbp; push %r12; push %r13; push %r14; push %r15
        mov %rsp, saved_sp(%rip)
        mov %rdi, state(%rip)
        mov %rsi, code(%rip)
        .irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
        movdqu 144+\i*16(%rdi), %xmm\i
        .endr
        pushq 128(%rdi)
        popfq
        mov 0(%rdi), %rax; mov 8(%rdi), %rcx; mov 16(%rdi), %rdx
        mov 24(%rdi), %rbx; mov 40(%rdi), %rbp; mov 48(%rdi), %rsi
        mov 64(%rdi), %r8; mov 72(%rdi), %r9; mov 80(%rdi), %r10
        mov 88(%rdi), %r11; mov 96(%rdi), %r12; mov 104(%rdi), %r13
        mov 112(%rdi), %r14; mov 120(%rdi), %r15
        mov 32(%rdi), %rsp; mov 56(%rdi), %rdi
        jmp *code(%rip)
run_back:
        mov %rax, scratch(%rip)
        mov state(%rip), %rax
        mov %rcx, 8(%rax); mov %rdx, 16(%rax); mov %rbx, 24(%rax)
        mov %rsp, 32(%rax); mov %rbp, 40(%rax); mov %rsi, 48(%rax)
        mov %rdi, 56(%rax); mov %r8, 64(%rax); mov %r9, 72(%rax)
        mov %r10, 80(%rax); mov %r11, 88(%rax); mov %r12, 96(%rax)
        mov %r13, 104(%rax); mov %r14, 112(%rax); mov %r15, 120(%rax)
        mov saved_sp(%rip), %rsp
        pushfq
        popq 128(%rax)
        cld
        mov scratch(%rip), %rcx
        mov %rcx, 0(%rax)
        .irp i, 0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15
        movdqu %xmm\i, 144+\i*16(%rax)
        .endr
        pop %r15; pop %r14; pop %r13; pop %r12; pop %rbp; pop %rbx
        ret
        .data
saved_sp: .quad 0
state:  .quad 0
code:   .quad 0
scratch: .quad 0
        .section .note.GNU-stack,"",@progbits
