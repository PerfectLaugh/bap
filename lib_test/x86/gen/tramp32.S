/* runs the code at the address in the second argument with the machine
   state at the first: 8 general purpose registers in the order of their
   numbers, eflags at 32, 8 ymm registers at 48 and 8 mm registers at 304 */
        .text
        .globl run_code, run_back
run_code:
        mov 4(%esp), %eax
        mov 8(%esp), %ecx
        push %ebx; push %ebp; push %esi; push %edi
        mov %esp, saved_sp
        mov %eax, state
        mov %ecx, code
        .irp i, 0,1,2,3,4,5,6,7
        vmovdqu 48+\i*32(%eax), %ymm\i
        .endr
        .irp i, 0,1,2,3,4,5,6,7
        movq 304+\i*8(%eax), %mm\i
        .endr
        pushl 32(%eax)
        popfl
        mov 4(%eax), %ecx; mov 8(%eax), %edx; mov 12(%eax), %ebx
        mov 20(%eax), %ebp; mov 24(%eax), %esi; mov 28(%eax), %edi
        mov 16(%eax), %esp; mov 0(%eax), %eax
        jmp *code
run_back:
        mov %eax, scratch
        mov state, %eax
        mov %ecx, 4(%eax); mov %edx, 8(%eax); mov %ebx, 12(%eax)
        mov %esp, 16(%eax); mov %ebp, 20(%eax); mov %esi, 24(%eax)
        mov %edi, 28(%eax)
        mov saved_sp, %esp
        pushfl
        popl 32(%eax)
        cld
        mov scratch, %ecx
        mov %ecx, 0(%eax)
        .irp i, 0,1,2,3,4,5,6,7
        vmovdqu %ymm\i, 48+\i*32(%eax)
        .endr
        .irp i, 0,1,2,3,4,5,6,7
        movq %mm\i, 304+\i*8(%eax)
        .endr
        emms
        pop %edi; pop %esi; pop %ebp; pop %ebx
        ret
        .data
saved_sp: .long 0
state:  .long 0
code:   .long 0
scratch: .long 0
        .section .note.GNU-stack,"",@progbits
