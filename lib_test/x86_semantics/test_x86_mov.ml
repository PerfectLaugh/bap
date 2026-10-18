(* the moves of x86, which were the x86-mov tests of the testsuite *)

open Show

let%expect_test "x86_64 88 c3" =
  show x86_64 "88 c3";
  [%expect
    {|
    movb %al, %bl
    {
      RBX := high:56[RBX].7:0[RAX]
    }
    |}]

let%expect_test "x86_64 88 e7" =
  show x86_64 "88 e7";
  [%expect
    {|
    movb %ah, %bh
    {
      RBX := high:48[RBX].15:8[RAX].low:8[RBX]
    }
    |}]

let%expect_test "x86_64 88 c7" =
  show x86_64 "88 c7";
  [%expect
    {|
    movb %al, %bh
    {
      RBX := high:48[RBX].7:0[RAX].low:8[RBX]
    }
    |}]

let%expect_test "x86_64 88 e3" =
  show x86_64 "88 e3";
  [%expect
    {|
    movb %ah, %bl
    {
      RBX := high:56[RBX].15:8[RAX]
    }
    |}]

let%expect_test "x86_64 88 03" =
  show x86_64 "88 03";
  [%expect
    {|
    movb %al, (%rbx)
    {
      mem := mem with [RBX] <- 7:0[RAX]
    }
    |}]

let%expect_test "x86_64 88 23" =
  show x86_64 "88 23";
  [%expect
    {|
    movb %ah, (%rbx)
    {
      mem := mem with [RBX] <- 15:8[RAX]
    }
    |}]

let%expect_test "x86_64 66 89 c3" =
  show x86_64 "66 89 c3";
  [%expect
    {|
    movw %ax, %bx
    {
      RBX := high:48[RBX].15:0[RAX]
    }
    |}]

let%expect_test "x86_64 66 89 03" =
  show x86_64 "66 89 03";
  [%expect
    {|
    movw %ax, (%rbx)
    {
      mem := mem with [RBX, el]:u16 <- 15:0[RAX]
    }
    |}]

let%expect_test "x86_64 89 c3" =
  show x86_64 "89 c3";
  [%expect
    {|
    movl %eax, %ebx
    {
      RBX := pad:64[31:0[RAX]]
    }
    |}]

let%expect_test "x86_64 89 03" =
  show x86_64 "89 03";
  [%expect
    {|
    movl %eax, (%rbx)
    {
      mem := mem with [RBX, el]:u32 <- 31:0[RAX]
    }
    |}]

let%expect_test "x86_64 48 89 c3" =
  show x86_64 "48 89 c3";
  [%expect {|
    movq %rax, %rbx
    {
      RBX := RAX
    }
    |}]

let%expect_test "x86_64 48 89 03" =
  show x86_64 "48 89 03";
  [%expect
    {|
    movq %rax, (%rbx)
    {
      mem := mem with [RBX, el]:u64 <- RAX
    }
    |}]

let%expect_test "x86_64 8a d8" =
  show x86_64 "8a d8";
  [%expect
    {|
    movb %al, %bl
    {
      RBX := high:56[RBX].7:0[RAX]
    }
    |}]

let%expect_test "x86_64 8a fc" =
  show x86_64 "8a fc";
  [%expect
    {|
    movb %ah, %bh
    {
      RBX := high:48[RBX].15:8[RAX].low:8[RBX]
    }
    |}]

let%expect_test "x86_64 8a f8" =
  show x86_64 "8a f8";
  [%expect
    {|
    movb %al, %bh
    {
      RBX := high:48[RBX].7:0[RAX].low:8[RBX]
    }
    |}]

let%expect_test "x86_64 8a dc" =
  show x86_64 "8a dc";
  [%expect
    {|
    movb %ah, %bl
    {
      RBX := high:56[RBX].15:8[RAX]
    }
    |}]

let%expect_test "x86_64 8a 03" =
  show x86_64 "8a 03";
  [%expect
    {|
    movb (%rbx), %al
    {
      RAX := high:56[RAX].mem[RBX]
    }
    |}]

let%expect_test "x86_64 8a 23" =
  show x86_64 "8a 23";
  [%expect
    {|
    movb (%rbx), %ah
    {
      RAX := high:48[RAX].mem[RBX].low:8[RAX]
    }
    |}]

let%expect_test "x86_64 66 8b d8" =
  show x86_64 "66 8b d8";
  [%expect
    {|
    movw %ax, %bx
    {
      RBX := high:48[RBX].15:0[RAX]
    }
    |}]

let%expect_test "x86_64 66 8b 03" =
  show x86_64 "66 8b 03";
  [%expect
    {|
    movw (%rbx), %ax
    {
      RAX := high:48[RAX].mem[RBX, el]:u16
    }
    |}]

let%expect_test "x86_64 8b d8" =
  show x86_64 "8b d8";
  [%expect
    {|
    movl %eax, %ebx
    {
      RBX := pad:64[31:0[RAX]]
    }
    |}]

let%expect_test "x86_64 8b 03" =
  show x86_64 "8b 03";
  [%expect
    {|
    movl (%rbx), %eax
    {
      RAX := pad:64[mem[RBX, el]:u32]
    }
    |}]

let%expect_test "x86_64 48 8b d8" =
  show x86_64 "48 8b d8";
  [%expect {|
    movq %rax, %rbx
    {
      RBX := RAX
    }
    |}]

let%expect_test "x86_64 48 8b 03" =
  show x86_64 "48 8b 03";
  [%expect
    {|
    movq (%rbx), %rax
    {
      RAX := mem[RBX, el]:u64
    }
    |}]

let%expect_test "x86_64 66 8c e0" =
  show x86_64 "66 8c e0";
  [%expect {|
    movw %fs, %ax
    {
      RAX := high:48[RAX].FS
    }
    |}]

let%expect_test "x86_64 8c e0" =
  show x86_64 "8c e0";
  [%expect {|
    movl %fs, %eax
    {
      RAX := pad:64[FS]
    }
    |}]

let%expect_test "x86_64 48 8c e0" =
  show x86_64 "48 8c e0";
  [%expect {|
    movq %fs, %rax
    {
      RAX := pad:64[FS]
    }
    |}]

let%expect_test "x86_64 66 8c 20" =
  show x86_64 "66 8c 20";
  [%expect
    {|
    movw %fs, (%rax)
    {
      mem := mem with [RAX, el]:u16 <- FS
    }
    |}]

let%expect_test "x86_64 66 8e e0" =
  show x86_64 "66 8e e0";
  [%expect {|
    movw %ax, %fs
    {
      FS := 15:0[RAX]
    }
    |}]

let%expect_test "x86_64 8e e0" =
  show x86_64 "8e e0";
  [%expect
    {|
    movl %eax, %fs
    {
      FS := low:16[31:0[RAX]]
    }
    |}]

let%expect_test "x86_64 48 8e e0" =
  show x86_64 "48 8e e0";
  [%expect {|
    movq %rax, %fs
    {
      FS := low:16[RAX]
    }
    |}]

let%expect_test "x86_64 66 8e 20" =
  show x86_64 "66 8e 20";
  [%expect
    {|
    movw (%rax), %fs
    {
      FS := mem[RAX, el]:u16
    }
    |}]

let%expect_test "x86_64 a0 04 00 00 00 00 00 00 00" =
  show x86_64 "a0 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsb 0x4, %al
    {
      RAX := high:56[RAX].mem[4]
    }
    |}]

let%expect_test "x86_64 66 a1 04 00 00 00 00 00 00 00" =
  show x86_64 "66 a1 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsw 0x4, %ax
    {
      RAX := high:48[RAX].mem[4, el]:u16
    }
    |}]

let%expect_test "x86_64 a1 04 00 00 00 00 00 00 00" =
  show x86_64 "a1 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsl 0x4, %eax
    {
      RAX := pad:64[mem[4, el]:u32]
    }
    |}]

let%expect_test "x86_64 48 a1 04 00 00 00 00 00 00 00" =
  show x86_64 "48 a1 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsq 0x4, %rax
    {
      RAX := mem[4, el]:u64
    }
    |}]

let%expect_test "x86_64 a2 04 00 00 00 00 00 00 00" =
  show x86_64 "a2 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsb %al, 0x4
    {
      mem := mem with [4] <- 7:0[RAX]
    }
    |}]

let%expect_test "x86_64 66 a3 04 00 00 00 00 00 00 00" =
  show x86_64 "66 a3 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsw %ax, 0x4
    {
      mem := mem with [4, el]:u16 <- 15:0[RAX]
    }
    |}]

let%expect_test "x86_64 a3 04 00 00 00 00 00 00 00" =
  show x86_64 "a3 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsl %eax, 0x4
    {
      mem := mem with [4, el]:u32 <- 31:0[RAX]
    }
    |}]

let%expect_test "x86_64 48 a3 04 00 00 00 00 00 00 00" =
  show x86_64 "48 a3 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsq %rax, 0x4
    {
      mem := mem with [4, el]:u64 <- RAX
    }
    |}]

let%expect_test "x86_64 b0 04" =
  show x86_64 "b0 04";
  [%expect {|
    movb $0x4, %al
    {
      RAX := high:56[RAX].4
    }
    |}]

let%expect_test "x86_64 b4 04" =
  show x86_64 "b4 04";
  [%expect
    {|
    movb $0x4, %ah
    {
      RAX := high:48[RAX].4.low:8[RAX]
    }
    |}]

let%expect_test "x86_64 66 b8 04 00" =
  show x86_64 "66 b8 04 00";
  [%expect {|
    movw $0x4, %ax
    {
      RAX := high:48[RAX].4
    }
    |}]

let%expect_test "x86_64 b8 04 00 00 00" =
  show x86_64 "b8 04 00 00 00";
  [%expect {|
    movl $0x4, %eax
    {
      RAX := 4
    }
    |}]

let%expect_test "x86_64 48 b8 04 00 00 00 00 00 00 00" =
  show x86_64 "48 b8 04 00 00 00 00 00 00 00";
  [%expect {|
    movabsq $0x4, %rax
    {
      RAX := 4
    }
    |}]

let%expect_test "x86_64 c6 00 04" =
  show x86_64 "c6 00 04";
  [%expect
    {|
    movb $0x4, (%rax)
    {
      mem := mem with [RAX] <- 4
    }
    |}]

let%expect_test "x86_64 66 c7 00 04 00" =
  show x86_64 "66 c7 00 04 00";
  [%expect
    {|
    movw $0x4, (%rax)
    {
      mem := mem with [RAX, el]:u16 <- 4
    }
    |}]

let%expect_test "x86_64 c7 00 04 00 00 00" =
  show x86_64 "c7 00 04 00 00 00";
  [%expect
    {|
    movl $0x4, (%rax)
    {
      mem := mem with [RAX, el]:u32 <- 4
    }
    |}]

let%expect_test "x86_64 48 c7 00 04 00 00 00" =
  show x86_64 "48 c7 00 04 00 00 00";
  [%expect
    {|
    movq $0x4, (%rax)
    {
      mem := mem with [RAX, el]:u64 <- 4
    }
    |}]

let%expect_test "i686 88 c3" =
  show i686 "88 c3";
  [%expect
    {|
    movb %al, %bl
    {
      EBX := high:24[EBX].7:0[EAX]
    }
    |}]

let%expect_test "i686 88 e7" =
  show i686 "88 e7";
  [%expect
    {|
    movb %ah, %bh
    {
      EBX := high:16[EBX].15:8[EAX].low:8[EBX]
    }
    |}]

let%expect_test "i686 88 c7" =
  show i686 "88 c7";
  [%expect
    {|
    movb %al, %bh
    {
      EBX := high:16[EBX].7:0[EAX].low:8[EBX]
    }
    |}]

let%expect_test "i686 88 e3" =
  show i686 "88 e3";
  [%expect
    {|
    movb %ah, %bl
    {
      EBX := high:24[EBX].15:8[EAX]
    }
    |}]

let%expect_test "i686 88 03" =
  show i686 "88 03";
  [%expect
    {|
    movb %al, (%ebx)
    {
      mem := mem with [EBX] <- 7:0[EAX]
    }
    |}]

let%expect_test "i686 88 23" =
  show i686 "88 23";
  [%expect
    {|
    movb %ah, (%ebx)
    {
      mem := mem with [EBX] <- 15:8[EAX]
    }
    |}]

let%expect_test "i686 66 89 c3" =
  show i686 "66 89 c3";
  [%expect
    {|
    movw %ax, %bx
    {
      EBX := high:16[EBX].15:0[EAX]
    }
    |}]

let%expect_test "i686 66 89 03" =
  show i686 "66 89 03";
  [%expect
    {|
    movw %ax, (%ebx)
    {
      mem := mem with [EBX, el]:u16 <- 15:0[EAX]
    }
    |}]

let%expect_test "i686 89 c3" =
  show i686 "89 c3";
  [%expect {|
    movl %eax, %ebx
    {
      EBX := EAX
    }
    |}]

let%expect_test "i686 89 03" =
  show i686 "89 03";
  [%expect
    {|
    movl %eax, (%ebx)
    {
      mem := mem with [EBX, el]:u32 <- EAX
    }
    |}]

let%expect_test "i686 8a d8" =
  show i686 "8a d8";
  [%expect
    {|
    movb %al, %bl
    {
      EBX := high:24[EBX].7:0[EAX]
    }
    |}]

let%expect_test "i686 8a fc" =
  show i686 "8a fc";
  [%expect
    {|
    movb %ah, %bh
    {
      EBX := high:16[EBX].15:8[EAX].low:8[EBX]
    }
    |}]

let%expect_test "i686 8a f8" =
  show i686 "8a f8";
  [%expect
    {|
    movb %al, %bh
    {
      EBX := high:16[EBX].7:0[EAX].low:8[EBX]
    }
    |}]

let%expect_test "i686 8a dc" =
  show i686 "8a dc";
  [%expect
    {|
    movb %ah, %bl
    {
      EBX := high:24[EBX].15:8[EAX]
    }
    |}]

let%expect_test "i686 8a 03" =
  show i686 "8a 03";
  [%expect
    {|
    movb (%ebx), %al
    {
      EAX := high:24[EAX].mem[EBX]
    }
    |}]

let%expect_test "i686 8a 23" =
  show i686 "8a 23";
  [%expect
    {|
    movb (%ebx), %ah
    {
      EAX := high:16[EAX].mem[EBX].low:8[EAX]
    }
    |}]

let%expect_test "i686 66 8b d8" =
  show i686 "66 8b d8";
  [%expect
    {|
    movw %ax, %bx
    {
      EBX := high:16[EBX].15:0[EAX]
    }
    |}]

let%expect_test "i686 66 8b 03" =
  show i686 "66 8b 03";
  [%expect
    {|
    movw (%ebx), %ax
    {
      EAX := high:16[EAX].mem[EBX, el]:u16
    }
    |}]

let%expect_test "i686 8b d8" =
  show i686 "8b d8";
  [%expect {|
    movl %eax, %ebx
    {
      EBX := EAX
    }
    |}]

let%expect_test "i686 8b 03" =
  show i686 "8b 03";
  [%expect
    {|
    movl (%ebx), %eax
    {
      EAX := mem[EBX, el]:u32
    }
    |}]

let%expect_test "i686 66 8c e0" =
  show i686 "66 8c e0";
  [%expect {|
    movw %fs, %ax
    {
      EAX := high:16[EAX].FS
    }
    |}]

let%expect_test "i686 8c e0" =
  show i686 "8c e0";
  [%expect {|
    movl %fs, %eax
    {
      EAX := pad:32[FS]
    }
    |}]

let%expect_test "i686 66 8e e0" =
  show i686 "66 8e e0";
  [%expect {|
    movw %ax, %fs
    {
      FS := 15:0[EAX]
    }
    |}]

let%expect_test "i686 8e e0" =
  show i686 "8e e0";
  [%expect {|
    movl %eax, %fs
    {
      FS := low:16[EAX]
    }
    |}]

let%expect_test "i686 a0 04 00 00 00" =
  show i686 "a0 04 00 00 00";
  [%expect
    {|
    movb 0x4, %al
    {
      EAX := high:24[EAX].mem[4]
    }
    |}]

let%expect_test "i686 66 a1 04 00 00 00" =
  show i686 "66 a1 04 00 00 00";
  [%expect
    {|
    movw 0x4, %ax
    {
      EAX := high:16[EAX].mem[4, el]:u16
    }
    |}]

let%expect_test "i686 a1 04 00 00 00" =
  show i686 "a1 04 00 00 00";
  [%expect {|
    movl 0x4, %eax
    {
      EAX := mem[4, el]:u32
    }
    |}]

let%expect_test "i686 a2 04 00 00 00" =
  show i686 "a2 04 00 00 00";
  [%expect
    {|
    movb %al, 0x4
    {
      mem := mem with [4] <- 7:0[EAX]
    }
    |}]

let%expect_test "i686 66 a3 04 00 00 00" =
  show i686 "66 a3 04 00 00 00";
  [%expect
    {|
    movw %ax, 0x4
    {
      mem := mem with [4, el]:u16 <- 15:0[EAX]
    }
    |}]

let%expect_test "i686 a3 04 00 00 00" =
  show i686 "a3 04 00 00 00";
  [%expect
    {|
    movl %eax, 0x4
    {
      mem := mem with [4, el]:u32 <- EAX
    }
    |}]

let%expect_test "i686 b0 04" =
  show i686 "b0 04";
  [%expect {|
    movb $0x4, %al
    {
      EAX := high:24[EAX].4
    }
    |}]

let%expect_test "i686 b4 04" =
  show i686 "b4 04";
  [%expect
    {|
    movb $0x4, %ah
    {
      EAX := high:16[EAX].4.low:8[EAX]
    }
    |}]

let%expect_test "i686 66 b8 04 00" =
  show i686 "66 b8 04 00";
  [%expect {|
    movw $0x4, %ax
    {
      EAX := high:16[EAX].4
    }
    |}]

let%expect_test "i686 b8 04 00 00 00" =
  show i686 "b8 04 00 00 00";
  [%expect {|
    movl $0x4, %eax
    {
      EAX := 4
    }
    |}]

let%expect_test "i686 c6 00 04" =
  show i686 "c6 00 04";
  [%expect
    {|
    movb $0x4, (%eax)
    {
      mem := mem with [EAX] <- 4
    }
    |}]

let%expect_test "i686 66 c7 00 04 00" =
  show i686 "66 c7 00 04 00";
  [%expect
    {|
    movw $0x4, (%eax)
    {
      mem := mem with [EAX, el]:u16 <- 4
    }
    |}]

let%expect_test "i686 c7 00 04 00 00 00" =
  show i686 "c7 00 04 00 00 00";
  [%expect
    {|
    movl $0x4, (%eax)
    {
      mem := mem with [EAX, el]:u32 <- 4
    }
    |}]
