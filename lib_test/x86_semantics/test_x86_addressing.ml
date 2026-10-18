(* the stores to the memory with all addressing modes and segment prefixes,
   which were the x86-addressing tests of the testsuite *)

open Show

let byte = Printf.sprintf "%02x"
let disp8 d = [ byte d ]
let disp32 d = [ byte d; "00"; "00"; "00" ]

(* the bytes after the opcode of the stores: a base and an index scaled by
   1, 2, 4 or 8, with no displacement or a displacement of a byte, an index
   alone with a displacement of four bytes, and in x86-64 the instruction
   pointer *)
let modes ~bits =
  List.concat_map
    (fun d ->
      ("45" :: disp8 d)
      :: List.map (fun sib -> "44" :: sib :: disp8 d) [ "15"; "55"; "95"; "d5" ])
    [ 0; 4 ]
  @ List.concat_map
      (fun d ->
        List.map (fun sib -> "3c" :: sib :: disp32 d) [ "05"; "45"; "85"; "c5" ])
      [ 0; 4 ]
  @ if bits = 64 then List.map (fun d -> "3d" :: disp32 d) [ 0; 4 ] else []

(* stores the accumulator or the destination index with the [prefix] *)
let stores ~bits prefix =
  let rex = if bits = 64 then [ "48" ] else [] in
  List.iter
    (fun bytes ->
      let mode = if bits = 64 then x86_64 else i686 in
      show mode (String.concat " " (prefix @ rex @ ("89" :: bytes))))
    (modes ~bits)

let%expect_test "x86-64 absolute" =
  show x86_64 "48 a3 04 00 00 00 00 00 00 00";
  [%expect
    {|
    movabsq %rax, 0x4
    {
      mem := mem with [4, el]:u64 <- RAX
    }
    |}]

let%expect_test "x86-64" =
  stores ~bits:64 [];
  [%expect
    {|
    movq %rax, (%rbp)
    {
      mem := mem with [RBP, el]:u64 <- RAX
    }
    movq %rax, (%rbp,%rdx)
    {
      mem := mem with [RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, (%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, (%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, (%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, 0x4(%rbp)
    {
      mem := mem with [RBP + 4, el]:u64 <- RAX
    }
    movq %rax, 0x4(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, 0x4(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, 0x4(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, 0x4(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, (,%rax)
    {
      mem := mem with [RAX, el]:u64 <- RDI
    }
    movq %rdi, (,%rax,2)
    {
      mem := mem with [RAX << 1, el]:u64 <- RDI
    }
    movq %rdi, (,%rax,4)
    {
      mem := mem with [RAX << 2, el]:u64 <- RDI
    }
    movq %rdi, (,%rax,8)
    {
      mem := mem with [RAX << 3, el]:u64 <- RDI
    }
    movq %rdi, 0x4(,%rax)
    {
      mem := mem with [RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, 0x4(,%rax,2)
    {
      mem := mem with [(RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, 0x4(,%rax,4)
    {
      mem := mem with [(RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, 0x4(,%rax,8)
    {
      mem := mem with [(RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, (%rip)
    {
      mem := mem with [7, el]:u64 <- RDI
    }
    movq %rdi, 0x4(%rip)
    {
      mem := mem with [0xB, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %fs" =
  stores ~bits:64 [ "64" ];
  [%expect
    {|
    movq %rax, %fs:(%rbp)
    {
      mem := mem with [FS_BASE + RBP, el]:u64 <- RAX
    }
    movq %rax, %fs:(%rbp,%rdx)
    {
      mem := mem with [FS_BASE + RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %fs:(%rbp,%rdx,2)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %fs:(%rbp,%rdx,4)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %fs:(%rbp,%rdx,8)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %fs:0x4(%rbp)
    {
      mem := mem with [FS_BASE + RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %fs:0x4(%rbp,%rdx)
    {
      mem := mem with [FS_BASE + RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %fs:0x4(%rbp,%rdx,2)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %fs:0x4(%rbp,%rdx,4)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %fs:0x4(%rbp,%rdx,8)
    {
      mem := mem with [FS_BASE + RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %fs:(,%rax)
    {
      mem := mem with [FS_BASE + RAX, el]:u64 <- RDI
    }
    movq %rdi, %fs:(,%rax,2)
    {
      mem := mem with [FS_BASE + (RAX << 1), el]:u64 <- RDI
    }
    movq %rdi, %fs:(,%rax,4)
    {
      mem := mem with [FS_BASE + (RAX << 2), el]:u64 <- RDI
    }
    movq %rdi, %fs:(,%rax,8)
    {
      mem := mem with [FS_BASE + (RAX << 3), el]:u64 <- RDI
    }
    movq %rdi, %fs:0x4(,%rax)
    {
      mem := mem with [FS_BASE + RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %fs:0x4(,%rax,2)
    {
      mem := mem with [FS_BASE + (RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %fs:0x4(,%rax,4)
    {
      mem := mem with [FS_BASE + (RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %fs:0x4(,%rax,8)
    {
      mem := mem with [FS_BASE + (RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %fs:(%rip)
    {
      mem := mem with [FS_BASE + 8, el]:u64 <- RDI
    }
    movq %rdi, %fs:0x4(%rip)
    {
      mem := mem with [FS_BASE + 0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %gs" =
  stores ~bits:64 [ "65" ];
  [%expect
    {|
    movq %rax, %gs:(%rbp)
    {
      mem := mem with [GS_BASE + RBP, el]:u64 <- RAX
    }
    movq %rax, %gs:(%rbp,%rdx)
    {
      mem := mem with [GS_BASE + RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %gs:(%rbp,%rdx,2)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %gs:(%rbp,%rdx,4)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %gs:(%rbp,%rdx,8)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %gs:0x4(%rbp)
    {
      mem := mem with [GS_BASE + RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %gs:0x4(%rbp,%rdx)
    {
      mem := mem with [GS_BASE + RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %gs:0x4(%rbp,%rdx,2)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %gs:0x4(%rbp,%rdx,4)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %gs:0x4(%rbp,%rdx,8)
    {
      mem := mem with [GS_BASE + RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %gs:(,%rax)
    {
      mem := mem with [GS_BASE + RAX, el]:u64 <- RDI
    }
    movq %rdi, %gs:(,%rax,2)
    {
      mem := mem with [GS_BASE + (RAX << 1), el]:u64 <- RDI
    }
    movq %rdi, %gs:(,%rax,4)
    {
      mem := mem with [GS_BASE + (RAX << 2), el]:u64 <- RDI
    }
    movq %rdi, %gs:(,%rax,8)
    {
      mem := mem with [GS_BASE + (RAX << 3), el]:u64 <- RDI
    }
    movq %rdi, %gs:0x4(,%rax)
    {
      mem := mem with [GS_BASE + RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %gs:0x4(,%rax,2)
    {
      mem := mem with [GS_BASE + (RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %gs:0x4(,%rax,4)
    {
      mem := mem with [GS_BASE + (RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %gs:0x4(,%rax,8)
    {
      mem := mem with [GS_BASE + (RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %gs:(%rip)
    {
      mem := mem with [GS_BASE + 8, el]:u64 <- RDI
    }
    movq %rdi, %gs:0x4(%rip)
    {
      mem := mem with [GS_BASE + 0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %cs" =
  stores ~bits:64 [ "2e" ];
  [%expect
    {|
    movq %rax, %cs:(%rbp)
    {
      mem := mem with [RBP, el]:u64 <- RAX
    }
    movq %rax, %cs:(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %cs:(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %cs:(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %cs:(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %cs:0x4(%rbp)
    {
      mem := mem with [RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %cs:0x4(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %cs:0x4(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %cs:0x4(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %cs:0x4(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %cs:(,%rax)
    {
      mem := mem with [RAX, el]:u64 <- RDI
    }
    movq %rdi, %cs:(,%rax,2)
    {
      mem := mem with [RAX << 1, el]:u64 <- RDI
    }
    movq %rdi, %cs:(,%rax,4)
    {
      mem := mem with [RAX << 2, el]:u64 <- RDI
    }
    movq %rdi, %cs:(,%rax,8)
    {
      mem := mem with [RAX << 3, el]:u64 <- RDI
    }
    movq %rdi, %cs:0x4(,%rax)
    {
      mem := mem with [RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %cs:0x4(,%rax,2)
    {
      mem := mem with [(RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %cs:0x4(,%rax,4)
    {
      mem := mem with [(RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %cs:0x4(,%rax,8)
    {
      mem := mem with [(RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %cs:(%rip)
    {
      mem := mem with [8, el]:u64 <- RDI
    }
    movq %rdi, %cs:0x4(%rip)
    {
      mem := mem with [0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %ds" =
  stores ~bits:64 [ "3e" ];
  [%expect
    {|
    movq %rax, %ds:(%rbp)
    {
      mem := mem with [RBP, el]:u64 <- RAX
    }
    movq %rax, %ds:(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %ds:(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %ds:(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %ds:(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %ds:0x4(%rbp)
    {
      mem := mem with [RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %ds:0x4(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %ds:0x4(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %ds:0x4(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %ds:0x4(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %ds:(,%rax)
    {
      mem := mem with [RAX, el]:u64 <- RDI
    }
    movq %rdi, %ds:(,%rax,2)
    {
      mem := mem with [RAX << 1, el]:u64 <- RDI
    }
    movq %rdi, %ds:(,%rax,4)
    {
      mem := mem with [RAX << 2, el]:u64 <- RDI
    }
    movq %rdi, %ds:(,%rax,8)
    {
      mem := mem with [RAX << 3, el]:u64 <- RDI
    }
    movq %rdi, %ds:0x4(,%rax)
    {
      mem := mem with [RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %ds:0x4(,%rax,2)
    {
      mem := mem with [(RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ds:0x4(,%rax,4)
    {
      mem := mem with [(RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ds:0x4(,%rax,8)
    {
      mem := mem with [(RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ds:(%rip)
    {
      mem := mem with [8, el]:u64 <- RDI
    }
    movq %rdi, %ds:0x4(%rip)
    {
      mem := mem with [0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %es" =
  stores ~bits:64 [ "26" ];
  [%expect
    {|
    movq %rax, %es:(%rbp)
    {
      mem := mem with [RBP, el]:u64 <- RAX
    }
    movq %rax, %es:(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %es:(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %es:(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %es:(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %es:0x4(%rbp)
    {
      mem := mem with [RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %es:0x4(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %es:0x4(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %es:0x4(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %es:0x4(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %es:(,%rax)
    {
      mem := mem with [RAX, el]:u64 <- RDI
    }
    movq %rdi, %es:(,%rax,2)
    {
      mem := mem with [RAX << 1, el]:u64 <- RDI
    }
    movq %rdi, %es:(,%rax,4)
    {
      mem := mem with [RAX << 2, el]:u64 <- RDI
    }
    movq %rdi, %es:(,%rax,8)
    {
      mem := mem with [RAX << 3, el]:u64 <- RDI
    }
    movq %rdi, %es:0x4(,%rax)
    {
      mem := mem with [RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %es:0x4(,%rax,2)
    {
      mem := mem with [(RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %es:0x4(,%rax,4)
    {
      mem := mem with [(RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %es:0x4(,%rax,8)
    {
      mem := mem with [(RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %es:(%rip)
    {
      mem := mem with [8, el]:u64 <- RDI
    }
    movq %rdi, %es:0x4(%rip)
    {
      mem := mem with [0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86-64 %ss" =
  stores ~bits:64 [ "36" ];
  [%expect
    {|
    movq %rax, %ss:(%rbp)
    {
      mem := mem with [RBP, el]:u64 <- RAX
    }
    movq %rax, %ss:(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX, el]:u64 <- RAX
    }
    movq %rax, %ss:(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1), el]:u64 <- RAX
    }
    movq %rax, %ss:(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2), el]:u64 <- RAX
    }
    movq %rax, %ss:(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3), el]:u64 <- RAX
    }
    movq %rax, %ss:0x4(%rbp)
    {
      mem := mem with [RBP + 4, el]:u64 <- RAX
    }
    movq %rax, %ss:0x4(%rbp,%rdx)
    {
      mem := mem with [RBP + RDX + 4, el]:u64 <- RAX
    }
    movq %rax, %ss:0x4(%rbp,%rdx,2)
    {
      mem := mem with [RBP + (RDX << 1) + 4, el]:u64 <- RAX
    }
    movq %rax, %ss:0x4(%rbp,%rdx,4)
    {
      mem := mem with [RBP + (RDX << 2) + 4, el]:u64 <- RAX
    }
    movq %rax, %ss:0x4(%rbp,%rdx,8)
    {
      mem := mem with [RBP + (RDX << 3) + 4, el]:u64 <- RAX
    }
    movq %rdi, %ss:(,%rax)
    {
      mem := mem with [RAX, el]:u64 <- RDI
    }
    movq %rdi, %ss:(,%rax,2)
    {
      mem := mem with [RAX << 1, el]:u64 <- RDI
    }
    movq %rdi, %ss:(,%rax,4)
    {
      mem := mem with [RAX << 2, el]:u64 <- RDI
    }
    movq %rdi, %ss:(,%rax,8)
    {
      mem := mem with [RAX << 3, el]:u64 <- RDI
    }
    movq %rdi, %ss:0x4(,%rax)
    {
      mem := mem with [RAX + 4, el]:u64 <- RDI
    }
    movq %rdi, %ss:0x4(,%rax,2)
    {
      mem := mem with [(RAX << 1) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ss:0x4(,%rax,4)
    {
      mem := mem with [(RAX << 2) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ss:0x4(,%rax,8)
    {
      mem := mem with [(RAX << 3) + 4, el]:u64 <- RDI
    }
    movq %rdi, %ss:(%rip)
    {
      mem := mem with [8, el]:u64 <- RDI
    }
    movq %rdi, %ss:0x4(%rip)
    {
      mem := mem with [0xC, el]:u64 <- RDI
    }
    |}]

let%expect_test "x86 absolute" =
  show i686 "a3 04 00 00 00";
  [%expect
    {|
    movl %eax, 0x4
    {
      mem := mem with [4, el]:u32 <- EAX
    }
    |}]

let%expect_test "x86" =
  stores ~bits:32 [];
  [%expect
    {|
    movl %eax, (%ebp)
    {
      mem := mem with [EBP, el]:u32 <- EAX
    }
    movl %eax, (%ebp,%edx)
    {
      mem := mem with [EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, (%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, (%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, (%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, 0x4(%ebp)
    {
      mem := mem with [EBP + 4, el]:u32 <- EAX
    }
    movl %eax, 0x4(%ebp,%edx)
    {
      mem := mem with [EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, 0x4(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, 0x4(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, 0x4(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, (,%eax)
    {
      mem := mem with [EAX, el]:u32 <- EDI
    }
    movl %edi, (,%eax,2)
    {
      mem := mem with [EAX << 1, el]:u32 <- EDI
    }
    movl %edi, (,%eax,4)
    {
      mem := mem with [EAX << 2, el]:u32 <- EDI
    }
    movl %edi, (,%eax,8)
    {
      mem := mem with [EAX << 3, el]:u32 <- EDI
    }
    movl %edi, 0x4(,%eax)
    {
      mem := mem with [EAX + 4, el]:u32 <- EDI
    }
    movl %edi, 0x4(,%eax,2)
    {
      mem := mem with [(EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, 0x4(,%eax,4)
    {
      mem := mem with [(EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, 0x4(,%eax,8)
    {
      mem := mem with [(EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %fs" =
  stores ~bits:32 [ "64" ];
  [%expect
    {|
    movl %eax, %fs:(%ebp)
    {
      mem := mem with [FS_BASE + EBP, el]:u32 <- EAX
    }
    movl %eax, %fs:(%ebp,%edx)
    {
      mem := mem with [FS_BASE + EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %fs:(%ebp,%edx,2)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %fs:(%ebp,%edx,4)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %fs:(%ebp,%edx,8)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %fs:0x4(%ebp)
    {
      mem := mem with [FS_BASE + EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %fs:0x4(%ebp,%edx)
    {
      mem := mem with [FS_BASE + EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %fs:0x4(%ebp,%edx,2)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %fs:0x4(%ebp,%edx,4)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %fs:0x4(%ebp,%edx,8)
    {
      mem := mem with [FS_BASE + EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %fs:(,%eax)
    {
      mem := mem with [FS_BASE + EAX, el]:u32 <- EDI
    }
    movl %edi, %fs:(,%eax,2)
    {
      mem := mem with [FS_BASE + (EAX << 1), el]:u32 <- EDI
    }
    movl %edi, %fs:(,%eax,4)
    {
      mem := mem with [FS_BASE + (EAX << 2), el]:u32 <- EDI
    }
    movl %edi, %fs:(,%eax,8)
    {
      mem := mem with [FS_BASE + (EAX << 3), el]:u32 <- EDI
    }
    movl %edi, %fs:0x4(,%eax)
    {
      mem := mem with [FS_BASE + EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %fs:0x4(,%eax,2)
    {
      mem := mem with [FS_BASE + (EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %fs:0x4(,%eax,4)
    {
      mem := mem with [FS_BASE + (EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %fs:0x4(,%eax,8)
    {
      mem := mem with [FS_BASE + (EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %gs" =
  stores ~bits:32 [ "65" ];
  [%expect
    {|
    movl %eax, %gs:(%ebp)
    {
      mem := mem with [GS_BASE + EBP, el]:u32 <- EAX
    }
    movl %eax, %gs:(%ebp,%edx)
    {
      mem := mem with [GS_BASE + EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %gs:(%ebp,%edx,2)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %gs:(%ebp,%edx,4)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %gs:(%ebp,%edx,8)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %gs:0x4(%ebp)
    {
      mem := mem with [GS_BASE + EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %gs:0x4(%ebp,%edx)
    {
      mem := mem with [GS_BASE + EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %gs:0x4(%ebp,%edx,2)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %gs:0x4(%ebp,%edx,4)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %gs:0x4(%ebp,%edx,8)
    {
      mem := mem with [GS_BASE + EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %gs:(,%eax)
    {
      mem := mem with [GS_BASE + EAX, el]:u32 <- EDI
    }
    movl %edi, %gs:(,%eax,2)
    {
      mem := mem with [GS_BASE + (EAX << 1), el]:u32 <- EDI
    }
    movl %edi, %gs:(,%eax,4)
    {
      mem := mem with [GS_BASE + (EAX << 2), el]:u32 <- EDI
    }
    movl %edi, %gs:(,%eax,8)
    {
      mem := mem with [GS_BASE + (EAX << 3), el]:u32 <- EDI
    }
    movl %edi, %gs:0x4(,%eax)
    {
      mem := mem with [GS_BASE + EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %gs:0x4(,%eax,2)
    {
      mem := mem with [GS_BASE + (EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %gs:0x4(,%eax,4)
    {
      mem := mem with [GS_BASE + (EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %gs:0x4(,%eax,8)
    {
      mem := mem with [GS_BASE + (EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %cs" =
  stores ~bits:32 [ "2e" ];
  [%expect
    {|
    movl %eax, %cs:(%ebp)
    {
      mem := mem with [EBP, el]:u32 <- EAX
    }
    movl %eax, %cs:(%ebp,%edx)
    {
      mem := mem with [EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %cs:(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %cs:(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %cs:(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %cs:0x4(%ebp)
    {
      mem := mem with [EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %cs:0x4(%ebp,%edx)
    {
      mem := mem with [EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %cs:0x4(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %cs:0x4(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %cs:0x4(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %cs:(,%eax)
    {
      mem := mem with [EAX, el]:u32 <- EDI
    }
    movl %edi, %cs:(,%eax,2)
    {
      mem := mem with [EAX << 1, el]:u32 <- EDI
    }
    movl %edi, %cs:(,%eax,4)
    {
      mem := mem with [EAX << 2, el]:u32 <- EDI
    }
    movl %edi, %cs:(,%eax,8)
    {
      mem := mem with [EAX << 3, el]:u32 <- EDI
    }
    movl %edi, %cs:0x4(,%eax)
    {
      mem := mem with [EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %cs:0x4(,%eax,2)
    {
      mem := mem with [(EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %cs:0x4(,%eax,4)
    {
      mem := mem with [(EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %cs:0x4(,%eax,8)
    {
      mem := mem with [(EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %ds" =
  stores ~bits:32 [ "3e" ];
  [%expect
    {|
    movl %eax, %ds:(%ebp)
    {
      mem := mem with [EBP, el]:u32 <- EAX
    }
    movl %eax, %ds:(%ebp,%edx)
    {
      mem := mem with [EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %ds:(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %ds:(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %ds:(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %ds:0x4(%ebp)
    {
      mem := mem with [EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %ds:0x4(%ebp,%edx)
    {
      mem := mem with [EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %ds:0x4(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %ds:0x4(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %ds:0x4(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %ds:(,%eax)
    {
      mem := mem with [EAX, el]:u32 <- EDI
    }
    movl %edi, %ds:(,%eax,2)
    {
      mem := mem with [EAX << 1, el]:u32 <- EDI
    }
    movl %edi, %ds:(,%eax,4)
    {
      mem := mem with [EAX << 2, el]:u32 <- EDI
    }
    movl %edi, %ds:(,%eax,8)
    {
      mem := mem with [EAX << 3, el]:u32 <- EDI
    }
    movl %edi, %ds:0x4(,%eax)
    {
      mem := mem with [EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %ds:0x4(,%eax,2)
    {
      mem := mem with [(EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %ds:0x4(,%eax,4)
    {
      mem := mem with [(EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %ds:0x4(,%eax,8)
    {
      mem := mem with [(EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %es" =
  stores ~bits:32 [ "26" ];
  [%expect
    {|
    movl %eax, %es:(%ebp)
    {
      mem := mem with [EBP, el]:u32 <- EAX
    }
    movl %eax, %es:(%ebp,%edx)
    {
      mem := mem with [EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %es:(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %es:(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %es:(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %es:0x4(%ebp)
    {
      mem := mem with [EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %es:0x4(%ebp,%edx)
    {
      mem := mem with [EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %es:0x4(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %es:0x4(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %es:0x4(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %es:(,%eax)
    {
      mem := mem with [EAX, el]:u32 <- EDI
    }
    movl %edi, %es:(,%eax,2)
    {
      mem := mem with [EAX << 1, el]:u32 <- EDI
    }
    movl %edi, %es:(,%eax,4)
    {
      mem := mem with [EAX << 2, el]:u32 <- EDI
    }
    movl %edi, %es:(,%eax,8)
    {
      mem := mem with [EAX << 3, el]:u32 <- EDI
    }
    movl %edi, %es:0x4(,%eax)
    {
      mem := mem with [EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %es:0x4(,%eax,2)
    {
      mem := mem with [(EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %es:0x4(,%eax,4)
    {
      mem := mem with [(EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %es:0x4(,%eax,8)
    {
      mem := mem with [(EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]

let%expect_test "x86 %ss" =
  stores ~bits:32 [ "36" ];
  [%expect
    {|
    movl %eax, %ss:(%ebp)
    {
      mem := mem with [EBP, el]:u32 <- EAX
    }
    movl %eax, %ss:(%ebp,%edx)
    {
      mem := mem with [EBP + EDX, el]:u32 <- EAX
    }
    movl %eax, %ss:(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1), el]:u32 <- EAX
    }
    movl %eax, %ss:(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2), el]:u32 <- EAX
    }
    movl %eax, %ss:(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3), el]:u32 <- EAX
    }
    movl %eax, %ss:0x4(%ebp)
    {
      mem := mem with [EBP + 4, el]:u32 <- EAX
    }
    movl %eax, %ss:0x4(%ebp,%edx)
    {
      mem := mem with [EBP + EDX + 4, el]:u32 <- EAX
    }
    movl %eax, %ss:0x4(%ebp,%edx,2)
    {
      mem := mem with [EBP + (EDX << 1) + 4, el]:u32 <- EAX
    }
    movl %eax, %ss:0x4(%ebp,%edx,4)
    {
      mem := mem with [EBP + (EDX << 2) + 4, el]:u32 <- EAX
    }
    movl %eax, %ss:0x4(%ebp,%edx,8)
    {
      mem := mem with [EBP + (EDX << 3) + 4, el]:u32 <- EAX
    }
    movl %edi, %ss:(,%eax)
    {
      mem := mem with [EAX, el]:u32 <- EDI
    }
    movl %edi, %ss:(,%eax,2)
    {
      mem := mem with [EAX << 1, el]:u32 <- EDI
    }
    movl %edi, %ss:(,%eax,4)
    {
      mem := mem with [EAX << 2, el]:u32 <- EDI
    }
    movl %edi, %ss:(,%eax,8)
    {
      mem := mem with [EAX << 3, el]:u32 <- EDI
    }
    movl %edi, %ss:0x4(,%eax)
    {
      mem := mem with [EAX + 4, el]:u32 <- EDI
    }
    movl %edi, %ss:0x4(,%eax,2)
    {
      mem := mem with [(EAX << 1) + 4, el]:u32 <- EDI
    }
    movl %edi, %ss:0x4(,%eax,4)
    {
      mem := mem with [(EAX << 2) + 4, el]:u32 <- EDI
    }
    movl %edi, %ss:0x4(,%eax,8)
    {
      mem := mem with [(EAX << 3) + 4, el]:u32 <- EDI
    }
    |}]
