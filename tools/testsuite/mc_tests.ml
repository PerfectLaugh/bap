(* the tests of bap-mc *)

open Suite

let mov _ =
  let cases =
    [
      ("x86-64", {|\x48\x89\xc3\x00|}, {|mov. %rax, %rbx|});
      ("x86", {|\x89\xc3|}, {|mov. %eax, %ebx|});
      ("arm", {|\x01\x00\xa0\xe1|}, {|mov r0, r1|});
      ("thumb", {|\x08\x46|}, {|mov r0, r1|});
      ("mips", {|\x00\x40\x08\x21|}, {|move *\$1, *\$2|});
      ("systemz", {|\x18\x12|}, {|lr %r1, %r2|});
    ]
  in
  List.concat_map
    (fun (arch, code, asm) ->
      (* the trailing byte is not an instruction *)
      List.map
        (fun (suffix, code) ->
          let name = arch ^ ".mov" ^ suffix in
          case ("mc/mov/" ^ name) (fun env ->
              let out = mc env [ "--arch=" ^ arch; "--show-insn=asm"; code ] in
              has env name out asm))
        [ ("", code); (".trail", code ^ {|\x00|}) ])
    cases

let version _ =
  [
    case "mc/version" (fun env ->
        has env "mc version" (mc env [ "--version" ]) "1|2");
  ]

let lift_opts arch =
  [
    "--arch=" ^ arch;
    "--show-insn=asm";
    "--x86-lifter=modern";
    "--show-bil=pretty";
  ]

(* [batch name arch insns] lifts the instructions [insns] in one run, and
   checks that the instructions and their BIL are in the output in order *)
let batch name arch insns =
  case name (fun env ->
      let codes =
        String.concat "," (List.map (fun (code, _, _) -> code) insns)
      in
      let out = mc env (lift_opts arch @ [ codes ]) in
      sequence env out
        (List.map
           (fun (_, asm, bil) ->
             (Printf.sprintf "%s for %s.*%s" name asm bil, asm ^ ".*" ^ bil))
           insns))

let escape str =
  String.to_seq str
  |> Seq.map (function
    | ('[' | ']' | '(' | ')' | '+') as c -> Printf.sprintf "\\%c" c
    | c -> String.make 1 c)
  |> List.of_seq |> String.concat ""

(* a number as bap prints it *)
let number n = if n < 10 then string_of_int n else Printf.sprintf "0x%X" n

(* the stores to the memory with all addressing modes and segment prefixes,
   the code, the assembly and the address in the BIL, and the stores
   relative to the instruction pointer, whose address depends on the
   address of the instruction *)
let addressing_modes bits =
  let reg r = (if bits = 64 then "r" else "e") ^ r in
  let up r = String.uppercase_ascii (reg r) in
  let insn = if bits = 64 then "movq" else "movl" in
  let rex = if bits = 64 then [ "0x48" ] else [] in
  let disp8 d = [ Printf.sprintf "0x%02x" d ]
  and disp32 d = [ Printf.sprintf "0x%02x" d; "0x00"; "0x00"; "0x00" ] in
  let index r k =
    let shift = match k with 1 -> 0 | 2 -> 1 | 4 -> 2 | _ -> 3 in
    if k = 1 then up r else Printf.sprintf "%s << %d" (up r) shift
  in
  let operand d inner = (if d = 0 then "" else "0x4") ^ "(" ^ inner ^ ")" in
  let scaled r k =
    if k = 1 then "%" ^ reg r else Printf.sprintf "%%%s,%d" (reg r) k
  in
  (* the source register, the bytes after the opcode, the operand, the terms
     of the address and the displacement *)
  let modes =
    List.concat_map
      (fun d ->
        ("ax", [ "0x45" ] @ disp8 d, operand d ("%" ^ reg "bp"), [ up "bp" ], d)
        :: List.map
             (fun (k, sib) ->
               ( "ax",
                 [ "0x44"; sib ] @ disp8 d,
                 operand d ("%" ^ reg "bp" ^ "," ^ scaled "dx" k),
                 [ up "bp"; index "dx" k ],
                 d ))
             [ (1, "0x15"); (2, "0x55"); (4, "0x95"); (8, "0xd5") ])
      [ 0; 4 ]
    @ List.concat_map
        (fun d ->
          List.map
            (fun (k, sib) ->
              ( "di",
                [ "0x3c"; sib ] @ disp32 d,
                operand d ("," ^ scaled "ax" k),
                [ index "ax" k ],
                d ))
            [ (1, "0x05"); (2, "0x45"); (4, "0x85"); (8, "0xc5") ])
        [ 0; 4 ]
  in
  let segments =
    [
      ("", [], None);
      ("%fs:", [ "0x64" ], Some "FS_BASE");
      ("%gs:", [ "0x65" ], Some "GS_BASE");
      ("%cs:", [ "0x2e" ], None);
      ("%ds:", [ "0x3e" ], None);
      ("%es:", [ "0x26" ], None);
      ("%ss:", [ "0x36" ], None);
    ]
  in
  let address terms =
    let terms =
      match terms with
      | [ term ] -> [ term ]
      | terms ->
          List.map
            (fun t -> if String.contains t '<' then "(" ^ t ^ ")" else t)
            terms
    in
    ".*" ^ escape ("[" ^ String.concat " + " terms ^ ", el]") ^ ".*"
  in
  let absolute =
    if bits = 64 then
      ( String.concat ","
          ([ "0x48"; "0xa3"; "0x04" ] @ List.init 7 (fun _ -> "0x00")),
        "movabsq %rax, 0x4",
        address [ "4" ] )
    else ("0xa3,0x04,0x00,0x00,0x00", "movl %eax, 0x4", address [ "4" ])
  in
  let stores =
    List.concat_map
      (fun (seg, prefix, base) ->
        List.map
          (fun (src, bytes, op, terms, d) ->
            ( String.concat "," (prefix @ rex @ [ "0x89" ] @ bytes),
              escape (Printf.sprintf "%s %%%s, %s%s" insn (reg src) seg op),
              address
                (Option.to_list base @ terms
                @ if d = 0 then [] else [ string_of_int d ]) ))
          modes)
      segments
  and relative =
    if bits = 32 then []
    else
      List.concat_map
        (fun (seg, prefix, base) ->
          List.map
            (fun d ->
              let pc = 7 + List.length prefix + d in
              ( String.concat "," (prefix @ rex @ [ "0x89"; "0x3d" ] @ disp32 d),
                escape
                  (Printf.sprintf "%s %%rdi, %s%s" insn seg (operand d "%rip")),
                address (Option.to_list base @ [ number pc ]) ))
            [ 0; 4 ])
        segments
  in
  (absolute :: stores, relative)

let addressing _ =
  List.concat_map
    (fun (arch, bits) ->
      let stores, relative = addressing_modes bits in
      let name = "mc/x86-addressing/" ^ arch in
      (* each instruction relative to the instruction pointer runs alone,
         since it is at the address 0 *)
      batch name arch stores
      :: List.map
           (fun (code, asm, bil) ->
             let name = Printf.sprintf "%s/[%s] -> %s" name asm code in
             case name (fun env ->
                 has env name
                   (mc env (lift_opts arch @ [ code ]))
                   (asm ^ "." ^ bil)))
           relative)
    [ ("x86-64", 64); ("x86", 32) ]

let x86_64_movs =
  [
    ({|0x88,0xc3|}, {|movb %al, %bl|}, {|RBX := high:56\[RBX\].7:0\[RAX\]|});
    ( {|0x88,0xe7|},
      {|movb %ah, %bh|},
      {|RBX := high:48\[RBX\].(extract:)?15:8\[RAX\].low:8\[RBX\]|} );
    ( {|0x88,0xc7|},
      {|movb %al, %bh|},
      {|RBX := high:48\[RBX\].7:0\[RAX\].low:8\[RBX\]|} );
    ( {|0x88,0xe3|},
      {|movb %ah, %bl|},
      {|RBX := high:56\[RBX\].(extract:)?15:8\[RAX\]|} );
    ( {|0x88,0x03|},
      {|movb %al, \(%rbx\)|},
      {|mem := mem with \[RBX\] <- 7:0\[RAX\]|} );
    ( {|0x88,0x23|},
      {|movb %ah, \(%rbx\)|},
      {|mem := mem with \[RBX\] <- (extract:)?15:8\[RAX\]|} );
    ( {|0x66,0x89,0xc3|},
      {|movw %ax, %bx|},
      {|RBX := high:48\[RBX\].15:0\[RAX\]|} );
    ( {|0x66,0x89,0x03|},
      {|movw %ax, \(%rbx\)|},
      {|mem := mem with \[RBX, el\]:u16 <- 15:0\[RAX\]|} );
    ({|0x89,0xc3|}, {|movl %eax, %ebx|}, {|RBX := pad:64\[31:0\[RAX\]\]|});
    ( {|0x89,0x03|},
      {|movl %eax, \(%rbx\)|},
      {|mem := mem with \[RBX, el\]:u32 <- 31:0\[RAX\]|} );
    ({|0x48,0x89,0xc3|}, {|movq %rax, %rbx|}, {|RBX := RAX|});
    ( {|0x48,0x89,0x03|},
      {|movq %rax, \(%rbx\)|},
      {|mem := mem with \[RBX, el\]:u64 <- RAX|} );
    ({|0x8a,0xd8|}, {|movb %al, %bl|}, {|RBX := high:56\[RBX\].7:0\[RAX\]|});
    ( {|0x8a,0xfc|},
      {|movb %ah, %bh|},
      {|RBX := high:48\[RBX\].(extract:)?15:8\[RAX\].low:8\[RBX\]|} );
    ( {|0x8a,0xf8|},
      {|movb %al, %bh|},
      {|RBX := high:48\[RBX\].7:0\[RAX\].low:8\[RBX\]|} );
    ( {|0x8a,0xdc|},
      {|movb %ah, %bl|},
      {|RBX := high:56\[RBX\].(extract:)?15:8\[RAX\]|} );
    ({|0x8a,0x03|}, {|movb \(%rbx\), %al|}, {|RAX := high:56\[RAX\].mem\[RBX\]|});
    ( {|0x8a,0x23|},
      {|movb \(%rbx\), %ah|},
      {|RAX := high:48\[RAX\].mem\[RBX\].low:8\[RAX\]|} );
    ( {|0x66,0x8b,0xd8|},
      {|movw %ax, %bx|},
      {|RBX := high:48\[RBX\].15:0\[RAX\]|} );
    ( {|0x66,0x8b,0x03|},
      {|movw \(%rbx\), %ax|},
      {|RAX := high:48\[RAX\].mem\[RBX, el\]:u16|} );
    ({|0x8b,0xd8|}, {|movl %eax, %ebx|}, {|RBX := pad:64\[31:0\[RAX\]\]|});
    ( {|0x8b,0x03|},
      {|movl \(%rbx\), %eax|},
      {|RAX := pad:64\[mem\[RBX, el\]:u32\]|} );
    ({|0x48,0x8b,0xd8|}, {|movq %rax, %rbx|}, {|RBX := RAX|});
    ({|0x48,0x8b,0x03|}, {|movq \(%rbx\), %rax|}, {|RAX := mem\[RBX, el\]:u64|});
    ({|0x66,0x8c,0xe0|}, {|movw %fs, %ax|}, {|RAX := high:48\[RAX\].FS|});
    ({|0x8c,0xe0|}, {|movl %fs, %eax|}, {|RAX := pad:64\[FS\]|});
    ({|0x48,0x8c,0xe0|}, {|movq %fs, %rax|}, {|RAX := pad:64\[FS\]|});
    ( {|0x66,0x8c,0x20|},
      {|movw %fs, \(%rax\)|},
      {|mem := mem with \[RAX, el\]:u16 <- FS|} );
    ({|0x66,0x8e,0xe0|}, {|movw %ax, %fs|}, {|FS := 15:0\[RAX\]|});
    ({|0x8e,0xe0|}, {|movl %eax, %fs|}, {|FS := low:16\[31:0\[RAX\]\]|});
    ({|0x48,0x8e,0xe0|}, {|movq %rax, %fs|}, {|FS := low:16\[RAX\]|});
    ({|0x66,0x8e,0x20|}, {|movw \(%rax\), %fs|}, {|FS := mem\[RAX, el\]:u16|});
    ( {|0xa0,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsb 0x4, %al|},
      {|RAX := high:56\[RAX\].mem\[4\]|} );
    ( {|0x66,0xa1,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsw 0x4, %ax|},
      {|RAX := high:48\[RAX\].mem\[4, el\]:u16|} );
    ( {|0xa1,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsl 0x4, %eax|},
      {|RAX := pad:64\[mem\[4, el\]:u32\]|} );
    ( {|0x48,0xa1,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsq 0x4, %rax|},
      {|RAX := mem\[4, el\]:u64|} );
    ( {|0xa2,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsb %al, 0x4|},
      {|mem := mem with \[4\] <- 7:0\[RAX\]|} );
    ( {|0x66,0xa3,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsw %ax, 0x4|},
      {|mem := mem with \[4, el\]:u16 <- 15:0\[RAX\]|} );
    ( {|0xa3,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsl %eax, 0x4|},
      {|mem := mem with \[4, el\]:u32 <- 31:0\[RAX\]|} );
    ( {|0x48,0xa3,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsq %rax, 0x4|},
      {|mem := mem with \[4, el\]:u64 <- RAX|} );
    ({|0xb0,0x04|}, {|movb \$0x4, %al|}, {|RAX := high:56\[RAX\].4|});
    ( {|0xb4,0x04|},
      {|movb \$0x4, %ah|},
      {|RAX := high:48\[RAX\].4.low:8\[RAX\]|} );
    ({|0x66,0xb8,0x04,0x00|}, {|movw \$0x4, %ax|}, {|RAX := high:48\[RAX\].4|});
    ({|0xb8,0x04,0x00,0x00,0x00|}, {|movl \$0x4, %eax|}, {|RAX := 4|});
    ( {|0x48,0xb8,0x04,0x00,0x00,0x00,0x00,0x00,0x00,0x00|},
      {|movabsq \$0x4, %rax|},
      {|RAX := 4|} );
    ( {|0xc6,0x00,0x04|},
      {|movb \$0x4, \(%rax\)|},
      {|mem := mem with \[RAX\] <- 4|} );
    ( {|0x66,0xc7,0x00,0x04,0x00|},
      {|movw \$0x4, \(%rax\)|},
      {|mem := mem with \[RAX, el\]:u16 <- 4|} );
    ( {|0xc7,0x00,0x04,0x00,0x00,0x00|},
      {|movl \$0x4, \(%rax\)|},
      {|mem := mem with \[RAX, el\]:u32 <- 4|} );
    ( {|0x48,0xc7,0x00,0x04,0x00,0x00,0x00|},
      {|movq \$0x4, \(%rax\)|},
      {|mem := mem with \[RAX, el\]:u64 <- 4|} );
  ]

let x86_movs =
  [
    ({|0x88,0xc3|}, {|movb %al, %bl|}, {|EBX := high:24\[EBX\].7:0\[EAX\]|});
    ( {|0x88,0xe7|},
      {|movb %ah, %bh|},
      {|EBX := high:16\[EBX\].(extract:)?15:8\[EAX\].low:8\[EBX\]|} );
    ( {|0x88,0xc7|},
      {|movb %al, %bh|},
      {|EBX := high:16\[EBX\].7:0\[EAX\].low:8\[EBX\]|} );
    ( {|0x88,0xe3|},
      {|movb %ah, %bl|},
      {|EBX := high:24\[EBX\].(extract:)?15:8\[EAX\]|} );
    ( {|0x88,0x03|},
      {|movb %al, \(%ebx\)|},
      {|mem := mem with \[EBX\] <- 7:0\[EAX\]|} );
    ( {|0x88,0x23|},
      {|movb %ah, \(%ebx\)|},
      {|mem := mem with \[EBX\] <- (extract:)?15:8\[EAX\]|} );
    ( {|0x66,0x89,0xc3|},
      {|movw %ax, %bx|},
      {|EBX := high:16\[EBX\].15:0\[EAX\]|} );
    ( {|0x66,0x89,0x03|},
      {|movw %ax, \(%ebx\)|},
      {|mem := mem with \[EBX, el\]:u16 <- 15:0\[EAX\]|} );
    ({|0x89,0xc3|}, {|movl %eax, %ebx|}, {|EBX := EAX|});
    ( {|0x89,0x03|},
      {|movl %eax, \(%ebx\)|},
      {|mem := mem with \[EBX, el\]:u32 <- EAX|} );
    ({|0x8a,0xd8|}, {|movb %al, %bl|}, {|EBX := high:24\[EBX\].7:0\[EAX\]|});
    ( {|0x8a,0xfc|},
      {|movb %ah, %bh|},
      {|EBX := high:16\[EBX\].(extract:)?15:8\[EAX\].low:8\[EBX\]|} );
    ( {|0x8a,0xf8|},
      {|movb %al, %bh|},
      {|EBX := high:16\[EBX\].7:0\[EAX\].low:8\[EBX\]|} );
    ( {|0x8a,0xdc|},
      {|movb %ah, %bl|},
      {|EBX := high:24\[EBX\].(extract:)?15:8\[EAX\]|} );
    ({|0x8a,0x03|}, {|movb \(%ebx\), %al|}, {|EAX := high:24\[EAX\].mem\[EBX\]|});
    ( {|0x8a,0x23|},
      {|movb \(%ebx\), %ah|},
      {|EAX := high:16\[EAX\].mem\[EBX\].low:8\[EAX\]|} );
    ( {|0x66,0x8b,0xd8|},
      {|movw %ax, %bx|},
      {|EBX := high:16\[EBX\].15:0\[EAX\]|} );
    ( {|0x66,0x8b,0x03|},
      {|movw \(%ebx\), %ax|},
      {|EAX := high:16\[EAX\].mem\[EBX, el\]:u16|} );
    ({|0x8b,0xd8|}, {|movl %eax, %ebx|}, {|EBX := EAX|});
    ({|0x8b,0x03|}, {|movl \(%ebx\), %eax|}, {|EAX := mem\[EBX, el\]:u32|});
    ({|0x66,0x8c,0xe0|}, {|movw %fs, %ax|}, {|EAX := high:16\[EAX\].FS|});
    ({|0x8c,0xe0|}, {|movl %fs, %eax|}, {|EAX := pad:32\[FS\]|});
    ({|0x66,0x8e,0xe0|}, {|movw %ax, %fs|}, {|FS := 15:0\[EAX\]|});
    ({|0x8e,0xe0|}, {|movl %eax, %fs|}, {|FS := low:16\[EAX\]|});
    ( {|0xa0,0x04,0x00,0x00,0x00|},
      {|movb 0x4, %al|},
      {|EAX := high:24\[EAX\].mem\[4\]|} );
    ( {|0x66,0xa1,0x04,0x00,0x00,0x00|},
      {|movw 0x4, %ax|},
      {|EAX := high:16\[EAX\].mem\[4, el\]:u16|} );
    ( {|0xa1,0x04,0x00,0x00,0x00|},
      {|movl 0x4, %eax|},
      {|EAX := mem\[4, el\]:u32|} );
    ( {|0xa2,0x04,0x00,0x00,0x00|},
      {|movb %al, 0x4|},
      {|mem := mem with \[4\] <- 7:0\[EAX\]|} );
    ( {|0x66,0xa3,0x04,0x00,0x00,0x00|},
      {|movw %ax, 0x4|},
      {|mem := mem with \[4, el\]:u16 <- 15:0\[EAX\]|} );
    ( {|0xa3,0x04,0x00,0x00,0x00|},
      {|movl %eax, 0x4|},
      {|mem := mem with \[4, el\]:u32 <- EAX|} );
    ({|0xb0,0x04|}, {|movb \$0x4, %al|}, {|EAX := high:24\[EAX\].4|});
    ( {|0xb4,0x04|},
      {|movb \$0x4, %ah|},
      {|EAX := high:16\[EAX\].4.low:8\[EAX\]|} );
    ({|0x66,0xb8,0x04,0x00|}, {|movw \$0x4, %ax|}, {|EAX := high:16\[EAX\].4|});
    ({|0xb8,0x04,0x00,0x00,0x00|}, {|movl \$0x4, %eax|}, {|EAX := 4|});
    ( {|0xc6,0x00,0x04|},
      {|movb \$0x4, \(%eax\)|},
      {|mem := mem with \[EAX\] <- 4|} );
    ( {|0x66,0xc7,0x00,0x04,0x00|},
      {|movw \$0x4, \(%eax\)|},
      {|mem := mem with \[EAX, el\]:u16 <- 4|} );
    ( {|0xc7,0x00,0x04,0x00,0x00,0x00|},
      {|movl \$0x4, \(%eax\)|},
      {|mem := mem with \[EAX, el\]:u32 <- 4|} );
  ]

let movs _ =
  [
    batch "mc/x86-mov/x86-64" "x86-64" x86_64_movs;
    batch "mc/x86-mov/x86" "x86" x86_movs;
  ]

let prefix _ =
  let insns =
    [
      ("0xf3,0x89,0xc3", "0x3", "mov. %eax, %ebx");
      ("0xf3,0xf2,0xf3,0x89,0xc3", "0x5", "mov. %eax, %ebx");
      ("0xf3,0xf2,0xf3,0x48,0x89,0xc3", "0x6", "mov. %rax, %rbx");
    ]
  in
  [
    case "mc/x86-prefix" (fun env ->
        let codes = String.concat "," (List.map (fun (c, _, _) -> c) insns) in
        let out = mc env [ "--show-size"; "--show-insn=asm"; codes ] in
        sequence env out
          (List.map
             (fun (_, size, asm) ->
               ("x86-prefix for " ^ size ^ " " ^ asm, size ^ ".*" ^ asm))
             insns));
  ]

(* throws garbage into the x86 disassembler and checks the output *)
let torture _ =
  [
    ({|\x89\xc3\x00|}, {|89 C3\(00\)|});
    ({|\x89\xc3\x00\x89\xc3|}, {|89 C3\(00 89\)C3|});
    ({|\x00|}, {|\(00\)|});
    ({|\xf3|}, {|\(F3\)|});
    ({|\xf3\xf2|}, {|\(F3 F2\)|});
    ({|\xf3\xf2\x00|}, {|\(F3 F2 00\)|});
  ]
  |> List.map (fun (input, output) ->
      let name = "mc/x86-torture/" ^ input in
      case name (fun env ->
          has env name
            (mc env [ "--stop-on-errors"; "--arch=x86"; input ])
            output))

let tests = [ mov; version; addressing; movs; prefix; torture ]
