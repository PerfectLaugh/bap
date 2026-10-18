(* the tests of bap-mc; the lifting of the moves and of the addressing modes
   of x86 is tested by the expect tests of lib_test/x86_semantics *)

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

let tests = [ mov; version; prefix; torture ]
