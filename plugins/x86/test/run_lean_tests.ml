open Core
open OUnit2
open Bap_plugins.Std
open Bap.Std
module X86_lean = X86.X86_lean

let mode =
  Lifter_test.mode ~addr:0x20000 ~target:"x86_64" ~encoding:"llvm-x86_64" ()

let assert_ok = function Ok () -> () | Error message -> assert_failure message

let assert_error ~substring = function
  | Ok () -> assert_failure "validation unexpectedly succeeded"
  | Error message ->
      assert_bool message
        (String.is_substring (String.lowercase message)
           ~substring:(String.lowercase substring))

let validate width code =
  X86_lean.validate_add ~width (Lifter_test.lift mode code)

let add8 _ = assert_ok (validate 8 "00 d8")
let add16 _ = assert_ok (validate 16 "66 01 d8")
let add32 _ = assert_ok (validate 32 "01 d8")
let add64 _ = assert_ok (validate 64 "48 01 d8")
let rejects_sub _ = assert_error ~substring:"error" (validate 64 "48 29 d8")

let validate_operation operation width code =
  X86_lean.validate_reg_reg ~operation ~width ~destination:"RAX" ~left:"RAX"
    ~right:"RBX"
    (Lifter_test.lift mode code)

let operation_cases =
  [
    ( X86_lean.Sub,
      "SUB",
      [ (8, "28 d8"); (16, "66 29 d8"); (32, "29 d8"); (64, "48 29 d8") ] );
    ( X86_lean.And,
      "AND",
      [ (8, "20 d8"); (16, "66 21 d8"); (32, "21 d8"); (64, "48 21 d8") ] );
    ( X86_lean.Or,
      "OR",
      [ (8, "08 d8"); (16, "66 09 d8"); (32, "09 d8"); (64, "48 09 d8") ] );
    ( X86_lean.Xor,
      "XOR",
      [ (8, "30 d8"); (16, "66 31 d8"); (32, "31 d8"); (64, "48 31 d8") ] );
  ]

let operation_tests =
  List.concat_map operation_cases ~f:(fun (operation, name, cases) ->
      List.map cases ~f:(fun (width, code) ->
          sprintf "%s%d" name width >:: fun _ ->
          assert_ok (validate_operation operation width code)))

let rejects_wrong_operation _ =
  validate_operation X86_lean.Sub 64 "48 01 d8"
  |> assert_error ~substring:"error"

let validates_other_destination _ =
  X86_lean.validate_reg_reg ~operation:X86_lean.Add ~width:64 ~destination:"RCX"
    ~left:"RCX" ~right:"RBX"
    (Lifter_test.lift mode "48 01 d9")
  |> assert_ok

let rejects_unsupported_statement _ =
  X86_lean.validate_add ~width:64 [ Bil.Special "trap" ]
  |> assert_error ~substring:"straight-line"

let variable name width = Var.create name (Type.imm width)
let move name width exp = Bil.Move (variable name width, exp)

let rejects_unexpected_writes _ =
  let writes = "RAX" :: "RBX" :: [ "CF"; "OF"; "AF"; "SF"; "ZF"; "PF" ] in
  let bil =
    List.map writes ~f:(fun name ->
        let width = if String.is_prefix name ~prefix:"R" then 64 else 1 in
        let var = variable name width in
        Bil.Move (var, Bil.Var var))
  in
  X86_lean.validate_add ~width:64 bil
  |> assert_error ~substring:"unexpected architectural writes"

let rejects_uninitialized_temporary _ =
  let rax = variable "RAX" 64 in
  let rbx = variable "RBX" 64 in
  let temporary =
    Var.create ~fresh:true ~is_virtual:true "temporary" (Type.imm 64)
  in
  let result =
    Bil.Move (rax, Bil.BinOp (Bil.PLUS, Bil.Var temporary, Bil.Var rbx))
  in
  let flags =
    List.map [ "CF"; "OF"; "AF"; "SF"; "ZF"; "PF" ] ~f:(fun name ->
        move name 1 (Bil.Int Word.b0))
  in
  X86_lean.validate_add ~width:64 (result :: flags)
  |> assert_error ~substring:"uninitialized temporary"

let rejects_invalid_width _ =
  X86_lean.validate_add ~width:128 []
  |> assert_error ~substring:"unsupported ADD width"

let suite =
  "X86_lean"
  >::: [
         "ADD8" >:: add8;
         "ADD16" >:: add16;
         "ADD32" >:: add32;
         "ADD64" >:: add64;
         "rejects SUB" >:: rejects_sub;
         "rejects wrong operation" >:: rejects_wrong_operation;
         "validates other destination" >:: validates_other_destination;
         "rejects unsupported statement" >:: rejects_unsupported_statement;
         "rejects unexpected writes" >:: rejects_unexpected_writes;
         "rejects uninitialized temporary" >:: rejects_uninitialized_temporary;
         "rejects invalid width" >:: rejects_invalid_width;
       ]
       @ operation_tests

let () =
  match Bap_main.init () with
  | Error err ->
      Format.eprintf "Failed to initialize BAP: %a@\n%!"
        Bap_main.Extension.Error.pp err;
      exit 1
  | Ok () -> run_test_tt_main suite
