open Core
open OUnit2
open Bap.Std
module Bil_lean = Bap_bil_plugin.Bil_lean

let typ = Type.imm 8
let out = Var.create "out" typ
let x = Var.create "x" typ
let var_x = Bil.var x
let zero = Bil.int (Word.of_int ~width:8 0)
let program exp = Bil.[ out := exp ]
let assert_ok = function Ok () -> () | Error message -> assert_failure message

let assert_error ~substring = function
  | Ok () -> assert_failure "validation unexpectedly succeeded"
  | Error message ->
      assert_bool message
        (String.is_substring (String.lowercase message)
           ~substring:(String.lowercase substring))

let accepting_checker calls source =
  calls := source :: !calls;
  Ok ()

let validate calls before after =
  Bil_lean.validate_with ~checker:(accepting_checker calls) (program before)
    (program after)

let pure_change _ =
  let calls = ref [] in
  assert_ok (validate calls (Bil.BinOp (Bil.PLUS, var_x, zero)) var_x);
  assert_equal ~printer:Int.to_string 1 (List.length !calls)

let unchanged_unsupported _ =
  let calls = ref [] in
  let memory = Var.create "memory" (Type.mem `r32 `r8) in
  let address = Var.create "address" (Type.imm 32) in
  let load = Bil.Load (Bil.var memory, Bil.var address, LittleEndian, `r8) in
  assert_ok (validate calls load load);
  assert_equal 0 (List.length !calls)

let changed_child_of_unsupported _ =
  let calls = ref [] in
  let memory = Var.create "memory" (Type.mem `r32 `r8) in
  let address = Var.create "address" (Type.imm 32) in
  let addr = Bil.var address in
  let before =
    Bil.Load
      ( Bil.var memory,
        Bil.BinOp (Bil.PLUS, addr, Bil.int (Word.of_int ~width:32 0)),
        LittleEndian,
        `r8 )
  in
  let after = Bil.Load (Bil.var memory, addr, LittleEndian, `r8) in
  assert_ok (validate calls before after);
  assert_equal ~printer:Int.to_string 1 (List.length !calls)

let changed_child_of_let _ =
  let calls = ref [] in
  let temporary = Var.create "temporary" typ in
  let before =
    Bil.Let (temporary, Bil.BinOp (Bil.PLUS, var_x, zero), Bil.var temporary)
  in
  let after = Bil.Let (temporary, var_x, Bil.var temporary) in
  assert_ok (validate calls before after);
  assert_equal ~printer:Int.to_string 1 (List.length !calls)

let rejects_unknown _ =
  let calls = ref [] in
  assert_error ~substring:"unknown values"
    (validate calls (Bil.Unknown ("undefined", typ)) var_x);
  assert_equal 0 (List.length !calls)

let rejects_width_change _ =
  let calls = ref [] in
  let wide = Bil.var (Var.create "wide" (Type.imm 16)) in
  assert_error ~substring:"result width" (validate calls var_x wide);
  assert_equal 0 (List.length !calls)

let rejects_statement_change _ =
  let calls = ref [] in
  let checker = accepting_checker calls in
  Bil_lean.validate_with ~checker (program var_x) []
  |> assert_error ~substring:"number of BIL statements";
  assert_equal 0 (List.length !calls)

let propagates_checker_failure _ =
  Bil_lean.validate_with
    ~checker:(fun _ -> Error "injected checker failure")
    (program (Bil.BinOp (Bil.PLUS, var_x, zero)))
    (program var_x)
  |> assert_error ~substring:"injected checker failure"

let variables_use_identity _ =
  let calls = ref [] in
  let left = Bil.var (Var.create ~fresh:true "same" typ) in
  let right = Bil.var (Var.create ~fresh:true "same" typ) in
  assert_ok
    (validate calls
       (Bil.BinOp (Bil.PLUS, left, right))
       (Bil.BinOp (Bil.TIMES, right, left)));
  match !calls with
  | [ source ] ->
      assert_bool source
        (String.is_substring source ~substring:"(v0 : BitVec 8)");
      assert_bool source
        (String.is_substring source ~substring:"(v1 : BitVec 8)")
  | _ -> assert_failure "expected one generated proof"

let exact_whole_expression _ =
  let calls = ref [] in
  let y = Bil.var (Var.create "y" typ) in
  let bin op left right = Bil.BinOp (op, left, right) in
  let before =
    bin Bil.PLUS (bin Bil.XOR var_x y)
      (bin Bil.TIMES (Bil.int (Word.of_int ~width:8 2)) (bin Bil.AND var_x y))
  in
  let after = bin Bil.PLUS var_x y in
  assert_ok
    (Bil_lean.validate_exp_exact_with ~checker:(accepting_checker calls) before
       after);
  assert_equal ~printer:Int.to_string 1 (List.length !calls);
  match !calls with
  | [ source ] ->
      assert_bool source (String.is_substring source ~substring:"^^^");
      assert_bool source (String.is_substring source ~substring:" + ")
  | _ -> assert_failure "expected one whole-expression proof"

let () =
  run_test_tt_main
    ("Bil_lean"
    >::: [
           "pure change" >:: pure_change;
           "unchanged unsupported" >:: unchanged_unsupported;
           "changed child of unsupported" >:: changed_child_of_unsupported;
           "changed child of let" >:: changed_child_of_let;
           "rejects unknown" >:: rejects_unknown;
           "rejects width change" >:: rejects_width_change;
           "rejects statement change" >:: rejects_statement_change;
           "propagates checker failure" >:: propagates_checker_failure;
           "variables use identity" >:: variables_use_identity;
           "exact whole expression" >:: exact_whole_expression;
         ])
