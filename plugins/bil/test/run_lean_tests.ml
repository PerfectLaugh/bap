open Core
open OUnit2
open Bap.Std
module Bil_lean = Bap_bil_plugin.Bil_lean

let typ = Type.imm 8
let out = Var.create "out" typ
let x = Bil.var (Var.create "x" typ)
let y = Bil.var (Var.create "y" typ)
let word ?(width = 8) value = Bil.int (Word.of_int ~width value)
let zero = word 0
let one = word 1
let bool value = Bil.int (if value then Word.b1 else Word.b0)
let bin operation left right = Bil.BinOp (operation, left, right)
let program exp = Bil.[ out := exp ]

let check before after =
  match Bil_lean.validate (program before) (program after) with
  | Ok () -> ()
  | Error message -> assert_failure message

let wide = Bil.var (Var.create "wide" (Type.imm 16))

let identities =
  [
    ("plus", bin Bil.PLUS x zero, x);
    ("minus", bin Bil.MINUS x x, zero);
    ("times", bin Bil.TIMES x one, x);
    ("divide", bin Bil.DIVIDE x one, x);
    ("signed divide", bin Bil.SDIVIDE x one, x);
    ("mod", bin Bil.MOD x one, zero);
    ("signed mod", bin Bil.SMOD x one, zero);
    ("left shift", bin Bil.LSHIFT x zero, x);
    ("right shift", bin Bil.RSHIFT x zero, x);
    ("arithmetic shift", bin Bil.ARSHIFT x zero, x);
    ("and", bin Bil.AND x (Bil.int (Word.ones 8)), x);
    ("or", bin Bil.OR x zero, x);
    ("xor", bin Bil.XOR x x, zero);
    ("equal", bin Bil.EQ x x, bool true);
    ("not equal", bin Bil.NEQ x x, bool false);
    ("less", bin Bil.LT x x, bool false);
    ("less or equal", bin Bil.LE x x, bool true);
    ("signed less", bin Bil.SLT x x, bool false);
    ("signed less or equal", bin Bil.SLE x x, bool true);
    ("negate", Bil.UnOp (Bil.NEG, Bil.UnOp (Bil.NEG, x)), x);
    ("not", Bil.UnOp (Bil.NOT, Bil.UnOp (Bil.NOT, x)), x);
    ("unsigned cast", Bil.Cast (Bil.LOW, 8, Bil.Cast (Bil.UNSIGNED, 16, x)), x);
    ("signed cast", Bil.Cast (Bil.LOW, 8, Bil.Cast (Bil.SIGNED, 16, x)), x);
    ("high cast", Bil.Cast (Bil.HIGH, 8, Bil.Concat (x, y)), x);
    ("low cast", Bil.Cast (Bil.LOW, 8, Bil.Concat (x, y)), y);
    ( "extract concat",
      Bil.Concat (Bil.Extract (15, 8, wide), Bil.Extract (7, 0, wide)),
      wide );
    ("conditional", Bil.Ite (bool true, x, y), x);
    ("signed mod of a negative", bin Bil.SMOD (word 255) (word 3), word 2);
    ("signed mod by a negative", bin Bil.SMOD (word 1) (word 253), word 254);
    ("signed mod of negatives", bin Bil.SMOD (word 254) (word 253), word 254);
    ("mod is unsigned", bin Bil.MOD (word 255) (word 3), zero);
    ("divide by zero", bin Bil.DIVIDE x zero, Bil.int (Word.ones 8));
    ("signed divide by zero", bin Bil.SDIVIDE x zero, Bil.int (Word.ones 8));
    ("mod by zero", bin Bil.MOD x zero, x);
    ("signed mod by zero", bin Bil.SMOD x zero, x);
    ("signed divide truncates", bin Bil.SDIVIDE (word 249) (word 2), word 253);
  ]

let identity_test (name, before, after) = name >:: fun _ -> check before after

let false_rewrite _ =
  match
    Bil_lean.validate
      (program (bin Bil.PLUS x zero))
      (program (bin Bil.PLUS x one))
  with
  | Ok () -> assert_failure "Lean accepted a false rewrite"
  | Error message ->
      assert_bool message (String.is_substring message ~substring:"error")

let rejected name before after =
  name >:: fun _ ->
  match Bil_lean.validate (program before) (program after) with
  | Ok () -> assert_failure ("Lean accepted " ^ name)
  | Error message ->
      assert_bool message (String.is_substring message ~substring:"error")

let wrong_semantics =
  [
    rejected "signed mod as a truncating remainder of a negative"
      (bin Bil.SMOD (word 255) (word 3))
      (word 255);
    rejected "signed mod as a truncating remainder by a negative"
      (bin Bil.SMOD (word 1) (word 253))
      (word 1);
    rejected "division by zero as zero" (bin Bil.DIVIDE x zero) zero;
    rejected "signed division by zero as zero" (bin Bil.SDIVIDE x zero) zero;
  ]

let checked_constant_folding _ =
  match
    Bil_lean.checked_fold_consts (program (bin Bil.PLUS (word 1) (word 2)))
  with
  | [ Bil.Move (_, Bil.Int result) ] -> assert_equal 3 (Word.to_int_exn result)
  | _ ->
      assert_failure "constant folding did not produce the expected immediate"

let checked_signed_mod_folding _ =
  match
    Bil_lean.checked_fold_consts (program (bin Bil.SMOD (word 255) (word 3)))
  with
  | [ Bil.Move (_, Bil.Int result) ] -> assert_equal 2 (Word.to_int_exn result)
  | _ -> assert_failure "folding did not produce the expected immediate"

let checked_division_by_zero_folding _ =
  match
    Bil_lean.checked_fold_consts (program (bin Bil.DIVIDE (word 5) zero))
  with
  | [ Bil.Move (_, Bil.Int result) ] ->
      assert_equal 255 (Word.to_int_exn result)
  | [ Bil.Move (_, Bil.BinOp (Bil.DIVIDE, _, _)) ] -> ()
  | _ -> assert_failure "folding did not produce the expected expression"

let memory_wrapper _ =
  let memory = Bil.var (Var.create "memory" (Type.mem `r32 `r8)) in
  let address = Bil.var (Var.create "address" (Type.imm 32)) in
  let zero = Bil.int (Word.zero 32) in
  let load address = Bil.Load (memory, address, LittleEndian, `r8) in
  check (load (bin Bil.PLUS address zero)) (load address)

let assumption_memory _ =
  let memory = Bil.var (Var.create "memory" (Type.mem `r32 `r8)) in
  let address = Var.create "address" (Type.imm 32) in
  let temporary =
    Var.create ~fresh:true ~is_virtual:true "address" (Type.imm 32)
  in
  let load address = Bil.Load (memory, address, LittleEndian, `r8) in
  match
    Bil_lean.validate_assumptions
      ~assumptions:[ (temporary, Bil.var address) ]
      (load (Bil.var temporary))
      (load (Bil.var address))
  with
  | Ok () -> ()
  | Error message -> assert_failure message

let () =
  run_test_tt_main
    ("Bil_lean_integration"
    >::: List.map identities ~f:identity_test
         @ wrong_semantics
         @ [
             "false rewrite" >:: false_rewrite;
             "checked constant folding" >:: checked_constant_folding;
             "checked signed mod folding" >:: checked_signed_mod_folding;
             "checked division by zero folding"
             >:: checked_division_by_zero_folding;
             "memory wrapper" >:: memory_wrapper;
             "assumption memory" >:: assumption_memory;
           ])
