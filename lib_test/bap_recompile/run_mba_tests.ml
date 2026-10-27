open Core
open Bap.Std
open OUnit2
module Mba = Bap_recompile.Recompile_mba

let width = 8
let x = Bil.var (Var.create "x" (Type.imm width))
let y = Bil.var (Var.create "y" (Type.imm width))
let z = Bil.var (Var.create "z" (Type.imm width))
let word value = Bil.int (Word.of_int ~width value)
let bin op left right = Bil.BinOp (op, left, right)
let plus = bin Bil.PLUS
let minus = bin Bil.MINUS
let times = bin Bil.TIMES
let and_ = bin Bil.AND
let or_ = bin Bil.OR
let xor = bin Bil.XOR

let simplify exp =
  match Mba.simplify_exp exp with
  | Ok exp -> exp
  | Error error -> assert_failure (Error.to_string_hum error)

let assert_exp expected actual =
  assert_equal ~cmp:Exp.equal
    ~printer:(Format.asprintf "%a" Exp.pp)
    expected actual

let test_identities _ =
  assert_exp x (simplify (plus x (word 0)));
  assert_exp x (simplify (times x (word 1)));
  assert_exp x (simplify (and_ x x));
  assert_exp (word 0) (simplify (xor x x));
  assert_exp x (simplify (Bil.UnOp (Bil.NOT, Bil.UnOp (Bil.NOT, x))));
  assert_exp (Bil.int Word.b1) (simplify (bin Bil.EQ x x))

let test_canonicalization _ =
  let left = simplify (plus x (plus y z)) in
  let right = simplify (plus (plus z y) x) in
  assert_exp left right;
  assert_exp left (simplify left)

let test_mba_add _ =
  let obfuscated = plus (xor x y) (times (word 2) (and_ x y)) in
  assert_exp (simplify (plus x y)) (simplify obfuscated)

let test_mba_or _ =
  assert_exp (simplify (or_ x y)) (simplify (plus (xor x y) (and_ x y)));
  assert_exp (simplify (plus x y)) (simplify (plus (or_ x y) (and_ x y)))

let test_mba_sub _ =
  assert_exp (simplify (xor x y)) (simplify (minus (or_ x y) (and_ x y)));
  assert_exp (simplify (and_ x y)) (simplify (minus (or_ x y) (xor x y)));
  assert_exp
    (simplify (xor x y))
    (simplify (minus (plus x y) (times (word 2) (and_ x y))))

let test_budget _ =
  match Mba.simplify_exp ~max_rewrites:0 (plus x (word 0)) with
  | Ok _ -> assert_failure "a rewrite exceeded the zero rewrite budget"
  | Error error ->
      assert_bool "unexpected budget error"
        (String.is_substring (Error.to_string_hum error) ~substring:"budget")

let test_certificate_rejection _ =
  match
    Mba.simplify_exp_with
      ~validate:(fun _ _ -> Error "injected rejection")
      (plus x (word 0))
  with
  | Ok _ -> assert_failure "an invalid rewrite certificate was accepted"
  | Error error ->
      assert_bool "the certificate error was lost"
        (String.is_substring
           (Error.to_string_hum error)
           ~substring:"injected rejection")

let test_unchanged_does_not_need_certificate _ =
  let calls = ref 0 in
  match
    Mba.simplify_exp_with
      ~validate:(fun _ _ ->
        incr calls;
        Error "unexpected validation")
      x
  with
  | Error error -> assert_failure (Error.to_string_hum error)
  | Ok after ->
      assert_exp x after;
      assert_equal 0 !calls

let test_subroutine_structure _ =
  let lhs = Var.create "out" (Type.imm width) in
  let def = Def.create lhs (plus x (word 0)) in
  let target = Tid.create () in
  let jmp = Jmp.create_goto ~cond:(bin Bil.EQ y y) (Direct target) in
  let blk = Blk.create ~defs:[ def ] ~jmps:[ jmp ] () in
  let sub = Sub.create ~name:"mba" ~blks:[ blk ] () in
  match Mba.simplify sub with
  | Error error -> assert_failure (Error.to_string_hum error)
  | Ok after -> (
      assert_equal ~cmp:Tid.equal (Term.tid sub) (Term.tid after);
      let after_blk = Term.first blk_t after |> Option.value_exn in
      assert_equal ~cmp:Tid.equal (Term.tid blk) (Term.tid after_blk);
      let after_def = Term.first def_t after_blk |> Option.value_exn in
      let after_jmp = Term.first jmp_t after_blk |> Option.value_exn in
      assert_equal ~cmp:Tid.equal (Term.tid def) (Term.tid after_def);
      assert_equal ~cmp:Tid.equal (Term.tid jmp) (Term.tid after_jmp);
      assert_exp x (Def.rhs after_def);
      assert_exp (Bil.int Word.b1) (Jmp.cond after_jmp);
      match Jmp.kind after_jmp with
      | Goto (Direct destination) ->
          assert_equal ~cmp:Tid.equal target destination
      | _ -> assert_failure "the jump destination changed")

let test_memory_boundaries _ =
  let memory = Bil.var (Var.create "memory" (Type.mem `r32 `r8)) in
  let address = Bil.var (Var.create "address" (Type.imm 32)) in
  let load address = Bil.Load (memory, address, LittleEndian, `r8) in
  let loaded = load address in
  let before =
    and_
      (Bil.Extract (7, 7, xor loaded (word 2)))
      (Bil.Extract (7, 7, xor loaded (word 1)))
  in
  assert_exp before (simplify before);
  let with_zero = load (plus address (Bil.int (Word.zero 32))) in
  assert_exp (load address) (simplify with_zero)

let temporary name =
  Var.create ~fresh:true ~is_virtual:true name (Type.imm width)

let simplify_blk defs jmps =
  Blk.create ~defs ~jmps () |> Mba.simplify_blk |> Or_error.ok_exn

let blk_def index blk =
  Term.enum def_t blk |> Seq.to_list |> fun defs -> List.nth_exn defs index

let test_shift_add _ =
  let shifted = Bil.BinOp (Bil.LSHIFT, x, word 1) in
  assert_exp (times x (word 3)) (simplify (plus x shifted))

let test_copy_propagation _ =
  let t1 = temporary "t1" and t2 = temporary "t2" and out = temporary "out" in
  let after =
    simplify_blk
      [
        Def.create t1 x;
        Def.create t2 (plus (Bil.var t1) (word 1));
        Def.create out (Bil.var t2);
      ]
      []
  in
  assert_exp (plus x (word 1)) (Def.rhs (blk_def 2 after))

let test_dependency_invalidation _ =
  let t1 = temporary "t1" and t2 = temporary "t2" and out = temporary "out" in
  let source = Var.create "source" (Type.imm width) in
  let after =
    simplify_blk
      [
        Def.create t1 (Bil.var source);
        Def.create t2 (plus (Bil.var t1) (word 1));
        Def.create source y;
        Def.create out (Bil.var t2);
      ]
      []
  in
  assert_exp (Bil.var t2) (Def.rhs (blk_def 3 after))

let test_self_reference _ =
  let t1 = temporary "t1" and out = temporary "out" in
  let after =
    simplify_blk
      [
        Def.create t1 (plus (Bil.var t1) (word 1)); Def.create out (Bil.var t1);
      ]
      []
  in
  assert_exp (Bil.var t1) (Def.rhs (blk_def 1 after))

let test_call_barrier _ =
  let t1 = temporary "t1" in
  let target = Tid.create () in
  let call = Jmp.create_call (Call.create ~target:(Direct target) ()) in
  let indirect = Jmp.create_goto (Indirect (Bil.var t1)) in
  let after = simplify_blk [ Def.create t1 x ] [ call; indirect ] in
  match Term.enum jmp_t after |> Seq.to_list with
  | [ _; goto ] -> (
      match Jmp.kind goto with
      | Goto (Indirect target) -> assert_exp (Bil.var t1) target
      | _ -> assert_failure "the indirect jump changed")
  | _ -> assert_failure "the call barrier changed the jump count"

let suite =
  "recompile_mba"
  >::: [
         "identities" >:: test_identities;
         "canonicalization" >:: test_canonicalization;
         "MBA addition" >:: test_mba_add;
         "MBA OR" >:: test_mba_or;
         "MBA subtraction" >:: test_mba_sub;
         "rewrite budget" >:: test_budget;
         "certificate rejection" >:: test_certificate_rejection;
         "unchanged certificate" >:: test_unchanged_does_not_need_certificate;
         "subroutine structure" >:: test_subroutine_structure;
         "memory boundaries" >:: test_memory_boundaries;
         "shift add" >:: test_shift_add;
         "copy propagation" >:: test_copy_propagation;
         "dependency invalidation" >:: test_dependency_invalidation;
         "self reference" >:: test_self_reference;
         "call barrier" >:: test_call_barrier;
       ]

let () = run_test_tt_main suite
