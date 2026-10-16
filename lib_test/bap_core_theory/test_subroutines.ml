open Core
open OUnit2
open Bap_core_theory
open KB.Syntax

(* evaluates a knowledge computation in an empty knowledge base *)
let eval (k : 'a KB.t) : 'a =
  let result = ref None in
  let obj =
    k >>= fun x ->
    result := Some x;
    Theory.Label.fresh
  in
  match KB.run Theory.Program.cls obj KB.empty with
  | Ok _ -> Option.value_exn !result
  | Error conflict -> assert_failure (KB.Conflict.to_string conflict)

let word x = Bitvec.(int x mod modulus 64)
let addrs xs = Set.of_list (module Bitvec_order) (List.map xs ~f:word)
let starts = addrs [ 0x10; 0x20 ]

(* a label at [addr] that belongs to [unit] *)
let label ?unit addr =
  Theory.Label.for_addr (word addr) >>= fun label ->
  KB.provide Theory.Label.unit label unit >>| fun () -> label

let is_subroutine ?unit addr =
  label ?unit addr >>= KB.collect Theory.Label.is_subroutine

let test_unit = Theory.Unit.for_file "/bin/test-subroutines"

let derived _ =
  eval
  @@ Theory.Label.promising_subroutines ~promise:(fun _ -> !!starts)
  @@ fun () ->
  let* unit = test_unit in
  let* starts' = KB.collect Theory.Unit.subroutines unit in
  assert_bool "the starts of the unit" (Set.equal starts starts');
  let* start = is_subroutine ~unit 0x10 in
  let* other = is_subroutine ~unit 0x11 in
  let+ orphan = is_subroutine 0x20 in
  assert_equal ~msg:"a start" (Some true) start;
  assert_equal ~msg:"not a start" None other;
  assert_equal ~msg:"a label without a unit" None orphan;
  assert_bool "all promises are bulk" (Theory.Label.has_bulk_subroutines ())

let per_label _ =
  let per_label label =
    KB.collect Theory.Label.addr label >>| function
    | Some addr when Set.mem starts addr -> Some true
    | _ -> None
  in
  eval
  @@ Theory.Label.promising_subroutines ~per_label ~promise:(fun _ -> !!starts)
  @@ fun () ->
  let+ start = is_subroutine 0x20 in
  assert_equal ~msg:"answered by the per-label promise" (Some true) start;
  assert_bool "a per-label promise with a bulk form"
    (Theory.Label.has_bulk_subroutines ())

let plain _ =
  let before = KB.Slot.promises Theory.Label.is_subroutine in
  eval
  @@ KB.promising Theory.Label.is_subroutine ~promise:(fun _ -> !!None)
  @@ fun () ->
  assert_equal ~msg:"a scoped promise is counted" ~printer:Int.to_string
    (before + 1)
    (KB.Slot.promises Theory.Label.is_subroutine);
  assert_bool "a promise without a bulk form"
    (not (Theory.Label.has_bulk_subroutines ()));
  KB.return ()

let scope_ends _ =
  let before = KB.Slot.promises Theory.Label.is_subroutine in
  eval
    (KB.promising Theory.Label.is_subroutine
       ~promise:(fun _ -> !!None)
       (fun () -> KB.return ()));
  assert_equal ~msg:"the promise is removed with its scope"
    ~printer:Int.to_string before
    (KB.Slot.promises Theory.Label.is_subroutine)

let suite =
  "Subroutines"
  >::: [
         "derived from the unit" >:: derived;
         "with a per-label promise" >:: per_label;
         "a plain promise" >:: plain;
         "the end of a scope" >:: scope_ends;
       ]

let () = run_test_tt_main suite
