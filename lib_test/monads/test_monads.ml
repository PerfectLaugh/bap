open Core
open OUnit2
open Monads.Std
module State = Monad.State

(* the collection functions of sequences are computed the same way, and
   with the same order of effects, as the ones of lists *)

open State.Syntax

(* records the visited elements in the state *)
let visit x = State.update (fun xs -> x :: xs) >>| fun () -> x

let check ~ctxt ~msg seq list =
  let input = List.init 20 ~f:Fn.id in
  let r1, s1 = State.run (seq (Sequence.of_list input)) [] in
  let r2, s2 = State.run (list input) [] in
  let printer xs = List.map xs ~f:Int.to_string |> String.concat ~sep:" " in
  assert_equal ~ctxt ~msg:(msg ^ ": result") ~printer r2 (Sequence.to_list r1);
  assert_equal ~ctxt ~msg:(msg ^ ": effects") ~printer s2 s1

let map ctxt =
  check ~ctxt ~msg:"map"
    (State.Seq.map ~f:(fun x -> visit (x * 2)))
    (State.List.map ~f:(fun x -> visit (x * 2)))

let all ctxt =
  check ~ctxt ~msg:"all"
    (fun xs -> State.Seq.all (Sequence.map xs ~f:visit))
    (fun xs -> State.List.all (List.map xs ~f:visit))

let filter_map ctxt =
  let f x = visit x >>| fun x -> Option.some_if (x % 3 = 0) (x + 1) in
  check ~ctxt ~msg:"filter_map" (State.Seq.filter_map ~f)
    (State.List.filter_map ~f)

let filter ctxt =
  let f x = visit x >>| fun x -> x % 2 = 0 in
  check ~ctxt ~msg:"filter" (State.Seq.filter ~f) (State.List.filter ~f)

(* each element of the result used to be nested in the previous one,
   which made taking the elements quadratic and could exhaust the
   stack *)
let long ctxt =
  let n = 200_000 in
  let xs = Sequence.init n ~f:State.return in
  let r = State.eval (State.Seq.all xs) () in
  assert_equal ~ctxt ~printer:Int.to_string
    (n * (n - 1) / 2)
    (Sequence.fold r ~init:0 ~f:( + ))

let suite =
  "Monads"
  >::: [
         "Seq.map" >:: map;
         "Seq.all" >:: all;
         "Seq.filter_map" >:: filter_map;
         "Seq.filter" >:: filter;
         "Seq.all of a long sequence" >:: long;
       ]

let () = run_test_tt_main suite
