open Core
open OUnit2
open Bap_knowledge
open Knowledge.Syntax

let opt = function None -> "None" | Some x -> Int.to_string x
let package = "test-direct"
let cls = Knowledge.Class.declare ~package "test" ()

let int name =
  Knowledge.Class.property ~package cls name
    (Knowledge.Domain.optional ~equal:Int.equal "int")

let x = int "x"
let y = int "y"
let z = int "z"

type Knowledge.conflict += Bad

(* evaluates [k] for a fresh object, the result is the state *)
let eval k =
  let result = ref None in
  let obj =
    Knowledge.Object.create cls >>= fun obj ->
    k obj >>| fun r ->
    result := Some r;
    obj
  in
  match Knowledge.run cls obj Knowledge.empty with
  | Ok _ -> Option.value_exn !result
  | Error conflict -> assert_failure (Knowledge.Conflict.to_string conflict)

let fails k =
  let obj =
    Knowledge.Object.create cls >>= fun obj ->
    k obj >>| fun _ -> obj
  in
  match Knowledge.run cls obj Knowledge.empty with
  | Ok _ -> None
  | Error conflict -> Some conflict

let sequence _ =
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.provide x obj (Some 1));
    let v = Knowledge.await (Knowledge.collect x obj) in
    Knowledge.await (Knowledge.provide y obj (Option.map v ~f:succ));
    Knowledge.await (Knowledge.collect y obj)
  in
  assert_equal ~printer:opt (Some 2) r

let promise _ =
  Knowledge.promise z (fun obj ->
      Knowledge.direct @@ fun () ->
      match Knowledge.await (Knowledge.collect x obj) with
      | Some v -> Some (v * 10)
      | None -> None);
  let r =
    eval @@ fun obj ->
    Knowledge.provide x obj (Some 4) >>= fun () -> Knowledge.collect z obj
  in
  assert_equal ~printer:opt (Some 40) r

let rejected _ =
  let finalized = ref false and after = ref false in
  let r =
    eval @@ fun obj ->
    Knowledge.with_empty ~missing:None @@ fun () ->
    Knowledge.direct @@ fun () ->
    Fun.protect ~finally:(fun () -> finalized := true) @@ fun () ->
    Knowledge.await (Knowledge.guard false);
    after := true;
    Knowledge.await (Knowledge.collect x obj)
  in
  assert_equal ~printer:opt None r;
  assert_bool "the finalizer runs" !finalized;
  assert_bool "the rest is aborted" (not !after)

let conflict _ =
  match
    fails @@ fun _ ->
    Knowledge.direct @@ fun () -> Knowledge.await (Knowledge.fail Bad)
  with
  | Some Bad -> ()
  | _ -> assert_failure "the conflict is lost"

let caught _ =
  let r =
    eval @@ fun _ ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.catch (Knowledge.fail Bad) (fun _ -> !!7))
  in
  assert_equal ~printer:Int.to_string 7 r

let nested _ =
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.provide x obj (Some 1));
    let inner =
      Knowledge.direct @@ fun () ->
      Knowledge.await (Knowledge.provide y obj (Some 2));
      Knowledge.await (Knowledge.collect x obj)
    in
    let v = Knowledge.await inner in
    (v, Knowledge.await (Knowledge.collect y obj))
  in
  assert_equal (Some 1, Some 2) r

let exn _ =
  assert_raises (Failure "boom") @@ fun () ->
  eval @@ fun obj ->
  Knowledge.direct @@ fun () ->
  ignore (Knowledge.await (Knowledge.collect x obj));
  failwith "boom"

let some _ =
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.provide x obj (Some 3));
    Knowledge.await_some (Knowledge.collect x obj)
  in
  assert_equal ~printer:Int.to_string 3 r;
  Knowledge.promise z (fun obj ->
      Knowledge.direct @@ fun () ->
      Some (Knowledge.await_some (Knowledge.collect y obj) + 1));
  let r = eval @@ fun obj -> Knowledge.collect z obj in
  assert_equal ~printer:opt None r

let unhandled _ =
  match Knowledge.await (Knowledge.return 1) with
  | _ -> assert_failure "await outside of direct"
  | exception Stdlib.Effect.Unhandled _ -> ()

let many _ =
  let n = 100_000 in
  let r =
    eval @@ fun _ ->
    Knowledge.direct @@ fun () ->
    let s = ref 0 in
    for i = 1 to n do
      s := !s + Knowledge.await (Knowledge.return i)
    done;
    !s
  in
  assert_equal ~printer:Int.to_string (n * (n + 1) / 2) r

let () =
  run_test_tt_main
    ("direct"
    >::: [
           "sequence" >:: sequence;
           "promise" >:: promise;
           "rejected" >:: rejected;
           "conflict" >:: conflict;
           "caught" >:: caught;
           "nested" >:: nested;
           "exn" >:: exn;
           "some" >:: some;
           "unhandled" >:: unhandled;
           "many" >:: many;
         ])
