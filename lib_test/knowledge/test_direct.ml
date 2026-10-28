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

(* a direct-style promise is awaited in another direct computation *)
let reentrant _ =
  let w = int "w" in
  Knowledge.promise w (fun obj ->
      Knowledge.direct @@ fun () ->
      Option.map (Knowledge.await (Knowledge.collect x obj)) ~f:(fun v -> v + 1));
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.provide x obj (Some 1));
    Knowledge.await (Knowledge.collect w obj)
  in
  assert_equal ~printer:opt (Some 2) r

(* a rejected proposal is the same as no opinion, so it doesn't shadow the
   opinions of the less reliable agents *)
let proposal _ =
  let agent reliability name =
    Knowledge.Agent.register ~package ~reliability name
  in
  let slot =
    Knowledge.Class.property ~package cls "opinion"
      (Knowledge.Domain.opinions ~empty:0 ~equal:Int.equal "opinion")
  in
  Knowledge.propose (agent Knowledge.Agent.authorative "authority") slot
    (fun obj ->
      Knowledge.direct @@ fun () ->
      Knowledge.await_some (Knowledge.collect x obj) * 100);
  Knowledge.propose (agent Knowledge.Agent.doubtful "doubter") slot (fun _ ->
      Knowledge.direct @@ fun () -> 5);
  let r = eval @@ fun obj -> Knowledge.resolve slot obj in
  assert_equal ~printer:Int.to_string 5 r;
  let r =
    eval @@ fun obj ->
    Knowledge.provide x obj (Some 2) >>= fun () -> Knowledge.resolve slot obj
  in
  assert_equal ~printer:Int.to_string 200 r

(* the objects that a direct computation creates stay in the state *)
let objects _ =
  let r =
    eval @@ fun _ ->
    ( Knowledge.direct @@ fun () ->
      let obj = Knowledge.await (Knowledge.Object.create cls) in
      Knowledge.await (Knowledge.provide x obj (Some 8));
      obj )
    >>= fun obj -> Knowledge.collect x obj
  in
  assert_equal ~printer:opt (Some 8) r

(* the conflicts of a direct computation are caught outside of it *)
let caught_outside _ =
  let r =
    eval @@ fun _ ->
    Knowledge.catch
      ( Knowledge.direct @@ fun () ->
        ignore (Knowledge.await (Knowledge.fail Bad));
        0 )
      (function Bad -> !!9 | other -> Knowledge.fail other)
  in
  assert_equal ~printer:Int.to_string 9 r

(* the callbacks of the knowledge functions need their own direct *)
let callback _ =
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    Knowledge.await (Knowledge.provide x obj (Some 3));
    let sum = ref 0 in
    Knowledge.await
    @@ Knowledge.List.iter [ 1; 2; 3 ] ~f:(fun i ->
        Knowledge.direct @@ fun () ->
        sum := !sum + (i * Knowledge.await_some (Knowledge.collect x obj)));
    !sum
  in
  assert_equal ~printer:Int.to_string 18 r

(* the effects and the side effects happen in the order of the program *)
let order _ =
  let log = ref [] in
  let say s = log := s :: !log in
  let r =
    eval @@ fun obj ->
    Knowledge.direct @@ fun () ->
    say "a";
    Knowledge.await (Knowledge.provide x obj (Some 1) >>| fun () -> say "b");
    say "c";
    let v =
      Knowledge.await
        ( Knowledge.collect x obj >>| fun v ->
          say "d";
          v )
    in
    say "e";
    v
  in
  assert_equal ~printer:opt (Some 1) r;
  assert_equal ~printer:(String.concat ~sep:" ")
    [ "a"; "b"; "c"; "d"; "e" ]
    (List.rev !log)

let imports _ =
  let r =
    eval @@ fun _ ->
    Knowledge.Symbol.intern ~public:true ~package:"foo" "main" cls
    >>= fun original ->
    Knowledge.provide x original (Some 42) >>= fun () ->
    Knowledge.Symbol.import ~package:"bar" [ "foo" ] >>= fun () ->
    Knowledge.Symbol.in_package "bar" (fun () ->
        Knowledge.Symbol.intern "main" cls)
    >>= fun imported -> Knowledge.collect x imported
  in
  assert_equal ~printer:opt (Some 42) r

(* the recursion of the direct functions, e.g., over the instructions of a
   stub, is as deep as in the monadic style *)
let deep _ =
  let rec sum n = if n = 0 then 0 else Knowledge.await !!n + sum (n - 1) in
  let rec nest n =
    if n = 0 then 0
    else Knowledge.await (Knowledge.direct @@ fun () -> nest (n - 1)) + 1
  in
  let r =
    eval @@ fun _ ->
    Knowledge.direct @@ fun () -> (sum 10_000, nest 1_000)
  in
  assert_equal (50_005_000, 1_000) r

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
           "reentrant" >:: reentrant;
           "proposal" >:: proposal;
           "objects" >:: objects;
           "caught-outside" >:: caught_outside;
           "callback" >:: callback;
           "order" >:: order;
           "imports" >:: imports;
           "deep" >:: deep;
         ])
