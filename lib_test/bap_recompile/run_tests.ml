open Core
open Bap.Std
open OUnit2

let block jmps = Blk.create ~jmps ()
let sub name blks = Sub.create ~name ~blks ()
let goto tid = Jmp.create_goto (Direct tid)
let ret tid = Jmp.create_ret (Direct tid)

let call ?return target =
  Jmp.create_call (Call.create ?return ~target:(Direct target) ())

let with_controlled_opt ir f =
  let key = "BAP_RECOMPILE_TEST_OUTPUT" in
  let previous = Sys.getenv key in
  Caml_unix.putenv key ir;
  Fun.protect
    ~finally:(fun () ->
      match previous with
      | Some value -> Caml_unix.putenv key value
      | None -> Caml_unix.unsetenv key)
    (fun () -> f (Sys.getenv_exn "BAP_RECOMPILE_TEST_OPT"))

let optimize ir sub =
  with_controlled_opt ir (fun opt -> Bap_recompile.optimize ~opt sub)

let deflatten ir sub =
  with_controlled_opt ir (fun opt -> Bap_recompile.deflatten ~opt ~rounds:1 sub)

let assert_error_contains expected = function
  | Ok _ -> assert_failure "the malformed subroutine was accepted"
  | Error err ->
      assert_bool "the error doesn't name the source and destination"
        (String.is_substring (Error.to_string_hum err) ~substring:expected)

let test_unknown_successor _ =
  let source =
    sub "malformed"
      [ block [ Jmp.create_ret (Indirect (Bil.int (Word.zero 64))) ] ]
  in
  let ir = "define void @f0() {\nentry:\n  br label %missing\n}\n" in
  assert_error_contains "no successor missing from entry" (deflatten ir source)

let tids sub = Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence

let jmps sub =
  Term.enum blk_t sub |> Seq.concat_map ~f:(Term.enum jmp_t) |> Seq.to_list

let test_valid_destinations _ =
  let first = Tid.create ()
  and second = Tid.create ()
  and third = Tid.create () in
  let callee = Tid.create () and external_ret = Tid.create () in
  let source =
    sub "valid"
      [
        block [ goto first ];
        Blk.create ~tid:first ~jmps:[ call callee; goto second ] ();
        Blk.create ~tid:second ~jmps:[ call ~return:(Direct third) callee ] ();
        Blk.create ~tid:third ~jmps:[ ret external_ret ] ();
      ]
  in
  let ir =
    "define void @f0() {\n\
     entry:\n\
    \  br label %first\n\
     first:\n\
    \  call void @f0.exit.0()\n\
    \  br label %second\n\
     second:\n\
    \  call void @f0.exit.1()\n\
    \  br label %third\n\
     third:\n\
    \  call void @f0.exit.2()\n\
    \  unreachable\n\
     }\n"
  in
  match deflatten ir source with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized ->
      let output = tids optimized in
      let jumps = jmps optimized in
      assert_bool "the direct internal edge is missing"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Goto (Direct tid) -> Set.mem output tid
             | _ -> false));
      assert_bool "the call fallthrough is missing"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Call call -> Option.is_none (Call.return call)
             | _ -> false));
      assert_bool "the call return is missing"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Call call -> (
                 match Call.return call with
                 | Some (Direct tid) -> Set.mem output tid
                 | _ -> false)
             | _ -> false));
      assert_bool "the external return is missing"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Call call -> (
                 match (Call.return call, Call.target call) with
                 | None, Direct tid -> Tid.equal tid external_ret
                 | _ -> false)
             | _ -> false))

let test_external_boundary _ =
  let external_goto = Tid.create ()
  and external_ret = Tid.create ()
  and external_int = Tid.create () in
  let source =
    sub "external"
      [
        block [ goto external_goto ];
        block [ ret external_ret ];
        block [ Jmp.create_int 8 external_int ];
      ]
  in
  let ir =
    "define void @f0() {\n\
     entry:\n\
    \  call void @f0.exit.0()\n\
    \  unreachable\n\
     ret:\n\
    \  call void @f0.exit.1()\n\
    \  unreachable\n\
     interrupt:\n\
    \  call void @f0.exit.2()\n\
    \  br label %int_cont\n\
     int_cont:\n\
    \  unreachable\n\
     }\n"
  in
  match deflatten ir source with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized ->
      let jumps = jmps optimized in
      assert_bool "the external goto was rejected"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Goto (Direct tid) -> Tid.equal tid external_goto
             | _ -> false));
      assert_bool "the external ret was rejected"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with
             | Call call -> (
                 match (Call.return call, Call.target call) with
                 | None, Direct tid -> Tid.equal tid external_ret
                 | _ -> false)
             | _ -> false));
      assert_bool "the interrupt return is missing"
        (List.exists jumps ~f:(fun jmp ->
             match Jmp.kind jmp with Int _ -> true | _ -> false))

let test_lost_opaque_exit _ =
  let source = sub "lost-exit" [ block [ call (Tid.create ()) ] ] in
  let ir = "define void @f0() {\nentry:\n  unreachable\n}\n" in
  assert_error_contains "changed opaque exits (1 before, 0 after)"
    (optimize ir source)

let test_duplicated_opaque_exit _ =
  let source = sub "duplicated-exit" [ block [ call (Tid.create ()) ] ] in
  let ir =
    "define void @f0() {\n\
     entry:\n\
    \  call void @f0.exit.0()\n\
    \  call void @f0.exit.0()\n\
    \  unreachable\n\
     }\n"
  in
  assert_error_contains "changed opaque exits (1 before, 2 after)"
    (deflatten ir source)

let test_altered_opaque_exit _ =
  let source =
    sub "altered-exit"
      [ block [ goto (Tid.create ()) ]; block [ ret (Tid.create ()) ] ]
  in
  let ir =
    "define void @f0() {\nentry:\n  call void @f0.exit.1()\n  unreachable\n}\n"
  in
  assert_error_contains "changed opaque exits (2 before, 1 after)"
    (optimize ir source)

let test_opaque_exit_attributes _ =
  let target = Tid.create () in
  let marked = Term.set_attr (call target) Term.dead () in
  let source = sub "exit-attributes" [ block [ marked ] ] in
  let ir =
    "define void @f0() {\nentry:\n  call void @f0.exit.0()\n  unreachable\n}\n"
  in
  match optimize ir source with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized -> (
      match jmps optimized with
      | [ jmp ] ->
          assert_bool "the opaque exit lost its attributes"
            (Term.has_attr jmp Term.dead);
          assert_bool "the opaque exit changed its target"
            (match Jmp.kind jmp with
            | Call call -> (
                match Call.target call with
                | Direct tid -> Tid.equal tid target
                | Indirect _ -> false)
            | _ -> false)
      | _ ->
          assert_failure "the valid opaque exit wasn't preserved exactly once")

let suite =
  "recompile"
  >::: [
         "unknown successor" >:: test_unknown_successor;
         "valid destinations" >:: test_valid_destinations;
         "external boundary" >:: test_external_boundary;
         "lost opaque exit" >:: test_lost_opaque_exit;
         "duplicated opaque exit" >:: test_duplicated_opaque_exit;
         "altered opaque exit" >:: test_altered_opaque_exit;
         "opaque exit attributes" >:: test_opaque_exit_attributes;
       ]

let () = run_test_tt_main suite
