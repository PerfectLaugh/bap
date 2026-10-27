open Core
open Bap.Std
open OUnit2

let block jmps = Blk.create ~jmps ()
let sub name blks = Sub.create ~name ~blks ()
let goto tid = Jmp.create_goto (Direct tid)

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

let dispatcher_ir =
  "define void @f0() {\n\
   entry:\n\
  \  br label %pred1\n\
   pred1:\n\
  \  br label %header\n\
   pred2:\n\
  \  br label %header\n\
   header:\n\
  \  %state = phi i32 [1, %pred1], [2, %pred2]\n\
  \  %cond = icmp eq i32 %state, 1\n\
  \  br i1 %cond, label %target, label %other\n\
   target:\n\
  \  %result = phi i32 [%state, %header]\n\
  \  unreachable\n\
   other:\n\
  \  unreachable\n\
   }\n"

let dispatcher_source () =
  let loop = Tid.create () in
  sub "dispatcher"
    [ block [ goto loop ]; Blk.create ~tid:loop ~jmps:[ goto loop ] () ]

let test_lean_dispatcher _ =
  let source = dispatcher_source () and calls = ref 0 and threads = ref 0 in
  let validate before after =
    incr calls;
    match Bap_bil_plugin.Bil_lean.validate_exp before after with
    | Ok () -> true
    | Error message -> failwith message
  in
  let validate_thread witness =
    incr threads;
    match Bap_recompile.validate_thread witness with
    | Ok () -> true
    | Error message -> failwith message
  in
  match
    with_controlled_opt dispatcher_ir (fun opt ->
        Bap_recompile.deflatten ~opt ~rounds:1 ~validate ~validate_thread source)
  with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized ->
      assert_bool "the dispatcher wasn't threaded"
        (Term.length blk_t optimized > Term.length blk_t source);
      assert_bool "no Lean expression proof was checked" (!calls > 0);
      assert_bool "no Lean CFG proof was checked" (!threads > 0)

let select_ir =
  "define void @f0() {\n\
   entry:\n\
  \  br label %pred1\n\
   pred1:\n\
  \  %cond = icmp eq i32 %x, 0\n\
  \  %state = select i1 %cond, i32 1, i32 2\n\
  \  br label %header\n\
   pred2:\n\
  \  br label %header\n\
   header:\n\
  \  %state = phi i32 [%state, %pred1], [2, %pred2]\n\
  \  %cond = icmp eq i32 %state, 1\n\
  \  br i1 %cond, label %target, label %other\n\
   target:\n\
  \  %result = phi i32 [%state, %header]\n\
  \  unreachable\n\
   other:\n\
  \  unreachable\n\
   }\n"

let test_lean_select _ =
  let source = dispatcher_source () and splits = ref 0 in
  let validate_thread witness =
    match Bap_recompile.validate_thread witness with
    | Ok () -> true
    | Error message -> failwith message
  in
  let validate_split witness =
    incr splits;
    match Bap_recompile.validate_split witness with
    | Ok () -> true
    | Error message -> failwith message
  in
  match
    with_controlled_opt select_ir (fun opt ->
        Bap_recompile.deflatten ~opt ~rounds:1 ~validate_thread ~validate_split
          source)
  with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized ->
      assert_bool "the symbolic dispatcher wasn't threaded"
        (Term.length blk_t optimized > Term.length blk_t source);
      assert_bool "no Lean split proof was checked" (!splits > 0)

let reject_mutation mutate =
  let source = dispatcher_source ()
  and calls = ref 0
  and accepted = ref false in
  let validate_thread witness =
    incr calls;
    let witness = mutate witness in
    match Bap_recompile.validate_thread witness with
    | Ok () ->
        accepted := true;
        true
    | Error message -> failwith message
  in
  ignore
    (with_controlled_opt dispatcher_ir (fun opt ->
         Bap_recompile.deflatten ~opt ~rounds:1 ~validate_thread source));
  assert_bool "the mutated witness wasn't checked" (!calls > 0);
  assert_bool "Lean accepted a mutated witness" (not !accepted)

let test_wrong_destination _ =
  reject_mutation (fun witness ->
      let header =
        List.find_exn witness.blocks ~f:(fun block ->
            String.equal block.label "other")
      in
      { witness with header })

let test_wrong_definition _ =
  reject_mutation (fun witness ->
      let open Bap_recompile.Recompile_optimize.Parse in
      let temp = Var.create ~fresh:true "definition" (Type.imm 32) in
      let value = Word.of_int ~width:32 7 in
      let wrong = Word.of_int ~width:32 8 in
      let blocks =
        List.map witness.blocks ~f:(fun block ->
            if String.equal block.label witness.header.label then
              {
                block with
                items = block.items @ [ Assign (temp, Bil.Int value) ];
              }
            else block)
      in
      let edge =
        {
          witness.edge with
          items = witness.edge.items @ [ Assign (temp, Bil.Int wrong) ];
        }
      in
      {
        witness with
        blocks;
        edge;
        env = Map.set witness.env ~key:temp ~data:value;
      })

let test_unbound_input _ =
  reject_mutation (fun witness ->
      let state = Var.create ~fresh:true "unbound" (Var.typ witness.state) in
      let blocks =
        List.map witness.blocks ~f:(fun block ->
            if String.equal block.label witness.header.label then
              { block with phis = [] }
            else block)
      in
      { witness with blocks; state })

let reject_split_mutation mutate =
  let source = dispatcher_source ()
  and calls = ref 0
  and accepted = ref false in
  let validate_split witness =
    incr calls;
    let witness = mutate witness in
    match Bap_recompile.validate_split witness with
    | Ok () ->
        accepted := true;
        true
    | Error message -> failwith message
  in
  ignore
    (with_controlled_opt select_ir (fun opt ->
         Bap_recompile.deflatten ~opt ~rounds:1 ~validate_split source));
  assert_bool "the mutated split wasn't checked" (!calls > 0);
  assert_bool "Lean accepted a mutated split" (not !accepted)

let test_swapped_split _ =
  reject_split_mutation (fun witness ->
      let open Bap_recompile.Recompile_optimize.Parse in
      {
        witness with
        split =
          {
            witness.split with
            terminator =
              Cbr
                ( witness.condition,
                  witness.right.edge.label,
                  witness.left.edge.label );
          };
      })

let test_split_wrong_definition _ =
  reject_split_mutation (fun witness ->
      let open Bap_recompile.Recompile_optimize.Parse in
      let temp = Var.create ~fresh:true "split-definition" (Type.imm 32) in
      let value = Word.of_int ~width:32 7 in
      let wrong = Word.of_int ~width:32 8 in
      let left = witness.left in
      let blocks =
        List.map left.blocks ~f:(fun block ->
            if String.equal block.label left.header.label then
              {
                block with
                items = block.items @ [ Assign (temp, Bil.Int value) ];
              }
            else block)
      in
      let edge =
        {
          left.edge with
          items = left.edge.items @ [ Assign (temp, Bil.Int wrong) ];
        }
      in
      let left =
        { left with blocks; edge; env = Map.set left.env ~key:temp ~data:value }
      in
      { witness with left })

let test_split_unbound_input _ =
  reject_split_mutation (fun witness ->
      let open Bap_recompile.Recompile_optimize.Parse in
      let temp = Var.create ~fresh:true "split-unbound-result" (Type.imm 32) in
      let unbound =
        Var.create ~fresh:true "split-unbound-input" (Type.imm 32)
      in
      let value = Word.of_int ~width:32 7 in
      let left = witness.left in
      let blocks =
        List.map left.blocks ~f:(fun block ->
            if String.equal block.label left.header.label then
              {
                block with
                items = block.items @ [ Assign (temp, Bil.Var unbound) ];
              }
            else block)
      in
      let left =
        { left with blocks; env = Map.set left.env ~key:temp ~data:value }
      in
      { witness with left })

let test_lean_mba _ =
  let var name = Bil.var (Var.create name (Type.imm 8)) in
  let x = var "x" and y = var "y" in
  let bin op left right = Bil.BinOp (op, left, right) in
  let before =
    bin Bil.PLUS (bin Bil.XOR x y)
      (bin Bil.TIMES (Bil.int (Word.of_int ~width:8 2)) (bin Bil.AND x y))
  in
  let unchecked = Bap_recompile.simplify_exp before |> Or_error.ok_exn in
  match Bap_recompile.simplify_exp_checked before with
  | Error error ->
      assert_failure
        (Format.asprintf "%s@.before: %a@.after: %a"
           (Error.to_string_hum error)
           Exp.pp before Exp.pp unchecked)
  | Ok after ->
      assert_bool "MBA addition wasn't simplified" (Exp.equal after unchecked)

let test_lean_shift_and_copy _ =
  let typ = Type.imm 8 in
  let x = Bil.var (Var.create "x" typ) in
  let word value = Bil.int (Word.of_int ~width:8 value) in
  let bin op left right = Bil.BinOp (op, left, right) in
  let shifted = bin Bil.LSHIFT x (word 1) in
  (match Bap_recompile.simplify_exp_checked (bin Bil.PLUS x shifted) with
  | Error error -> assert_failure (Error.to_string_hum error)
  | Ok after ->
      assert_bool "shift/add wasn't proved"
        (Exp.equal after (bin Bil.TIMES x (word 3))));
  let temp name = Var.create ~fresh:true ~is_virtual:true name typ in
  let t1 = temp "t1" and t2 = temp "t2" and out = temp "out" in
  let blk =
    Blk.create
      ~defs:
        [
          Def.create t1 x;
          Def.create t2 (bin Bil.PLUS (Bil.var t1) (word 1));
          Def.create out (Bil.var t2);
        ]
      ()
  in
  match Bap_recompile.Recompile_mba.simplify_blk_checked blk with
  | Error error -> assert_failure (Error.to_string_hum error)
  | Ok after ->
      let defs = Term.enum def_t after |> Seq.to_list in
      assert_bool "copy propagation wasn't proved"
        (Exp.equal (Def.rhs (List.nth_exn defs 2)) (bin Bil.PLUS x (word 1)))

let test_lean_mba_dispatcher _ =
  let source = dispatcher_source () and threads = ref 0 in
  let validate_thread witness =
    incr threads;
    match Bap_recompile.validate_thread witness with
    | Ok () -> true
    | Error message -> failwith message
  in
  match
    with_controlled_opt dispatcher_ir (fun opt ->
        Bap_recompile.deflatten ~opt ~rounds:1 ~mba:Bap_recompile.Checked
          ~validate_thread source)
  with
  | Error err -> assert_failure (Error.to_string_hum err)
  | Ok optimized ->
      assert_bool "the MBA-preprocessed dispatcher wasn't threaded"
        (Term.length blk_t optimized > Term.length blk_t source);
      assert_bool "no CFG proof followed MBA simplification" (!threads > 0)

let () =
  run_test_tt_main
    ("recompile_lean"
    >::: [
           "MBA expression" >:: test_lean_mba;
           "MBA shift and copy" >:: test_lean_shift_and_copy;
           "MBA dispatcher" >:: test_lean_mba_dispatcher;
           "dispatcher" >:: test_lean_dispatcher;
           "select" >:: test_lean_select;
           "swapped split" >:: test_swapped_split;
           "split wrong definition" >:: test_split_wrong_definition;
           "split unbound input" >:: test_split_unbound_input;
           "wrong destination" >:: test_wrong_destination;
           "wrong definition" >:: test_wrong_definition;
           "unbound input" >:: test_unbound_input;
         ])
