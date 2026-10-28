open Core
open Bap.Std
module Ast = Decompile_ast
module Cfg = Decompile_cfg

let always exp =
  match exp with Bil.Int value -> Word.is_one value | _ -> false

let rec referenced_gotos statements =
  List.fold statements ~init:String.Set.empty ~f:(fun labels stmt ->
      let nested = function
        | Ast.If (_, yes, no) -> referenced_gotos (yes @ no)
        | Ast.While (_, body) | Ast.Do_while (body, _) -> referenced_gotos body
        | Ast.Switch (_, cases, default) ->
            referenced_gotos
              (List.concat_map cases ~f:snd @ Option.value default ~default:[])
        | _ -> String.Set.empty
      in
      match stmt with
      | Ast.Goto label -> Set.add labels label
      | _ -> Set.union labels (nested stmt))

let remove_unused_labels statements =
  let labels = referenced_gotos statements in
  List.filter statements ~f:(function
    | Ast.Label label -> Set.mem labels label
    | _ -> true)

let structure cfg ~block:emit_block ~edge:emit_edge ~call:emit_call ~condition =
  let emitted = Tid.Hash_set.create () in
  let block_prefix tid =
    let label = Ast.Label (Cfg.label tid) in
    match Cfg.block cfg tid with
    | None -> [ label ]
    | Some blk ->
        let statements = emit_block blk in
        (label :: statements) @ List.concat_map (Cfg.calls cfg tid) ~f:emit_call
  in
  let post_test = ref None in
  let rec sequence active stop context tid =
    if Tid.equal tid stop || Cfg.is_exit cfg tid || not (Set.mem active tid)
    then []
    else if Hash_set.mem emitted tid then [ Ast.Goto (Cfg.label tid) ]
    else
      match Cfg.loop_at cfg tid with
      | Some loop when Set.is_subset loop.nodes ~of_:active ->
          emit_loop active stop context loop
      | _ -> emit_node active stop context tid
  and transfer active stop context (edge : Cfg.edge) =
    let prefix = emit_edge edge in
    if Cfg.is_exit cfg edge.dst then prefix
    else if Tid.equal edge.dst stop then prefix
    else
      match context with
      | Some loop when Tid.equal edge.dst loop.Cfg.header ->
          prefix @ [ Ast.Continue ]
      | Some loop when not (Set.mem loop.Cfg.nodes edge.dst) ->
          prefix @ [ Ast.Break ]
      | _ -> prefix @ sequence active stop context edge.dst
  and guarded tid raw_condition statements =
    if always raw_condition then statements
    else [ Ast.If (condition tid raw_condition, statements, []) ]
  and raw active stop context start =
    let rec gather pending nodes =
      match pending with
      | [] -> nodes
      | tid :: rest ->
          if
            Tid.equal tid stop || Cfg.is_exit cfg tid
            || (not (Set.mem active tid))
            || Set.mem nodes tid
          then gather rest nodes
          else
            let pending =
              List.fold (Cfg.successors cfg tid) ~init:rest ~f:(fun rest edge ->
                  edge.Cfg.dst :: rest)
            in
            gather pending (Set.add nodes tid)
    in
    let nodes = gather [ start ] Tid.Set.empty in
    Set.iter nodes ~f:(Hash_set.add emitted);
    let body =
      Set.to_list nodes
      |> List.concat_map ~f:(fun tid ->
          block_prefix tid
          @ List.concat_map (Cfg.successors cfg tid) ~f:(fun edge ->
              let jump = emit_edge edge in
              let jump =
                if Cfg.is_exit cfg edge.dst then jump
                else jump @ [ Ast.Goto (Cfg.label edge.dst) ]
              in
              guarded tid edge.Cfg.condition jump))
    in
    body @ sequence active stop context stop
  and emit_node active stop context tid =
    Hash_set.add emitted tid;
    let prefix = block_prefix tid in
    match !post_test with
    | Some (latch, back, _) when Tid.equal tid latch -> prefix @ emit_edge back
    | _ -> (
        match Cfg.successors cfg tid with
        | [] -> prefix
        | [ edge ] -> prefix @ transfer active stop context edge
        | [ first; second ]
          when (not (always first.Cfg.condition)) && always second.Cfg.condition
          -> (
            match Cfg.join cfg first.dst second.dst with
            | Some join ->
                let yes = transfer active join context first in
                let no = transfer active join context second in
                prefix
                @ [ Ast.If (condition tid first.condition, yes, no) ]
                @ sequence active stop context join
            | None -> raw active stop context tid)
        | edges -> (
            match switch_region active stop context prefix tid edges with
            | Some statements -> statements
            | None -> raw active stop context tid))
  and switch_region active stop context prefix tid edges =
    let rec value_of condition =
      match condition with
      | Bil.BinOp (EQ, exp, Bil.Int value) | Bil.BinOp (EQ, Bil.Int value, exp)
        ->
          Some (exp, value)
      | _ -> None
    in
    match List.last edges with
    | Some default when always default.Cfg.condition -> (
        let cases = List.drop_last_exn edges in
        let parsed =
          List.map cases ~f:(fun edge -> value_of edge.Cfg.condition)
        in
        if
          List.length cases < 2
          || List.exists parsed ~f:Option.is_none
          || List.exists edges ~f:(fun edge -> Cfg.is_exit cfg edge.dst)
        then None
        else
          let value = fst (Option.value_exn (List.hd_exn parsed)) in
          if
            List.exists parsed ~f:(fun item ->
                let exp, _ = Option.value_exn item in
                not (Exp.equal value exp))
          then None
          else
            let join =
              List.fold edges ~init:(Some (List.hd_exn edges).Cfg.dst)
                ~f:(fun join edge ->
                  Option.bind join ~f:(fun join -> Cfg.join cfg join edge.dst))
            in
            match join with
            | None -> None
            | Some join ->
                let cases =
                  List.map2_exn cases parsed ~f:(fun edge item ->
                      let _, value = Option.value_exn item in
                      let body = transfer active join context edge in
                      (value, body @ [ Ast.Break ]))
                in
                let default_body = transfer active join context default in
                Some
                  (prefix
                  @ [
                      Ast.Switch (condition tid value, cases, Some default_body);
                    ]
                  @ sequence active stop context join))
    | _ -> None
  and emit_loop active stop outer loop =
    let tid = loop.Cfg.header in
    let context = Some loop in
    let post =
      Set.to_list loop.Cfg.latches
      |> List.find_map ~f:(fun latch ->
          match Cfg.successors cfg latch with
          | [ first; second ] -> (
              let candidate (back : Cfg.edge) (exit_edge : Cfg.edge) =
                if
                  Tid.equal back.Cfg.dst loop.header
                  && (not (always back.Cfg.condition))
                  && always exit_edge.Cfg.condition
                then Some (latch, back, exit_edge)
                else None
              in
              match candidate first second with
              | Some _ as result -> result
              | None -> candidate second first)
          | _ -> None)
    in
    match post with
    | Some (latch, back, exit_edge) ->
        Hash_set.add emitted tid;
        let previous = !post_test in
        post_test := Some (latch, back, exit_edge);
        let body = emit_node loop.nodes loop.header context tid in
        post_test := previous;
        [ Ast.Do_while (body, condition latch back.condition) ]
        @ emit_edge exit_edge
        @ sequence active stop outer exit_edge.dst
    | None -> (
        Hash_set.add emitted tid;
        let prefix = block_prefix tid in
        let is_inside (edge : Cfg.edge) =
          Set.mem loop.nodes edge.dst && not (Tid.equal edge.dst loop.header)
        in
        match Cfg.successors cfg tid with
        | [ first; second ] -> (
            let candidate (conditional : Cfg.edge) (fallthrough : Cfg.edge) =
              if
                (not (always conditional.Cfg.condition))
                && always fallthrough.Cfg.condition
              then
                if is_inside conditional && not (is_inside fallthrough) then
                  Some (conditional, fallthrough, conditional.condition, true)
                else if is_inside fallthrough && not (is_inside conditional)
                then
                  Some (fallthrough, conditional, conditional.condition, false)
                else None
              else None
            in
            let selected =
              match candidate first second with
              | Some _ as result -> result
              | None -> candidate second first
            in
            match selected with
            | Some (body_edge, exit_edge, raw_test, body_on_true) ->
                let body = transfer loop.nodes loop.header context body_edge in
                let branch_condition = condition tid raw_test in
                let test =
                  if body_on_true then branch_condition
                  else
                    {
                      branch_condition with
                      Ast.node = Ast.Unary ("!", branch_condition);
                    }
                in
                let loop_stmt =
                  if List.length prefix = 1 then Ast.While (test, body)
                  else
                    let yes, no =
                      if body_on_true then ([], [ Ast.Break ])
                      else ([ Ast.Break ], [])
                    in
                    Ast.While
                      ( condition tid (Bil.Int Word.b1),
                        prefix @ [ Ast.If (branch_condition, yes, no) ] @ body
                      )
                in
                [ loop_stmt ] @ emit_edge exit_edge
                @ sequence active stop outer exit_edge.dst
            | _ -> raw active stop context tid)
        | _ -> raw active stop context tid)
  in
  let active = Cfg.nodes cfg in
  let statements = sequence active (Cfg.exit cfg) None (Cfg.entry cfg) in
  remove_unused_labels statements
