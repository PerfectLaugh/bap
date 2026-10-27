open Core
open Bap.Std
open Bap_core_theory
module Recompile_optimize = Recompile_optimize

let deflatten_passes =
  "function(sroa,early-cse,instcombine<no-verify-fixpoint>,sccp,simplifycfg,jump-threading,simplifycfg,sccp,instcombine<no-verify-fixpoint>,gvn,dse,adce,simplifycfg)"

let default_passes =
  "function(sroa,early-cse,instcombine<no-verify-fixpoint>,simplifycfg,sccp,gvn,dse,adce,jump-threading,instcombine<no-verify-fixpoint>,simplifycfg)"

(* the optimized subs by the pipeline and the text of the sub, which has
   its identifiers, so that the same sub is optimized once *)
let cache : sub term Or_error.t String.Table.t = String.Table.create ()

let key ?target ~expression_validated ~thread_validated ~split_validated passes
    sub =
  let target =
    Option.value_map target ~default:"" ~f:(fun t ->
        KB.Name.show (Theory.Target.name t))
  in
  String.concat ~sep:"\n"
    [
      target;
      passes;
      Bool.to_string expression_validated;
      Bool.to_string thread_validated;
      Bool.to_string split_validated;
      Sub.to_string sub;
    ]

let has_code sub =
  not (Recompile_llvm.is_external sub || Recompile_llvm.is_intrinsic sub)

let direct_destinations jmp =
  let direct = function Some (Direct tid) -> [ tid ] | _ -> [] in
  match Jmp.kind jmp with
  | Goto label | Ret label -> direct (Some label)
  | Call call -> direct (Call.return call)
  | Int (_, tid) -> [ tid ]

let external_boundary sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:Tid.Set.empty ~f:(fun boundary blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:boundary ~f:(fun boundary jmp ->
          List.fold (direct_destinations jmp) ~init:boundary
            ~f:(fun boundary tid ->
              if Set.mem blocks tid then boundary else Set.add boundary tid)))

let validate_destinations ~boundary sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:(Ok ()) ~f:(fun result blk ->
      Result.bind result ~f:(fun () ->
          Term.enum jmp_t blk
          |> Seq.fold ~init:(Ok ()) ~f:(fun result jmp ->
              Result.bind result ~f:(fun () ->
                  List.fold (direct_destinations jmp) ~init:(Ok ())
                    ~f:(fun result tid ->
                      Result.bind result ~f:(fun () ->
                          if Set.mem blocks tid || Set.mem boundary tid then
                            Ok ()
                          else
                            Or_error.errorf
                              "the sub %s has the jump %s in the block %s to \
                               the missing destination %s"
                              (Sub.name sub)
                              (Tid.to_string (Term.tid jmp))
                              (Tid.to_string (Term.tid blk))
                              (Tid.to_string tid)))))))

let opaque_exits sub =
  let blocks =
    Term.enum blk_t sub |> Seq.map ~f:Term.tid |> Tid.Set.of_sequence
  in
  let internal tid = Set.mem blocks tid in
  let continuation = function
    | None -> "none"
    | Some (Direct tid) when internal tid -> "internal"
    | Some (Direct tid) -> "external:" ^ Tid.to_string tid
    | Some (Indirect _) -> "indirect"
  in
  let signature jmp =
    let kind =
      match Jmp.kind jmp with
      | Goto (Direct tid) when internal tid -> None
      | Goto (Direct tid) -> Some ("goto:" ^ Tid.to_string tid)
      | Goto (Indirect _) -> Some "goto:indirect"
      | Ret (Direct tid) when internal tid -> None
      | Ret (Direct tid) -> Some ("return:" ^ Tid.to_string tid)
      | Ret (Indirect _) -> Some "return:indirect"
      | Call call ->
          let target =
            match Call.target call with
            | Direct tid -> Tid.to_string tid
            | Indirect _ -> "indirect"
          in
          Some ("call:" ^ target ^ ":" ^ continuation (Call.return call))
      | Int (number, _) -> Some ("interrupt:" ^ Int.to_string number)
    in
    Option.map kind ~f:(fun kind ->
        kind ^ ":" ^ Sexp.to_string_mach (Dict.sexp_of_t (Term.attrs jmp)))
  in
  Term.enum blk_t sub
  |> Seq.fold ~init:String.Map.empty ~f:(fun exits blk ->
      Term.enum jmp_t blk
      |> Seq.fold ~init:exits ~f:(fun exits jmp ->
          match signature jmp with
          | None -> exits
          | Some signature ->
              Map.update exits signature ~f:(function
                | None -> 1
                | Some count -> count + 1)))

let validate_opaque_exits original optimized =
  let before = opaque_exits original and after = opaque_exits optimized in
  if Map.equal Int.equal before after then Ok ()
  else
    let total =
      Map.fold ~init:0 ~f:(fun ~key:_ ~data:count sum -> sum + count)
    in
    Or_error.errorf "the sub %s changed opaque exits (%d before, %d after)"
      (Sub.name original) (total before) (total after)

let validate_candidate original optimized =
  Result.bind
    (validate_destinations ~boundary:(external_boundary original) optimized)
    ~f:(fun () -> validate_opaque_exits original optimized)

let optimize_subs ?target ?(opt = "opt") ?(passes = default_passes) ?validate
    ?validate_thread ?validate_split subs =
  let key =
    key ?target ~expression_validated:(Option.is_some validate)
      ~thread_validated:(Option.is_some validate_thread)
      ~split_validated:(Option.is_some validate_split)
      passes
  in
  let cached, fresh =
    List.partition_map subs ~f:(fun sub ->
        match Hashtbl.find cache (key sub) with
        | Some result -> First (sub, result)
        | None -> Second sub)
  in
  let optimized =
    if List.is_empty fresh then []
    else
      Recompile_optimize.optimize_subs ?target ?validate ?validate_thread
        ?validate_split ~opt ~pipeline:passes fresh
  in
  let optimized =
    List.map optimized ~f:(fun (sub, result) ->
        let result =
          Result.bind result ~f:(fun optimized ->
              Result.map (validate_candidate sub optimized) ~f:(fun () ->
                  optimized))
        in
        (sub, result))
  in
  List.iter optimized ~f:(fun (sub, result) ->
      Hashtbl.set cache ~key:(key sub) ~data:result);
  cached @ optimized

let optimize ?target ?opt ?passes ?validate ?validate_thread ?validate_split sub
    =
  match
    optimize_subs ?target ?opt ?passes ?validate ?validate_thread
      ?validate_split [ sub ]
  with
  | [ (_, result) ] -> result
  | _ -> Or_error.error_string "the sub wasn't optimized"

module Region = struct
  type t = { blks : blk term list; replaces : Tid.Set.t }

  let blks t = t.blks
  let entry t = List.hd_exn t.blks

  (* the block ends, as its last jump is unconditional *)
  let ends blk =
    match Term.last jmp_t blk with
    | Some jmp -> (
        match Jmp.cond jmp with Int w -> Word.is_one w | _ -> false)
    | None -> false

  (* the blocks, whose code falls through, continue in the next block, and
     the last one in [last], explicitly *)
  let close ~last blks =
    let continue blk dst =
      if ends blk then Ok blk
      else
        match dst with
        | Some dst -> Ok (Term.append jmp_t blk (Jmp.create_goto dst))
        | None ->
            Or_error.errorf "the block %s falls through, without the next"
              (Tid.to_string (Term.tid blk))
    in
    let rec loop acc = function
      | [] -> Ok (List.rev acc)
      | [ blk ] ->
          Result.map (continue blk last) ~f:(fun b -> List.rev (b :: acc))
      | blk :: (next :: _ as rest) ->
          Result.bind
            (continue blk (Some (Direct (Term.tid next))))
            ~f:(fun b -> loop (b :: acc) rest)
    in
    loop [] blks

  let create ~last blks =
    match blks with
    | [] -> Or_error.error_string "the region has no blocks"
    | _ ->
        Result.map (close ~last blks) ~f:(fun blks ->
            { blks; replaces = Tid.Set.of_list (List.map blks ~f:Term.tid) })

  let of_blks ?next blks =
    create ~last:(Option.map next ~f:(fun a -> Indirect (Bil.int a))) blks

  let of_sub sub = create ~last:None (Term.enum blk_t sub |> Seq.to_list)

  (* the targets of the jumps of the block, that stay in the sub *)
  let targets blk =
    Term.enum jmp_t blk |> Seq.to_list
    |> List.concat_map ~f:(fun jmp ->
        let direct = function Some (Direct tid) -> [ tid ] | _ -> [] in
        match Jmp.kind jmp with
        | Goto l | Ret l -> direct (Some l)
        | Call c -> direct (Call.return c)
        | Int (_, tid) -> [ tid ])

  let of_range sub ~lo ~hi =
    (* the blocks of an instruction, but the first, have no address *)
    let blks = Term.enum blk_t sub |> Seq.to_list in
    let _, marked =
      List.fold_map blks ~init:None ~f:(fun addr blk ->
          let addr =
            match Term.get_attr blk address with
            | Some a -> Some a
            | None -> addr
          in
          let inside =
            match addr with
            | Some a -> Addr.(a >= lo) && Addr.(a < hi)
            | None -> false
          in
          (addr, (blk, inside)))
    in
    let inside = List.filter_map marked ~f:(fun (b, i) -> Option.some_if i b) in
    match inside with
    | [] -> Or_error.error_string "no blocks of the sub are in the range"
    | entry :: _ ->
        let tids = Tid.Set.of_list (List.map inside ~f:Term.tid) in
        (* the region has one entry, as its other blocks use the values,
           that the entry computed, after it is optimized *)
        let entered =
          List.filter_map marked ~f:(fun (b, i) -> Option.some_if (not i) b)
          |> List.concat_map ~f:targets
          |> List.filter ~f:(fun tid ->
              Set.mem tids tid && not (Tid.equal tid (Term.tid entry)))
        in
        if not (List.is_empty entered) then
          Or_error.errorf "the code outside of the range jumps to %s inside"
            (Tid.to_string (List.hd_exn entered))
        else
          (* the last block continues in the block after the range *)
          let after =
            List.drop_while blks ~f:(fun b ->
                not (Tid.equal (Term.tid b) (Term.tid (List.last_exn inside))))
            |> List.tl |> Option.bind ~f:List.hd
          in
          create
            ~last:(Option.map after ~f:(fun b -> Direct (Term.tid b)))
            inside

  let update sub t =
    let placed = ref false in
    let blks =
      Term.enum blk_t sub |> Seq.to_list
      |> List.concat_map ~f:(fun b ->
          if not (Set.mem t.replaces (Term.tid b)) then [ b ]
          else if !placed then []
          else (
            placed := true;
            t.blks))
    in
    let updated =
      Sub.create ~tid:(Term.tid sub) ~name:(Sub.name sub)
        ~args:(Term.enum arg_t sub |> Seq.to_list)
        ~blks ()
    in
    Term.with_attrs updated (Term.attrs sub)
end

(* the rounds of the optimization, until the number of the blocks
   doesn't change, as each round threads the dispatchers, that the
   previous one revealed *)
let deflatten ?target ?opt ?(passes = deflatten_passes) ?validate
    ?validate_thread ?validate_split ?(rounds = 4) sub =
  let blocks sub = Term.length blk_t sub in
  let rec loop n sub =
    if n = 0 then Ok sub
    else
      Result.bind
        (optimize ?target ?opt ~passes ?validate ?validate_thread
           ?validate_split sub) ~f:(fun sub' ->
          if blocks sub' = blocks sub then Ok sub' else loop (n - 1) sub')
  in
  loop rounds sub

let validate_thread = Recompile_lean.validate_thread
let thread_proof = Recompile_lean.thread_proof
let validate_split = Recompile_lean.validate_split
let split_proof = Recompile_lean.split_proof

let optimize_region ?target ?opt ?passes (region : Region.t) =
  let sub = Sub.create ~name:"region" ~blks:region.blks () in
  Result.map (optimize ?target ?opt ?passes sub) ~f:(fun sub ->
      { region with blks = Term.enum blk_t sub |> Seq.to_list })

let print_error sub err =
  eprintf "bap-recompile: can't optimize %s: %s\n%!" (Sub.name sub)
    (Error.to_string_hum err)

let optimize_program ?target ?opt ?passes ?(select = has_code)
    ?(report = print_error) prog =
  Term.enum sub_t prog |> Seq.to_list
  |> List.filter ~f:(fun sub -> has_code sub && select sub)
  |> optimize_subs ?target ?opt ?passes
  |> List.fold ~init:prog ~f:(fun prog (sub, result) ->
      match result with
      | Ok sub -> Term.update sub_t prog sub
      | Error err ->
          report sub err;
          prog)

let recompile ?(entry = "main") proj =
  let path =
    match Project.get proj filename with
    | Some file -> Caml_unix.realpath file
    | None -> invalid_arg "the project has no file"
  in
  ( Recompile_llvm.emit ~entry ~path (Recompile_llvm.program_of proj),
    Recompile_runtime.source )
