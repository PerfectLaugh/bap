open Core
open Bap.Std
open Bap_core_theory
module Recompile_optimize = Recompile_optimize
module Recompile_mba = Recompile_mba
module Frame = Recompile_frame

let simplify_exp = Recompile_mba.simplify_exp
let simplify_exp_checked = Recompile_mba.simplify_exp_checked
let simplify_mba = Recompile_mba.simplify
let simplify_mba_checked = Recompile_mba.simplify_checked

let deflatten_passes =
  "function(sroa,early-cse,instcombine<no-verify-fixpoint>,sccp,simplifycfg,jump-threading,simplifycfg,sccp,instcombine<no-verify-fixpoint>,gvn,dse,adce,simplifycfg)"

let default_passes =
  "function(sroa,early-cse,instcombine<no-verify-fixpoint>,simplifycfg,sccp,gvn,dse,adce,jump-threading,instcombine<no-verify-fixpoint>,simplifycfg)"

(* the optimized subs by the pipeline and the text of the sub, which has
   its identifiers, so that the same sub is optimized once *)
let cache : sub term Or_error.t String.Table.t = String.Table.create ()

type mba = Disabled | Unchecked | Checked

let mba_name = function
  | Disabled -> "disabled"
  | Unchecked -> "unchecked"
  | Checked -> "checked"

let apply_mba mode sub =
  match mode with
  | Disabled -> Ok sub
  | Unchecked -> Recompile_mba.simplify sub
  | Checked -> Recompile_mba.simplify_checked sub

let key ?target ~mba ~expression_validated ~thread_validated ~split_validated
    passes sub =
  let target =
    Option.value_map target ~default:"" ~f:(fun t ->
        KB.Name.show (Theory.Target.name t))
  in
  String.concat ~sep:"\n"
    [
      target;
      passes;
      mba_name mba;
      Bool.to_string expression_validated;
      Bool.to_string thread_validated;
      Bool.to_string split_validated;
      Sub.to_string sub;
    ]

let has_code sub =
  not (Recompile_llvm.is_external sub || Recompile_llvm.is_intrinsic sub)

let validate_candidate = Recompile_candidate.validate_candidate

let optimize_subs ?target ?(opt = "opt") ?(passes = default_passes)
    ?(mba = Disabled) ?validate ?validate_thread ?validate_split subs =
  let key =
    key ?target ~mba ~expression_validated:(Option.is_some validate)
      ~thread_validated:(Option.is_some validate_thread)
      ~split_validated:(Option.is_some validate_split)
      passes
  in
  let cached, fresh =
    List.partition_map subs ~f:(fun original ->
        match Hashtbl.find cache (key original) with
        | Some result -> First (original, result)
        | None -> (
            match apply_mba mba original with
            | Error _ as result -> First (original, result)
            | Ok prepared -> Second (original, prepared)))
  in
  let optimized =
    if List.is_empty fresh then []
    else
      Recompile_optimize.optimize_subs ?target ?validate ?validate_thread
        ?validate_split ~opt ~pipeline:passes (List.map fresh ~f:snd)
      |> List.map2_exn fresh ~f:(fun (original, prepared) (_, result) ->
          let result =
            Result.bind result ~f:(fun optimized ->
                Result.map (validate_candidate prepared optimized) ~f:(fun () ->
                    optimized))
          in
          (original, result))
  in
  List.iter optimized ~f:(fun (sub, result) ->
      Hashtbl.set cache ~key:(key sub) ~data:result);
  cached @ optimized

let optimize ?target ?opt ?passes ?mba ?validate ?validate_thread
    ?validate_split sub =
  match
    optimize_subs ?target ?opt ?passes ?mba ?validate ?validate_thread
      ?validate_split [ sub ]
  with
  | [ (_, result) ] -> result
  | _ -> Or_error.error_string "the sub wasn't optimized"

module Region = Recompile_region

(* the rounds of the optimization, until the number of the blocks
   doesn't change, as each round threads the dispatchers, that the
   previous one revealed *)
let deflatten ?target ?opt ?(passes = deflatten_passes) ?mba ?validate
    ?validate_thread ?validate_split ?(rounds = 4) sub =
  let blocks sub = Term.length blk_t sub in
  let rec loop n sub =
    if n = 0 then Ok sub
    else
      Result.bind
        (optimize ?target ?opt ~passes ?mba ?validate ?validate_thread
           ?validate_split sub) ~f:(fun sub' ->
          if blocks sub' = blocks sub then Ok sub' else loop (n - 1) sub')
  in
  loop rounds sub

let validate_thread = Recompile_lean.validate_thread
let thread_proof = Recompile_lean.thread_proof
let validate_split = Recompile_lean.validate_split
let split_proof = Recompile_lean.split_proof

let optimize_region ?target ?opt ?passes ?mba (region : Region.t) =
  let sub = Sub.create ~name:"region" ~blks:(Region.blks region) () in
  Result.map (optimize ?target ?opt ?passes ?mba sub) ~f:(fun sub ->
      Region.with_blks region (Term.enum blk_t sub |> Seq.to_list))

let print_error sub err =
  eprintf "bap-recompile: can't optimize %s: %s\n%!" (Sub.name sub)
    (Error.to_string_hum err)

let optimize_program ?target ?opt ?passes ?mba ?(select = has_code)
    ?(report = print_error) prog =
  Term.enum sub_t prog |> Seq.to_list
  |> List.filter ~f:(fun sub -> has_code sub && select sub)
  |> optimize_subs ?target ?opt ?passes ?mba
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
