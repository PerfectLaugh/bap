open Core
open Bap_types.Std
open Graphlib.Std
open Bap_ir
module Ssa = Bap_sema_ssa
module G = Bap_tid_graph

let ( ++ ) = Set.union
and ( -- ) = Set.diff

let ssa_free_vars sub =
  let is_undefined v = Var.index v = 0 in
  Term.enum blk_t sub
  |> Seq.fold ~init:Var.Set.empty ~f:(fun vars blk ->
      vars ++ Set.filter (Ir_blk.free_vars blk) ~f:is_undefined)

module Live = struct
  type tran = { defs : Var.Set.t; uses : Var.Set.t }
  type t = {
    blks : tran Tid.Map.t;
    ins : Var.Set.t Tid.Map.t;
    outs : (tid, Var.Set.t) Solution.t;
  }

  let pp_vars ppf vars =
    Format.pp_print_list ~pp_sep:Format.pp_print_space Var.pp ppf (Set.to_list vars)

  let pp_transfer ppf { uses; defs } =
    Format.fprintf ppf "(%a) / (%a)" pp_vars uses pp_vars defs

  let blk_defs blk =
    Term.enum def_t blk
    |> Seq.fold ~init:Var.Set.empty ~f:(fun defs def -> Set.add defs (Ir_def.lhs def))

  let update blk trans ~f =
    Map.update trans blk ~f:(function
      | None -> f { defs = Var.Set.empty; uses = Var.Set.empty }
      | Some had -> f had)

  let block_transitions sub =
    Term.enum blk_t sub
    |> Seq.fold ~init:Tid.Map.empty ~f:(fun fs blk ->
        Map.add_exn fs ~key:(Term.tid blk)
          ~data:{ defs = blk_defs blk; uses = Ir_blk.free_vars blk })
    |> fun trans ->
    Term.enum blk_t sub
    |> Seq.fold ~init:trans ~f:(fun init blk ->
        Term.enum phi_t blk
        |> Seq.fold ~init ~f:(fun init phi ->
            Ir_phi.values phi
            |> Seq.fold ~init ~f:(fun fs (src, exp) ->
                update src fs ~f:(fun { defs; uses } ->
                    { defs = Set.add defs (Ir_phi.lhs phi); uses = uses ++ (Exp.free_vars exp -- defs) }))))

  let lookup blks n =
    match Map.find blks n with
    | None -> { defs = Var.Set.empty; uses = Var.Set.empty }
    | Some t -> t

  let apply { defs; uses } vars = vars -- defs ++ uses
  let initialize ?(init = Var.Set.empty) sub =
    Seq.fold (Term.enum arg_t sub) ~init ~f:(fun vars arg ->
        match Ir_arg.intent arg with
        | None | Some In -> vars
        | Some (Out | Both) -> vars ++ Exp.free_vars (Ir_arg.rhs arg))

  let unwrap = function Ok value -> value | Error message -> failwith message

  external liveness_native :
    Bap_ir_wire.wire_sub -> Bap_bil_wire.wire_var list ->
    (Bap_ir_wire.wire_live list, string) result = "bap_cfg_rs_liveness"

  let compute ?keep:init sub =
    let initial = initialize ?init sub in
    let env, input = Bap_ir_wire.encode_sub_with_vars initial sub in
    let keep = Bap_ir_wire.encode_vars env initial in
    let ins, outs =
      liveness_native input keep |> unwrap
      |> Bap_ir_wire.decode_liveness env ~start:G.start ~exit:G.exit
    in
    {
      blks = block_transitions sub;
      ins;
      outs = Solution.create outs Var.Set.empty;
    }

  let outs { outs } blk = Solution.get outs blk
  let ins { ins } blk = Map.find ins blk |> Option.value ~default:Var.Set.empty
  let defs { blks } blk = (lookup blks blk).defs
  let uses { blks } blk = (lookup blks blk).uses

  let fold live ~init ~f =
    Map.fold live.blks ~init ~f:(fun ~key:blk ~data:_ init -> f init blk (ins live blk))

  let blks live var =
    fold live ~init:Tid.Set.empty ~f:(fun blks blk ins ->
        if Set.mem ins var then Set.add blks blk else blks)

  let vars live = outs live G.start
  let solution { outs = x } = x

  let pp ppf live =
    Format.pp_open_vbox ppf 0;
    fold live ~init:() ~f:(fun () blk live ->
        Format.fprintf ppf "@[<h>%a: @[<hov 2>(%a)@]@]@;" Tid.pp blk pp_vars live);
    Format.pp_close_box ppf ()
end

let compute_liveness sub = Live.(solution @@ compute sub)

let free_vars_of_sub sub =
  if Ssa.is_transformed sub then ssa_free_vars sub else Live.(vars @@ compute sub)
