open Core
open Bap_bil
open Bap_ir

module Wire = Bap_bil_wire
module Var = Bap_var

type wire_def = { tid : int; var : Wire.wire_var; rhs : Wire.wire_exp }
type wire_phi = { tid : int; var : Wire.wire_var; values : (int * Wire.wire_exp) list }
type wire_label = Direct of int | Indirect of Wire.wire_exp
type wire_kind =
  | Goto of wire_label
  | Call of wire_label * wire_label option
  | Return of wire_label
  | Interrupt of int * int
type wire_jmp = { tid : int; condition : Wire.wire_exp option; kind : wire_kind }
type wire_blk = { tid : int; phis : wire_phi list; defs : wire_def list; jmps : wire_jmp list }
type wire_sub = { tid : int; name : string; args : wire_def list; blks : wire_blk list }
type wire_live = { tid : int; ins : Wire.wire_var list; outs : Wire.wire_var list }
type wire_edge = { src : int; dst : int; label : int }

type env = { wire : Wire.env; tids : Tid.t array }
type encoder = {
  bil : Wire.encoder;
  mutable tids_rev : Tid.t list;
  tid_ids : int Tid.Table.t;
}

let create_encoder () =
  { bil = Wire.create_encoder (); tids_rev = []; tid_ids = Tid.Table.create () }

let finish_encoder encoder =
  { wire = Wire.finish_encoder encoder.bil; tids = Array.of_list_rev encoder.tids_rev }

let intern_tid encoder tid =
  Hashtbl.find_or_add encoder.tid_ids tid ~default:(fun () ->
      let id = List.length encoder.tids_rev in
      encoder.tids_rev <- tid :: encoder.tids_rev;
      id)

let tid_of_wire env value = env.tids.(value)

let label encoder : Bap_ir.label -> wire_label = function
  | Direct value -> (Direct (intern_tid encoder value) : wire_label)
  | Indirect exp -> Indirect (Wire.exp encoder.bil exp)

let def_with_tag _tag encoder term =
  { tid = intern_tid encoder (Term.tid term); var = Wire.var encoder.bil (Ir_def.lhs term); rhs = Wire.exp encoder.bil (Ir_def.rhs term) }

let arg encoder term =
  { tid = intern_tid encoder (Term.tid term); var = Wire.var encoder.bil (Ir_arg.lhs term); rhs = Wire.exp encoder.bil (Ir_arg.rhs term) }

let phi encoder term =
  let values =
    Ir_phi.values term
    |> Sequence.map ~f:(fun (source, exp) -> (intern_tid encoder source, Wire.exp encoder.bil exp))
    |> Sequence.to_list
  in
  { tid = intern_tid encoder (Term.tid term); var = Wire.var encoder.bil (Ir_phi.lhs term); values }

let jmp encoder term =
  let condition =
    match Ir_jmp.guard term with
    | None -> None
    | Some _ -> Some (Wire.exp encoder.bil (Ir_jmp.cond term))
  in
  let kind =
    match Ir_jmp.kind term with
    | Goto value -> Goto (label encoder value)
    | Ret value -> Return (label encoder value)
    | Call call ->
        Call (label encoder (Call.target call), Option.map (Call.return call) ~f:(label encoder))
    | Int (number, return_to) -> Interrupt (number, intern_tid encoder return_to)
  in
  { tid = intern_tid encoder (Term.tid term); condition; kind }

let blk encoder term =
  {
    tid = intern_tid encoder (Term.tid term);
    phis = Term.enum phi_t term |> Sequence.map ~f:(phi encoder) |> Sequence.to_list;
    defs = Term.enum def_t term |> Sequence.map ~f:(def_with_tag "def" encoder) |> Sequence.to_list;
    jmps = Term.enum jmp_t term |> Sequence.map ~f:(jmp encoder) |> Sequence.to_list;
  }

let encode_sub_with_vars vars sub =
  let encoder = create_encoder () in
  Set.iter vars ~f:(fun var -> ignore (Wire.intern encoder.bil var));
  let wire =
    {
      tid = intern_tid encoder (Term.tid sub);
      name = Ir_sub.name sub;
      args = Term.enum arg_t sub |> Sequence.map ~f:(arg encoder) |> Sequence.to_list;
      blks = Term.enum blk_t sub |> Sequence.map ~f:(blk encoder) |> Sequence.to_list;
    }
  in
  (finish_encoder encoder, wire)

let encode_sub = encode_sub_with_vars Var.Set.empty

let decode_tid env ~start ~exit = function
  | -1 -> start
  | -2 -> exit
  | value -> tid_of_wire env value

let label_of_wire env ~start ~exit (label : wire_label) : Bap_ir.label =
  match label with
  | Direct tid -> Direct (decode_tid env ~start ~exit tid)
  | Indirect exp -> Indirect (Wire.exp_of_wire env.wire exp)

let update_jmp env ~start ~exit original (decoded : wire_jmp) =
  let original =
    match decoded.condition with
    | None -> Ir_jmp.with_guard original None
    | Some condition -> Ir_jmp.with_cond original (Wire.exp_of_wire env.wire condition)
  in
  let kind : Bap_ir.jmp_kind =
    match decoded.kind with
    | Goto label -> Goto (label_of_wire env ~start ~exit label)
    | Return label -> Ret (label_of_wire env ~start ~exit label)
    | Call (target, return_to) ->
        let target = label_of_wire env ~start ~exit target in
        let return = Option.map return_to ~f:(label_of_wire env ~start ~exit) in
        Call (Call.create ?return ~target ())
    | Interrupt (number, return_to) -> Int (number, decode_tid env ~start ~exit return_to)
  in
  Ir_jmp.with_kind original kind

let decode_ssa env ~start ~exit original (decoded : wire_sub) =
  let ids = Tid.Table.create () in
  Array.iteri env.tids ~f:(fun id tid -> Hashtbl.set ids ~key:tid ~data:id);
  let update_blk original (decoded : wire_blk) =
    let by_def (items : wire_def list) tid : wire_def =
      List.find_exn items ~f:(fun item -> item.tid = tid)
    in
    let by_jmp (items : wire_jmp list) tid : wire_jmp =
      List.find_exn items ~f:(fun item -> item.tid = tid)
    in
    let original =
      Term.map def_t original ~f:(fun def ->
          let rhs = by_def decoded.defs (Hashtbl.find_exn ids (Term.tid def)) in
          Ir_def.with_rhs
            (Ir_def.with_lhs def (Wire.var_of_wire env.wire rhs.var))
            (Wire.exp_of_wire env.wire rhs.rhs))
    in
    let original =
      Term.map jmp_t original ~f:(fun jmp ->
          update_jmp env ~start ~exit jmp (by_jmp decoded.jmps (Hashtbl.find_exn ids (Term.tid jmp))))
    in
    let original_phis = Term.enum phi_t original |> Sequence.to_list in
    let original = Term.filter phi_t original ~f:(fun _ -> false) in
    List.fold decoded.phis ~init:original ~f:(fun blk phi ->
        let var = Wire.var_of_wire env.wire phi.var in
        let values =
          List.map phi.values ~f:(fun (source, exp) -> (decode_tid env ~start ~exit source, Wire.exp_of_wire env.wire exp))
        in
        let phi' =
          match
            List.find original_phis ~f:(fun original ->
                Hashtbl.find_exn ids (Term.tid original) = phi.tid)
          with
          | Some original ->
              List.fold values ~init:(Ir_phi.with_lhs original var) ~f:(fun phi (source, exp) ->
                  Ir_phi.update phi source exp)
          | None -> Ir_phi.of_list var values
        in
        Term.append phi_t blk phi')
  in
  Term.enum blk_t original
  |> Sequence.fold ~init:original ~f:(fun sub blk ->
      let decoded =
        List.find_exn decoded.blks ~f:(fun candidate ->
            candidate.tid = Hashtbl.find_exn ids (Term.tid blk))
      in
      Term.update blk_t sub (update_blk blk decoded))

let encode_vars env vars =
  let encode var =
    let id =
      Array.findi env.wire.vars ~f:(fun _ candidate -> Var.equal candidate var)
      |> Option.value_exn ~message:"liveness variable is not present in the subroutine"
      |> fst
    in
    {
      Wire.id = id;
      index = Var.index var;
      typ = Wire.typ (Var.typ var);
      is_virtual = Var.is_virtual var;
    }
  in
  Set.to_list vars |> List.map ~f:encode

let decode_liveness env ~start ~exit reports =
  let decode_tid = function -1 -> start | -2 -> exit | value -> tid_of_wire env value in
  let var_set values = List.map values ~f:(Wire.var_of_wire env.wire) |> Var.Set.of_list in
  List.fold reports ~init:(Tid.Map.empty, Tid.Map.empty) ~f:(fun (ins, outs) report ->
      let tid = decode_tid report.tid in
      ( Map.set ins ~key:tid ~data:(var_set report.ins),
        Map.set outs ~key:tid ~data:(var_set report.outs) ))

let decode_edges env ~start ~exit edges =
  let decode_tid = function -1 -> start | -2 -> exit | value -> tid_of_wire env value in
  List.map edges ~f:(fun edge -> (decode_tid edge.src, decode_tid edge.dst, decode_tid edge.label))
