(* The constants, that the defs of a sub compute, in its SSA form, e.g.,
   the address, that adrp and add of AArch64, or mov and movk, build, are
   folded into the expressions, that use them, until no def computes a
   new one, so that the addresses, that the code builds, are the
   constants of the loads, the stores, and the jumps, see Bap_emu_xrefs
   and Bap_emu_slice. *)

open Core
open Bap.Std

type t = {
  ssa : sub term;  (** the sub in the SSA form, whose terms keep their tids *)
  simplify : exp -> exp;
      (** the expression, with the constants of its variables folded *)
  resolve : exp -> exp;
      (** as [simplify], and the variable, that holds the word of a slot, i.e.,
          a load from a constant address, is the load, e.g., the target of the
          jump of a PLT stub *)
}

let fold sub =
  let ssa = Sub.ssa sub in
  let consts = Var.Table.create () in
  let slots = Var.Table.create () in
  let substitute =
    object
      inherit Exp.mapper

      method! map_var v =
        match Hashtbl.find consts v with Some w -> Int w | None -> Var v
    end
  in
  let simplify e = Exp.fold_consts (substitute#map_exp e) in
  let defs =
    Term.enum blk_t ssa
    |> Seq.concat_map ~f:(Term.enum def_t)
    |> Seq.filter ~f:(fun d ->
        match Var.typ (Def.lhs d) with Imm _ -> true | _ -> false)
    |> Seq.to_list
  in
  let rec loop pending =
    let n = List.length pending in
    let pending =
      List.filter pending ~f:(fun d ->
          match simplify (Def.rhs d) with
          | Int w ->
              Hashtbl.set consts ~key:(Def.lhs d) ~data:w;
              false
          | Load (_, Int _, _, _) as load ->
              Hashtbl.set slots ~key:(Def.lhs d) ~data:load;
              true
          | _ -> true)
    in
    if List.length pending < n then loop pending
  in
  loop defs;
  let resolve e =
    match simplify e with
    | Var v as e -> Option.value (Hashtbl.find slots v) ~default:e
    | e -> e
  in
  { ssa; simplify; resolve }

(* the folded right-hand sides of the defs of the sub, by their tids *)
let defs { ssa; simplify; _ } =
  let folded = Tid.Table.create () in
  Term.enum blk_t ssa
  |> Seq.iter ~f:(fun blk ->
      Term.enum def_t blk
      |> Seq.iter ~f:(fun d ->
          Hashtbl.set folded ~key:(Term.tid d) ~data:(simplify (Def.rhs d))));
  folded
