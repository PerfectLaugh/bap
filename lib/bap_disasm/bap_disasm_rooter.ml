open Bap_core_theory
open Core
open Bap_types.Std
open Bap_image_std
open Bap_disasm_source
module Context = Bap_disasm_source.Context
open KB.Syntax
module Insn = Bap_disasm_insn

type t = { path : string option; roots : addr seq; biased : bool }
type rooter = t

let merge_paths = Option.first_some
let create seq = { roots = seq; path = None; biased = false }
let roots { roots = x } = x

let union x y =
  {
    path = merge_paths x.path y.path;
    roots = Seq.append x.roots y.roots;
    biased = x.biased || y.biased;
  }

let set_path r s = { r with path = Some s }
let path { path = x } = x
let empty = create Seq.empty

module Factory = Factory.Make (struct
  type nonrec t = t
end)

let of_image img =
  {
    path = Image.filename img;
    roots =
      Image.symbols img |> Table.to_sequence |> Seq.map ~f:fst
      |> Seq.map ~f:Memory.min_addr
      |> Seq.cons (Image.entry_point img);
    biased = true;
  }

let of_blocks blocks =
  let roots = String.Table.create () in
  Seq.iter blocks ~f:(fun (name, sa, _) ->
      Hashtbl.change roots name ~f:(function
        | Some a when Addr.(a < sa) -> Some a
        | _ -> Some sa));
  create (Hashtbl.data roots |> Seq.of_list)

let make_provider rooter =
  let init = Set.empty (module Word) in
  let roots = roots rooter |> Seq.fold ~init ~f:Set.add in
  fun label ->
    KB.collect Theory.Label.addr label >>=? fun addr ->
    Context.for_label label >>| fun ctxt ->
    if Context.is_applicable ctxt rooter.path then
      let addr = Context.create_addr ctxt ~unbiased:(not rooter.biased) addr in
      Option.some_if (Set.mem roots addr) true
    else None

(* the starts of the unit, i.e., the label addresses that [make_provider]
   accepts: a label address [a] is accepted if [a - bias] (computed in
   the code address size, with [bias] only for unbiased rooters) is a
   root of that size, so the starts are the roots of that size plus
   [bias] *)
let make_starts rooter =
  let roots = roots rooter |> Seq.to_list in
  fun unit ->
    KB.collect Theory.Unit.path unit >>= fun path ->
    KB.collect Theory.Unit.bias unit >>= fun bias ->
    KB.collect Theory.Unit.target unit >>| fun target ->
    let size = Theory.Target.code_addr_size target in
    (* as [Context.is_applicable] *)
    let applicable =
      match (rooter.path, path) with
      | None, _ -> true
      | Some _, None -> false
      | Some p1, Some p2 -> String.equal p1 p2
    in
    if not applicable then Set.empty (module Bitvec_order)
    else
      let bias =
        match bias with
        | Some bias when not rooter.biased -> Word.create bias size
        | _ -> Word.zero size
      in
      List.fold roots
        ~init:(Set.empty (module Bitvec_order))
        ~f:(fun starts root ->
          if Int.equal (Word.bitwidth root) size then
            Set.add starts (Word.to_bitvec Word.(root + bias))
          else starts)

let provide =
  KB.Rule.(
    declare ~package:"bap" "reflect-rooter"
    |> dynamic [ "rooter" ] |> require Theory.Label.addr
    |> require Theory.Label.unit |> require Theory.Unit.path
    |> provide Theory.Unit.subroutines
    |> comment "[Rooter.provide r] provides [r] to KB (and is-subroutine).");
  fun rooter ->
    Theory.Label.promise_subroutines ~per_label:(make_provider rooter)
      (make_starts rooter)

let providing rooter =
  Theory.Label.promising_subroutines ~per_label:(make_provider rooter)
    ~promise:(make_starts rooter)
