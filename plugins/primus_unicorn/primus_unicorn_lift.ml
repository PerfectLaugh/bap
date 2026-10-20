(* Disassembles and lifts the instructions of a project on demand, e.g.,
   of a bare project, which has no disassembly, as the disassembler does,
   so that the lifters see them as the instructions of its program.

   The knowledge is computed in the toplevel, also when a Primus system
   runs, whose knowledge replaces it, when it finishes, so the facts of
   the instructions, which are lifted again, are not kept. *)

open Core
open Bap_core_theory
open Bap.Std
module Dis = Disasm_expert.Basic

(* the memory of the code from [addr] to the end of its segment *)
let code proj addr =
  Memmap.to_sequence (Project.memory proj)
  |> Seq.find_map ~f:(fun (mem, tag) ->
      match Value.get Image.segment tag with
      | Some seg
        when Image.Segment.is_executable seg && Memory.contains mem addr ->
          Some (Memory.view_exn ~from:addr mem)
      | _ -> None)

let decode file mem =
  let open KB.Syntax in
  let addr = Word.to_bitvec (Memory.min_addr mem) in
  Theory.Label.for_addr addr >>= fun label ->
  Theory.Unit.for_file file >>= fun unit ->
  ( KB.collect Theory.Label.unit label >>= function
    | Some _ -> KB.return ()
    | None -> KB.provide Theory.Label.unit label (Some unit) )
  >>= fun () ->
  Theory.Label.target label >>= fun target ->
  KB.collect Theory.Label.encoding label >>= fun coding ->
  match Dis.lookup target coding with
  | Error _ -> KB.return (label, None)
  | Ok dis ->
      Dis.run dis mem ~stop_on:[ `Valid ] ~return:KB.return ~init:None
        ~hit:(fun _ mem insn _ ->
          KB.provide Memory.slot label (Some mem) >>= fun () ->
          KB.provide Dis.Insn.slot label (Some insn) >>| fun () ->
          Some (Memory.length mem))
      >>| fun size -> (label, size)

(* the size and the IR of the instruction at [addr], if it is decoded *)
let insn proj addr =
  match Project.get proj filename with
  | None -> None
  | Some file -> (
      let width = Theory.Target.code_addr_size (Project.target proj) in
      let addr = Word.of_int64 ~width addr in
      match code proj addr with
      | None -> None
      | Some mem -> (
          let result = Toplevel.var "unicorn-lifted-insn" in
          match
            Toplevel.put result
              (let open KB.Syntax in
               decode file mem >>= fun (label, size) ->
               match size with
               | None -> KB.return None
               | Some size ->
                   KB.collect Theory.Semantics.slot label >>| fun insn ->
                   Some (size, insn))
          with
          | exception _ -> None
          | () -> (
              match Toplevel.get result with
              | Some (size, insn) -> Some (size, Blk.from_insn ~addr insn)
              | None -> None)))
