(* Disassembles and lifts the instructions, which the program has at
   run time, e.g., of a bare project, which has no disassembly, or of
   the code, that the program writes, as the disassembler does, so that
   the lifters see them as the instructions of the program.

   An instruction is decoded from the bytes, that the caller reads from
   the memory of the machine, into a fresh label with the address of the
   instruction, as the label of the address may have the facts of other
   bytes, e.g., of the code, that the program changed.

   The labels belong to a unit of this process, with the facts of the
   unit of the file, as the knowledge of the unit of the file, which bap
   loads from its cache, has no program of the Primus Lisp semantics,
   e.g., of x86, which is not persistent, so the lifters, that use it,
   lift nothing. The unit stays in the knowledge, so that its program is
   loaded once, and the labels, that the lifting creates, stay too, which
   is bounded by the instructions, see [lifted]. *)

open Core
open Bap_core_theory
open Bap.Std
module Dis = Disasm_expert.Basic

(* the name of the unit of this process, which is computed, when it is
   needed, as the plugin may be loaded, where the random seeds are not
   allowed, e.g., in the inline tests *)
let nonce =
  lazy
    (let state = Random.State.make_self_init () in
     sprintf "%016Lx" (Random.State.int64 state Int64.max_value))

(* the unit of the labels, see above *)
let unit_of_file file =
  let open KB.Syntax in
  Theory.Unit.for_file file >>= fun origin ->
  KB.Symbol.intern ~package:"primus-unicorn"
    (file ^ "#" ^ Lazy.force nonce)
    Theory.Unit.cls
  >>= fun unit ->
  KB.collect Theory.Unit.target unit >>= fun target ->
  if not (Theory.Target.is_unknown target) then KB.return unit
  else
    let copy slot = KB.collect slot origin >>= KB.provide slot unit in
    copy Theory.Unit.target >>= fun () ->
    copy Theory.Unit.path >>= fun () ->
    copy Theory.Unit.bias >>= fun () ->
    copy Theory.Unit.compiler >>= fun () ->
    copy Arch.unit_slot >>= fun () ->
    copy Image.Spec.slot >>| fun () -> unit

let decode unit mem =
  let open KB.Syntax in
  let addr = Word.to_bitvec (Memory.min_addr mem) in
  KB.Object.create Theory.Program.cls >>= fun label ->
  KB.provide Theory.Label.addr label (Some addr) >>= fun () ->
  KB.provide Theory.Label.unit label (Some unit) >>= fun () ->
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

(* the jumps to the labels of the addresses, which are outside of the
   instruction, jump to the addresses, which the interpreter takes,
   instead of the labels, which the linker doesn't know *)
let addressed width blks =
  let inside tid = List.exists blks ~f:(fun b -> Tid.equal (Term.tid b) tid) in
  let resolve : label -> label = function
    | Direct tid when not (inside tid) -> (
        match Toplevel.eval Theory.Label.addr (KB.return tid) with
        | Some addr -> Indirect (Bil.int (Word.create addr width))
        | None | (exception _) -> Direct tid)
    | label -> label
  in
  List.map blks ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun jmp ->
          match Jmp.kind jmp with
          | Goto l -> Jmp.with_kind jmp (Goto (resolve l))
          | Ret l -> Jmp.with_kind jmp (Ret (resolve l))
          | Call c ->
              let c = Call.with_target c (resolve (Call.target c)) in
              let c =
                match Call.return c with
                | Some r -> Call.with_return c (resolve r)
                | None -> c
              in
              Jmp.with_kind jmp (Call c)
          | Int _ -> jmp))

(* the IR, that the disassembler computed for the instruction at
   [addr], if it has the bytes, that [code] starts with, which spares
   the loading of the program of the semantics, see above *)
let disassembled addr code =
  let result = Toplevel.var "unicorn-disassembled-insn" in
  match
    Toplevel.put result
      (let open KB.Syntax in
       Theory.Label.for_addr (Word.to_bitvec addr) >>= fun label ->
       KB.collect Memory.slot label >>= function
       | Some mem
         when String.is_prefix code
                ~prefix:(Bigsubstring.to_string (Memory.to_buffer mem)) ->
           KB.collect Theory.Semantics.slot label >>| fun insn ->
           Some (Memory.length mem, insn)
       | _ -> KB.return None)
  with
  | exception _ -> None
  | () -> (
      match Toplevel.get result with
      | Some (size, insn) ->
          let blks = Blk.from_insn ~addr insn in
          if
            List.exists blks ~f:(fun blk ->
                Term.length def_t blk + Term.length jmp_t blk > 0)
          then Some (size, blks)
          else None
      | None | (exception _) -> None)

(* the size and the IR of the instruction at [addr], if [code], the
   bytes from [addr], has it *)
let lift proj addr code =
  match Project.get proj filename with
  | None -> None
  | Some file -> (
      let target = Project.target proj in
      let width = Theory.Target.code_addr_size target in
      let addr = Word.of_int64 ~width addr in
      let endian =
        if Theory.Endianness.(equal eb) (Theory.Target.endianness target) then
          BigEndian
        else LittleEndian
      in
      match disassembled addr code with
      | Some (size, blks) -> Some (size, addressed width blks)
      | None -> (
          match Memory.create endian addr (Bigstring.of_string code) with
          | Error _ -> None
          | Ok mem -> (
              let result = Toplevel.var "unicorn-lifted-insn" in
              match
                Toplevel.put result
                  (let open KB.Syntax in
                   unit_of_file file >>= fun unit ->
                   (* the labels, that the lifters create, e.g., to find
                    the target, which unaliases the registers, belong to
                    the unit, as the project does it *)
                   KB.promising Theory.Label.unit ~promise:(fun _ ->
                       KB.return (Some unit))
                   @@ fun () ->
                   decode unit mem >>= fun (label, size) ->
                   match size with
                   | None -> KB.return None
                   | Some size ->
                       KB.collect Theory.Semantics.slot label >>| fun insn ->
                       Some (size, insn))
              with
              | exception _ -> None
              | () -> (
                  match Toplevel.get result with
                  | Some (size, insn) ->
                      Some (size, addressed width (Blk.from_insn ~addr insn))
                  | None | (exception _) -> None))))

(* the instructions, that x86 has, are at most 15 bytes long *)
let max_size = 16

type entry = { code : string; insn : (int * blk term list) option }

(* the instructions, which are lifted, with their bytes, so that the
   instruction, whose bytes change, is lifted anew *)
let lifted : entry Int64.Table.t String.Table.t = String.Table.create ()

(* [insn proj ~read addr] the instruction at [addr], from the bytes,
   that [read addr n] reads, which are at most [n], or only the one,
   that the disassembler computed, if [disassembled_only], which costs
   less, if it is not cached, e.g., for the guesses of [trap] *)
let insn ?(disassembled_only = false) proj ~read addr =
  let file = Option.value (Project.get proj filename) ~default:"" in
  let insns = Hashtbl.find_or_add lifted file ~default:Int64.Table.create in
  let bytes = read addr max_size in
  let remember insn =
    let code =
      match insn with
      | Some (size, _) -> String.prefix bytes size
      | None -> bytes
    in
    Hashtbl.set insns ~key:addr ~data:{ code; insn };
    insn
  in
  match Hashtbl.find insns addr with
  | Some { code; insn } when String.is_prefix bytes ~prefix:code -> insn
  | _ when String.is_empty bytes -> remember None
  | _ when disassembled_only -> (
      let target = Project.target proj in
      let width = Theory.Target.code_addr_size target in
      match disassembled (Word.of_int64 ~width addr) bytes with
      | Some (size, blks) -> remember (Some (size, addressed width blks))
      | None -> None)
  | _ -> remember (lift proj addr bytes)

(* the bytes of the instruction at [addr], which is lifted *)
let code proj addr =
  let file = Option.value (Project.get proj filename) ~default:"" in
  Option.bind (Hashtbl.find lifted file) ~f:(fun insns ->
      Option.map (Hashtbl.find insns addr) ~f:(fun { code; _ } -> code))
