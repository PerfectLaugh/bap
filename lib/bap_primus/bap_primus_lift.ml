(* Disassembles and lifts the instructions, which the program has at
   run time, e.g., of a bare project, which has no disassembly, or of
   the code, that the program writes or changes, as the disassembler
   does, so that the lifters see them as the instructions of the program.

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
   is bounded by the instructions, see [lifted].

   The knowledge is of the system, that runs the machine, see
   [Machine.knowledge], so the systems, e.g., the emulators of a script,
   lift the instructions in their own knowledge, with their own cache. *)

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

let decode ?encoding unit mem =
  let open KB.Syntax in
  let addr = Word.to_bitvec (Memory.min_addr mem) in
  KB.Object.create Theory.Program.cls >>= fun label ->
  KB.provide Theory.Label.addr label (Some addr) >>= fun () ->
  KB.provide Theory.Label.unit label (Some unit) >>= fun () ->
  Theory.Label.target label >>= fun target ->
  (* the encoding, that the caller knows, e.g., from the mode of the
     machine, or that the disassembler found for the address, e.g., of
     the Thumb code of ARM, which the label of the address has *)
  (match encoding with
    | Some coding -> KB.return coding
    | None ->
        Theory.Label.for_addr addr >>= fun known ->
        KB.collect Theory.Label.encoding known)
  >>= fun known ->
  (if Theory.Language.is_unknown known then
     KB.collect Theory.Label.encoding label
   else KB.provide Theory.Label.encoding label known >>| fun () -> known)
  >>= fun coding ->
  match Dis.lookup target coding with
  | Error _ -> KB.return (label, None)
  | Ok dis ->
      Dis.run dis mem ~stop_on:[ `Valid ] ~return:KB.return ~init:None
        ~hit:(fun _ mem insn _ ->
          KB.provide Memory.slot label (Some mem) >>= fun () ->
          KB.provide Dis.Insn.slot label (Some insn) >>| fun () ->
          Some (Memory.length mem, coding))
      >>| fun size -> (label, size)

(* the jumps to the labels of the addresses, which are outside of the
   instruction, jump to the addresses, which the interpreter takes,
   instead of the labels, which the linker doesn't know, and the jumps
   to the named labels, e.g., to the intrinsic functions, and to the
   interrupts jump to the labels of the toplevel knowledge, as the terms
   of the program have their names and interrupts there, see [Tid.name],
   and the labels are of the knowledge of the system, see [Make] *)
let addressed width blks =
  let open KB.Syntax in
  let inside tid = List.exists blks ~f:(fun b -> Tid.equal (Term.tid b) tid) in
  let resolve : label -> label KB.t = function
    | Direct tid when not (inside tid) -> (
        KB.collect Theory.Label.addr tid >>= function
        | Some addr -> KB.return (Indirect (Bil.int (Word.create addr width)))
        | None -> (
            KB.collect Theory.Label.name tid >>= function
            | Some name -> KB.return (Direct (Tid.for_name name))
            | None -> (
                KB.collect Theory.Label.ivec tid >>| function
                | Some ivec -> Direct (Tid.for_ivec ivec)
                | None -> Direct tid)))
    | label -> KB.return label
  in
  let resolve_jmp jmp =
    match Jmp.kind jmp with
    | Goto l -> resolve l >>| fun l -> Jmp.with_kind jmp (Goto l)
    | Ret l -> resolve l >>| fun l -> Jmp.with_kind jmp (Ret l)
    | Call c ->
        resolve (Call.target c) >>= fun target ->
        let c = Call.with_target c target in
        (match Call.return c with
          | Some r -> resolve r >>| Call.with_return c
          | None -> KB.return c)
        >>| fun c -> Jmp.with_kind jmp (Call c)
    | Int _ -> KB.return jmp
  in
  KB.List.map blks ~f:(fun blk ->
      Term.enum jmp_t blk |> Seq.to_list
      |> KB.List.fold ~init:blk ~f:(fun blk jmp ->
          resolve_jmp jmp >>| Term.update jmp_t blk))

(* the IR, that the disassembler computed for the instruction at
   [addr], if it has the bytes, that [code] starts with, which spares
   the loading of the program of the semantics, see above *)
let disassembled ?encoding addr code =
  let open KB.Syntax in
  Theory.Label.for_addr (Word.to_bitvec addr) >>= fun label ->
  KB.collect Theory.Label.encoding label >>= fun coding ->
  KB.collect Memory.slot label >>= function
  | Some mem
    when String.is_prefix code
           ~prefix:(Bigsubstring.to_string (Memory.to_buffer mem))
         && Option.for_all encoding ~f:(Theory.Language.equal coding) ->
      KB.collect Theory.Semantics.slot label >>| fun insn ->
      let blks = Blk.from_insn ~addr insn in
      if
        List.exists blks ~f:(fun blk ->
            Term.length def_t blk + Term.length jmp_t blk > 0)
      then Some (Memory.length mem, coding, insn)
      else None
  | _ -> KB.return None

(* the jumps of the call, that leave it, are the calls, that return
   to the next instruction, as the program has them, while the IR of the
   instruction has the jumps, e.g., of x86 and ARM *)
let calls ~next blks =
  let inside tid = List.exists blks ~f:(fun b -> Tid.equal (Term.tid b) tid) in
  let leaves : label -> bool = function
    | Direct tid -> not (inside tid)
    | Indirect _ -> true
  in
  List.map blks ~f:(fun blk ->
      Term.map jmp_t blk ~f:(fun jmp ->
          match Jmp.kind jmp with
          | Goto l when leaves l ->
              Jmp.with_kind jmp
                (Call (Call.create ~return:(Indirect next) ~target:l ()))
          | _ -> jmp))

(* the instruction, that no lifter defined, e.g., whose Primus Lisp
   definition is missing, which has no name, rather than the one, whose
   definition does nothing, e.g., NOP *)
let is_undefined insn = String.equal (Insn.name insn) (Insn.name Insn.empty)

(* the size, the encoding, the name and the IR of the instruction of
   [size] bytes at [addr], or none, if no lifter defined it, rather than
   the instruction, that does nothing, so that it fails, where it runs *)
let ir ~width ~addr ~size coding insn =
  if is_undefined insn then KB.return None
  else
    let blks = Blk.from_insn ~addr insn in
    let blks =
      if Insn.(is call) insn then calls ~next:(Bil.int Word.(addr ++ size)) blks
      else blks
    in
    KB.map (addressed width blks) ~f:(fun blks ->
        Some (size, coding, Insn.name insn, blks))

let width_of proj = Theory.Target.code_addr_size (Project.target proj)

(* the instruction, that the disassembler computed, see [disassembled] *)
let disassembled_insn ?encoding proj addr code =
  let open KB.Syntax in
  let width = width_of proj in
  let addr = Word.of_int64 ~width addr in
  disassembled ?encoding addr code >>= function
  | Some (size, coding, insn) -> ir ~width ~addr ~size coding insn
  | None -> KB.return None

(* the size and the IR of the instruction at [addr], that the decoder
   decodes from [code], the bytes from [addr], in the unit of [file] *)
let decoded ?encoding proj file addr code =
  let open KB.Syntax in
  let target = Project.target proj in
  let width = width_of proj in
  let addr = Word.of_int64 ~width addr in
  let endian =
    if Theory.Endianness.(equal eb) (Theory.Target.endianness target) then
      BigEndian
    else LittleEndian
  in
  match Memory.create endian addr (Bigstring.of_string code) with
  | Error _ -> KB.return None
  | Ok mem -> (
      unit_of_file file >>= fun unit ->
      (* the labels, that the lifters create, e.g., to find the target,
         which unaliases the registers, belong to the unit, as the
         project does it *)
      KB.promising Theory.Label.unit ~promise:(fun _ -> KB.return (Some unit))
      @@ fun () ->
      decode ?encoding unit mem >>= fun (label, size) ->
      match size with
      | None -> KB.return None
      | Some (size, coding) ->
          KB.collect Theory.Semantics.slot label
          >>= ir ~width ~addr ~size coding)

(* the size and the IR of the instruction at [addr], if [code], the
   bytes from [addr], has it, as the disassembler computed it, unless
   [disassembled] is false, e.g., so that the decoder decodes it, and
   keeps its state, see the IT blocks of Thumb *)
let lift ?encoding ?(disassembled = true) proj addr code =
  let open KB.Syntax in
  match Project.get proj filename with
  | None -> KB.return None
  | Some file -> (
      (if disassembled then disassembled_insn ?encoding proj addr code
       else KB.return None)
      >>= function
      | Some _ as insn -> KB.return insn
      | None -> decoded ?encoding proj file addr code)

(* the name of the instruction at [addr], that [code] has, which no
   lifter defined, so that it is not lifted, see [ir] *)
let undefined ?encoding proj addr code =
  let open KB.Syntax in
  match Project.get proj filename with
  | None -> KB.return None
  | Some file -> (
      let target = Project.target proj in
      let width = width_of proj in
      let addr = Word.of_int64 ~width addr in
      let endian =
        if Theory.Endianness.(equal eb) (Theory.Target.endianness target) then
          BigEndian
        else LittleEndian
      in
      match Memory.create endian addr (Bigstring.of_string code) with
      | Error _ -> KB.return None
      | Ok mem ->
          unit_of_file file >>= fun unit ->
          KB.promising Theory.Label.unit ~promise:(fun _ ->
              KB.return (Some unit))
          @@ fun () ->
          decode ?encoding unit mem >>= fun (label, size) ->
          if Option.is_none size then KB.return None
          else
            KB.collect Theory.Semantics.slot label >>= fun insn ->
            if not (is_undefined insn) then KB.return None
            else
              KB.collect Dis.Insn.slot label >>| fun basic ->
              Some
                (Option.value_map basic ~default:"an unknown instruction"
                   ~f:Dis.Insn.name))

let undefined ?encoding proj addr code =
  let open KB.Syntax in
  KB.catch (undefined ?encoding proj addr code) (fun _ -> KB.return None)

(* the instructions, that x86 has, are at most 15 bytes long *)
let max_size = 16

(* the instruction, outside of a machine, in the toplevel knowledge, e.g.,
   of a script, whose conflicts, e.g., of an invalid instruction, are no
   instruction *)
let instruction ?encoding ?disassembled proj addr code =
  let open KB.Syntax in
  KB.catch
    (lift ?encoding ?disassembled proj addr code
    >>| Option.map ~f:(fun (size, _, _, blks) -> (size, blks)))
    (fun _ -> KB.return None)

let named ?encoding proj addr code =
  let open KB.Syntax in
  KB.catch
    (lift ?encoding proj addr code
    >>| Option.map ~f:(fun (size, _, name, blks) -> (size, name, blks)))
    (fun _ -> KB.return None)

type entry = {
  code : string;
  encoding : Theory.language option;  (** that the caller asked for *)
  used : Theory.language;  (** that the instruction has *)
  name : string;  (** the name of the instruction, e.g., tBLXi *)
  insn : (int * blk term list) option;
}

(* the instructions, which are lifted, with their bytes, so that the
   instruction, whose bytes change, is lifted anew, which are of the
   system, as their labels are of its knowledge *)
let lifted =
  Bap_primus_machine.State.declare ~uuid:"7d3a1f86-2c94-4b5e-a0d7-58e6c1b92f34"
    ~name:"lifted-instructions" (fun _ -> Map.empty (module Int64))

module Make (Machine : Bap_primus_types.Machine) = struct
  open Machine.Syntax

  (* the conflicts of the lifters, e.g., of an invalid instruction, are
     no instruction *)
  let knowledge x = Machine.knowledge (KB.catch x (fun _ -> KB.return None))

  (* [insn ~read addr] the instruction at [addr], from the bytes, that
     [read addr n] reads, which are at most [n], or only the one, that
     the disassembler computed, if [disassembled_only], which costs
     less, if it is not cached, e.g., for the guesses of a trap *)
  let insn ?(disassembled_only = false) ?encoding ~read addr =
    Machine.get () >>= fun proj ->
    Machine.Global.get lifted >>= fun insns ->
    let bytes = read addr max_size in
    let remember result =
      let code, used, name, insn =
        match result with
        | Some (size, used, name, blks) ->
            (String.prefix bytes size, used, name, Some (size, blks))
        | None -> (bytes, Theory.Language.unknown, "", None)
      in
      Machine.Global.update lifted ~f:(fun insns ->
          Map.set insns ~key:addr ~data:{ code; encoding; used; name; insn })
      >>| fun () -> insn
    in
    let same = Option.equal Theory.Language.equal in
    match Map.find insns addr with
    | Some { code; encoding = cached; insn; _ }
      when String.is_prefix bytes ~prefix:code
           && (Option.is_none encoding || same cached encoding) ->
        Machine.return insn
    | _ when String.is_empty bytes -> remember None
    | _ when disassembled_only -> (
        knowledge (disassembled_insn ?encoding proj addr bytes) >>= function
        | Some _ as insn -> remember insn
        | None -> Machine.return None)
    | _ -> knowledge (lift ?encoding proj addr bytes) >>= remember

  let entry addr f =
    Machine.Global.get lifted >>| fun insns ->
    Option.map (Map.find insns addr) ~f

  (* the bytes of the instruction at [addr], which is lifted *)
  let code addr = entry addr (fun { code; _ } -> code)

  (* the encoding of the instruction at [addr], which is lifted *)
  let encoding addr = entry addr (fun { used; _ } -> used)

  (* the name of the instruction at [addr], which is lifted *)
  let name addr = entry addr (fun { name; _ } -> name)
end
