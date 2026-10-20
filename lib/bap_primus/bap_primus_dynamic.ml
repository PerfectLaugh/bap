open Core
open Bap_core_theory
open Bap.Std
open Bap_primus_types
include Self ()

module Primus = struct
  module Linker = Bap_primus_linker
  module Machine = Bap_primus_machine
  module Memory = Bap_primus_memory
  module Value = Bap_primus_value
end

open Primus
module Interpreter = Bap_primus_interpreter
module Lift = Bap_primus_lift

(* The code, that the program changes or writes, e.g., on the heap,
   which the disassembly of the program doesn't have, runs as it is in
   the memory of the machine: the instructions are lifted, when they run,
   see [Bap_primus_lift], until the program jumps to the code, that it
   didn't change. A basic block of the program, that the program stores
   to, and its subroutine, which starts there, are linked to the dynamic
   code, as well as the executable address, that nothing is linked to.

   Limits:

   - the block, that the program changes, while it runs, e.g., the next
     instructions of the block, that stores to them, runs as it was,
     until the program jumps to it again, as the interpreter runs the
     blocks, not the instructions;

   - the dynamic code of a subroutine, that the program calls, e.g., as
     it changed its first block, posts no [call] and [call-return]
     observations, which the interpreter posts for the subroutines of the
     program, as the dynamic code has no arguments, and neither do the
     calls, that the dynamic code makes;

   - the mode of the dynamic code of ARM, see [Arm], Thumb or A32, is the
     encoding,
     that the disassembler found at the address, or the mode, that the
     jumps tell: the jump to the odd address, e.g., [blx r3], enters
     Thumb, the next instruction and the direct jumps, e.g., [b label],
     stay in the mode, and the other jumps to the even addresses, e.g.,
     [bx r3], enter A32, so the direct jump from Thumb to the A32 code,
     that the program writes, i.e., [blx label], is decoded as Thumb, and
     the code, that the program enters otherwise, e.g., by a return,
     whose IR clears the Thumb bit, has the default encoding of the
     target, e.g., A32. *)

(* the basic blocks of the disassembly, their last addresses, and the
   blocks and the subroutines of the program, that start there, which are
   indexed, when the program first stores to the executable segments *)
type blocks = {
  blocks : addr Addr.Map.t;
  blks : tid list Addr.Map.t;
  subs : (tid * string) Addr.Map.t;
}

type code = { segments : (addr * addr) list; index : blocks Lazy.t }

let index proj =
  let blocks =
    Graphs.Cfg.nodes (Disasm.cfg (Project.disasm proj))
    |> Seq.fold ~init:Addr.Map.empty ~f:(fun blocks blk ->
        let mem = Block.memory blk in
        Map.set blocks
          ~key:(Bap.Std.Memory.min_addr mem)
          ~data:(Bap.Std.Memory.max_addr mem))
  in
  let prog = Project.program proj in
  let blks =
    Term.enum sub_t prog
    |> Seq.concat_map ~f:(Term.enum blk_t)
    |> Seq.fold ~init:Addr.Map.empty ~f:(fun blks blk ->
        match Term.get_attr blk address with
        | Some addr -> Map.add_multi blks ~key:addr ~data:(Term.tid blk)
        | None -> blks)
  and subs =
    Term.enum sub_t prog
    |> Seq.fold ~init:Addr.Map.empty ~f:(fun subs sub ->
        match Term.get_attr sub address with
        | Some addr -> Map.set subs ~key:addr ~data:(Term.tid sub, Sub.name sub)
        | None -> subs)
  in
  { blocks; blks; subs }

let code =
  Primus.Machine.State.declare ~uuid:"5b9e0d3a-7c1f-4e2b-9a6d-3f8c1e0b2d47"
    ~name:"program-code" (fun proj ->
      let segments =
        Memmap.to_sequence (Project.memory proj)
        |> Seq.filter_map ~f:(fun (mem, tag) ->
            match Bap.Std.Value.get Image.segment tag with
            | Some seg when Image.Segment.is_executable seg ->
                Some (Bap.Std.Memory.min_addr mem, Bap.Std.Memory.max_addr mem)
            | _ -> None)
        |> Seq.to_list
      in
      { segments; index = lazy (index proj) })

(* the addresses, that are linked to the dynamic code *)
let dynamic =
  Primus.Machine.State.declare ~uuid:"e1a4c7f2-3b5d-4c8e-8f0a-6d2b9c4e1f73"
    ~name:"dynamic-code" (fun _ -> Addr.Set.empty)

(* The mode of the machine, that tells the encoding of the dynamic
   code, e.g., Thumb or A32 of ARM, and the addresses of the code, that
   the jumps enter, which are the targets of the jumps, by default, see
   [Generic] and [Arm]. *)
module type Mode = functor (Machine : Machine) -> sig
  val enter : addr -> addr Machine.t
  (** [enter addr] the address of the instruction, that the jump to [addr]
      enters *)

  val encoding : addr -> Theory.language option Machine.t
  (** [encoding addr] the encoding of the instruction at [addr], that the mode
      tells, otherwise [Lift.insn] finds it *)

  val leave : addr -> blk term list -> next:addr -> addr -> addr Machine.t
  (** [leave addr blks ~next dst] the address, that the instruction at [addr],
      whose IR is [blks], jumps to, when it jumps to [dst], or falls through to
      [next] *)
end

(* the code, that has one mode *)
module Generic (Machine : Machine) = struct
  let enter = Machine.return
  let encoding _ = Machine.return None
  let leave _ _ ~next:_ dst = Machine.return dst
end

(* The mode of ARM, Thumb or A32, is the encoding, that the disassembler
   found at the address, or the mode, that the jumps tell: the jump to
   the odd address, e.g., [blx r3], enters the Thumb code at the even
   address, the next instruction and the direct jumps, e.g., [b label],
   stay in the mode, and the other jumps to the even addresses, e.g.,
   [bx r3], enter A32. *)
(* the addresses of the Thumb code, that the dynamic code runs *)
let thumb =
  Bap_primus_machine.State.declare ~uuid:"9d3f6a21-58c4-4b7e-a0d2-7e1c5b8f4a69"
    ~name:"dynamic-thumb-code" (fun _ -> Addr.Set.empty)

let thumb_encoding =
  lazy
    (match Theory.Language.read ~package:"bap" "llvm-thumb" with
    | language -> Some language
    | exception _ -> None)

module Arm (Machine : Machine) = struct
  open Machine.Syntax

  let int64 x = Bitvec.to_int64 (Word.to_bitvec x)
  let set_thumb addr = Machine.Local.update thumb ~f:(fun s -> Set.add s addr)

  (* the address without the Thumb bit, and the bit *)
  let even addr =
    if Word.(is_one (extract_exn ~hi:0 addr)) then
      (Word.(addr land lnot (one (bitwidth addr))), true)
    else (addr, false)

  let enter addr =
    let addr, odd = even addr in
    (if odd then set_thumb addr else Machine.return ()) >>| fun () -> addr

  let encoding addr =
    Machine.Local.get thumb >>| fun s ->
    if Set.mem s addr then Lazy.force thumb_encoding else None

  (* the instruction is Thumb, as the mode tells, or the disassembler *)
  let is_thumb addr =
    Machine.get () >>= fun proj ->
    Machine.Local.get thumb >>| fun s ->
    Set.mem s addr
    ||
    match (Lift.encoding proj (int64 addr), Lazy.force thumb_encoding) with
    | Some used, Some thumb -> Theory.Language.equal used thumb
    | _ -> false

  (* the jump to the constant address, e.g., [b label], that stays in
     the mode, unlike [bx r0] to the even address *)
  let is_direct blks =
    List.for_all blks ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.for_all ~f:(fun jmp ->
            match Jmp.kind jmp with
            | Goto (Indirect (Bil.Int _)) | Call _ | Goto (Direct _) | Int _ ->
                true
            | Goto (Indirect _) | Ret _ -> false))

  let leave addr blks ~next dst =
    is_thumb addr >>= fun thumb ->
    let dst, odd = even dst in
    (if thumb then set_thumb next else Machine.return ()) >>= fun () ->
    (if odd || (thumb && is_direct blks) then set_thumb dst
     else Machine.return ())
    >>| fun () -> dst
end

module Run (Mode : Mode) (Machine : Machine) = struct
  open Machine.Syntax
  open Machine.Let
  module Memory = Primus.Memory.Make (Machine)
  module Interp = Interpreter.Make (Machine)
  module Code = Linker.Make (Machine)
  module Mode = Mode (Machine)

  let int64 x = Bitvec.to_int64 (Word.to_bitvec x)

  (* the bytes from [addr], while they are executable *)
  let fetch addr =
    let+ loaded = Memory.load_bytes addr Lift.max_size in
    let rec bytes i acc =
      if i = Array.length loaded then acc
      else
        match loaded.(i) with
        | Some (c, { Primus.Memory.executable = true; _ }) ->
            bytes (i + 1) (c :: acc)
        | _ -> acc
    in
    String.of_char_list (List.rev (bytes 0 []))

  let is_call blks =
    List.exists blks ~f:(fun blk ->
        Term.enum jmp_t blk
        |> Seq.exists ~f:(fun jmp ->
            match Jmp.kind jmp with Call _ -> true | _ -> false))

  (* the return of a call, which the code at [addr] calls, is linked
     with the term, which the callee returns to, as the interpreter
     does, see [Interpreter.call_at], and from which the code continues *)
  let return_of ~link addr =
    let* linked = Machine.Local.get dynamic in
    let* tid = Code.resolve_tid (`addr addr) in
    match tid with
    | Some tid when Set.mem linked addr -> Machine.return tid
    | _ ->
        let tid = Tid.create () in
        let+ () = link ~tid addr in
        tid

  (* runs the code from [addr], see above, the code, that is linked
     to the address, see [link], runs as the code of the program *)
  let rec run ~link addr =
    let* proj = Machine.get () in
    let* addr = Mode.enter addr in
    let* encoding = Mode.encoding addr in
    let* bytes = fetch addr in
    let read _ n = String.prefix bytes n in
    match Lift.insn ?encoding proj ~read (int64 addr) with
    | None -> Machine.raise (Interpreter.Segmentation_fault addr)
    | Some (size, blks) ->
        let next = Word.(addr ++ size) in
        let* dst = Interp.step ~next blks in
        let* dst = Mode.leave addr blks ~next (Value.to_word dst) in
        if is_call blks && not (Word.equal dst next) then
          let* return = return_of ~link next in
          let* () = Interp.call_at dst ~return in
          run ~link next
        else
          let* linked = Machine.Local.get dynamic in
          let* tid = Code.resolve_tid (`addr dst) in
          (* the return, that a call waits for, unwinds to the call *)
          if Set.mem linked dst && Option.is_none tid then run ~link dst
          else Interp.continue_at dst
end

(* the code, that runs the dynamic code from [addr], in the mode of the
   architecture *)
let rec dynamic_code addr : Linker.code =
  let module Code (Machine : Machine) = struct
    open Machine.Syntax
    module Generic = Run (Generic) (Machine)
    module Arm = Run (Arm) (Machine)
    module Linker = Linker.Make (Machine)

    let link ~tid addr =
      Machine.Local.update dynamic ~f:(fun linked -> Set.add linked addr)
      >>= fun () -> Linker.link ~addr ~tid (dynamic_code addr)

    let exec =
      Machine.gets Project.arch >>= function
      | #Arch.arm | #Arch.thumb -> Arm.run ~link addr
      | _ -> Generic.run ~link addr
  end in
  (module Code)

module LinkBinaryProgram (Machine : Machine) = struct
  open Machine.Syntax
  module Linker = Linker.Make (Machine)
  module Memory = Primus.Memory.Make (Machine)
  module Interp = Interpreter.Make (Machine)

  let link_dynamic ?tid ?name addr =
    Machine.Local.update dynamic ~f:(fun linked -> Set.add linked addr)
    >>= fun () -> Linker.link ~addr ?tid ?name (dynamic_code addr)

  (* the block of the program, that the program stores to, in the
     virtual memory, not in another memory, e.g., of the symbolic
     executor, whose addresses are not of the code *)
  let changed (a, _) =
    let addr = Value.to_word a in
    Machine.Global.get code >>= fun { segments; index } ->
    Memory.memory >>= fun memory ->
    Machine.gets Project.target >>= fun target ->
    let virtual_memory () =
      String.equal
        (Primus.Memory.Descriptor.name memory)
        (Theory.Var.name (Theory.Target.data target))
    in
    if
      (not
         (List.exists segments ~f:(fun (lower, upper) ->
              Addr.(lower <= addr && addr <= upper))))
      || not (virtual_memory ())
    then Machine.return ()
    else
      let { blocks; blks; subs } = Lazy.force index in
      match Map.closest_key blocks `Less_or_equal_to addr with
      | Some (start, last) when Addr.(addr <= last) -> (
          Machine.Local.get dynamic >>= fun linked ->
          if Set.mem linked start then Machine.return ()
          else
            let tids = Map.find_multi blks start in
            (if List.is_empty tids then link_dynamic start
             else Machine.List.iter tids ~f:(fun tid -> link_dynamic ~tid start))
            >>= fun () ->
            match Map.find subs start with
            | Some (tid, name) -> link_dynamic ~tid ~name start
            | None -> Machine.return ())
      | _ -> Machine.return ()

  (* the executable address, that nothing is linked to, see the
     [unresolved] observation of the linker *)
  let unresolved = function
    | `addr addr -> (
        Memory.is_executable addr >>= function
        | true -> link_dynamic addr
        | false -> Machine.return ())
    | `symbol _ | `tid _ -> Machine.return ()

  let is_linked name t =
    [
      Linker.is_linked (`tid (Term.tid t)); Linker.is_linked (`symbol (name t));
    ]
    |> Machine.List.all >>| List.exists ~f:Fn.id
    >>= function
    | true -> Machine.return true
    | false -> (
        match Term.get_attr t address with
        | None -> Machine.return false
        | Some x -> Linker.is_linked (`addr x))

  let collect name t tids =
    is_linked name t >>= function
    | true -> tids >>| fun tids -> Set.add tids @@ Term.tid t
    | false -> tids

  let collector =
    object
      inherit [Tid.Set.t Machine.t] Term.visitor
      method! enter_blk = collect Term.name
      method! enter_sub = collect Sub.name
    end

  let link name code t m =
    m >>= fun () ->
    Linker.link ~name:(name t) ~tid:(Term.tid t) ?addr:(Term.get_attr t address)
      code

  let linker linked =
    object
      inherit [unit Machine.t] Term.visitor

      method! enter_blk t m =
        if not @@ Set.mem linked @@ Term.tid t then
          let module Code (Machine : Machine) = struct
            module Interp = Interpreter.Make (Machine)

            let exec = Interp.blk t
          end in
          link Term.name (module Code) t m
        else m

      method! enter_sub t m =
        if not @@ Set.mem linked @@ Term.tid t then (
          let module Code (Machine : Machine) = struct
            module Interp = Interpreter.Make (Machine)

            let exec = Interp.sub t
          end in
          info "Linking subroutine %s%!" @@ Sub.name t;
          link Sub.name (module Code) t m)
        else m
    end

  let init () =
    Machine.get () >>= fun proj ->
    let prog = Project.program proj in
    info "Linking binary program%!";
    collector#run prog !!Tid.Set.empty >>= fun linked ->
    (linker linked)#run prog !!() >>= fun () ->
    info "Finished linking binary program%!";
    Machine.sequence
      [
        Machine.Observation.observe Interpreter.stored changed;
        Machine.Observation.observe Bap_primus_linker.unresolved unresolved;
      ]
end
