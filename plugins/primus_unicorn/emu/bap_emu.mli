(** Runs a program in Unicorn, as the script drives it.

    The emulator runs the program of a project, e.g., of a bare project, which
    isn't disassembled, see [Bap_script.project], in a Primus system, by default
    the [bap:unicorn-executor], in which the code runs in Unicorn, and Primus
    runs the stubs, e.g., of libc, and the system calls. The script pauses and
    continues the program, reads and writes its registers and memory, and hooks
    its instructions, its memory accesses and the calls of its functions, as it
    would with Unicorn, e.g.,

    {[
      let emu = Bap_emu.create (Bap_script.project file) in
      Bap_emu.on_call emu "getuid" (fun _ -> Return 0L);
      match Bap_emu.run emu ~until:0x401000L with
      | Paused -> Bap_emu.set_reg emu "RAX" 42L
      | Exited code -> ...
    ]}

    The program runs in the fiber of the script, which it leaves, when it
    pauses, and the script continues it with {!run}. The emulators run side by
    side, e.g., of the programs of different targets, each in its own engine of
    Unicorn and its own Primus system, with its own registers, memory, names,
    hooks, stops of the debugger, and snapshots, e.g.,

    {[
    let a = Bap_emu.create (Bap_script.project x86_file) in
    let b = Bap_emu.create (Bap_script.project arm_file) in
    ignore (Bap_emu.step a);
    ignore (Bap_emu.step b)
    ]}

    The script, which runs in one thread, runs one of them at a time.

    See [docs/emulation.md] for the guide, with the examples of the hooks, the
    snapshots, the checkpoints, the taint, and the symbolic execution. *)

open Bap.Std

type t
(** the emulator *)

(** the state of the program *)
type status =
  | Paused  (** the program pauses, e.g., at the address of [until] *)
  | Running  (** the program runs, e.g., in a hook, which may only {!stop} it *)
  | Exited of int option  (** the program exited, with the code, if known *)
  | Failed of string  (** the program or the emulator failed *)

(** what a hook of a call does *)
type action =
  | Default  (** the function runs, e.g., its stub *)
  | Return of int64  (** the function returns the value at once *)

val create :
  ?system:string ->
  ?components:string list ->
  ?init:Bap_primus.Std.Primus.Machine.component list ->
  ?redirects:(string * string) list ->
  ?args:string list ->
  ?envp:string list ->
  ?entry:string ->
  ?restore:string ->
  project ->
  t
(** [create project] starts the program of [project], from [entry], by default
    its entry point, or [_start], in the [system], by default
    [bap:unicorn-executor], with the [components], e.g., [bap:debugger], the
    program arguments [args], without the name of the program, and the
    environment [envp], and pauses it before its first instruction runs in
    Unicorn.

    The components of [init], e.g., [Bap_script_debugger.component], and the
    [redirects] of the channels of the program, e.g.,
    [[ ("<stdin>", "input.txt") ]], run in the machine after the components of
    the system, before the program starts.

    With [restore] the program continues from the checkpoint in the file, see
    {!save}, instead of the [entry], and pauses before its address. *)

val run : ?until:int64 -> t -> status
(** [run emu] continues the program, until it pauses, e.g., before the
    instruction at [until], or by {!stop}, or exits. *)

val step : t -> status
(** [step emu] runs one instruction in Unicorn. *)

val status : t -> status
(** the state of the program *)

val stop : t -> unit
(** [stop emu] pauses the program, e.g., in a hook, before the next instruction.
*)

val pc : t -> int64
(** the address of the next instruction, with the lower bit set in the Thumb
    state of ARM *)

val set_pc : t -> int64 -> unit
(** [set_pc emu addr] continues the program from [addr], when it is paused *)

val registers : t -> string list
(** the names of the registers of the target, e.g., [RAX] *)

val reg : t -> string -> int64
(** [reg emu name] the value of the register, at most 64 bits wide, raises
    [Invalid_argument] for the unknown register. *)

val set_reg : t -> string -> int64 -> unit
(** [set_reg emu name x] writes [x] to the register. *)

val read : t -> int64 -> int -> string
(** [read emu addr n] reads [n] bytes from [addr], raises [Invalid_argument], if
    Primus would fault on any of them, or, in a hook, if their page is not in
    Unicorn yet, which a paused program copies. *)

val write : t -> int64 -> string -> unit
(** [write emu addr data] stores the bytes to the memory of the machine in
    Primus, also to the read-only pages, e.g., to the code, from which they go
    to Unicorn, which translates the changed code anew, so that they stay, as
    the program changed them, e.g., after {!snapshot} or {!restore} of a later
    snapshot, and the instructions, that Primus interprets, or whose registers
    the executor tracks, are decoded and lifted anew from them.

    Raises [Invalid_argument] as {!read} does, or if the program is not paused,
    e.g., in a hook, where {!write_direct} writes. *)

val write_direct : t -> int64 -> string -> unit
(** [write_direct emu addr data] writes the bytes to Unicorn, also to the code,
    as the debuggers do, raises [Invalid_argument] as {!read} does. It is the
    only write in the hooks.

    {b Warning:} the bytes of a read-only page, e.g., of the code, go only to
    the copy of the page in Unicorn, not to the memory of the machine in Primus,
    so they are lost, when Unicorn copies the page anew, e.g., after
    {!snapshot}, which forks the machine, or after the protection of the page
    changes, and Primus doesn't see them, e.g., when it interprets the code of
    the page, see the taint and the symbolic execution. Use {!write} for the
    code, that must stay changed.

    The writable pages have no such problem, as their changes go to Primus. *)

val bir : ?thumb:bool -> t -> int64 -> (int * blk term list) option
(** [bir emu addr] is the size and the BIR of the instruction at [addr], lifted
    on demand from the bytes, that the program has there now, e.g., after
    {!write}, as Primus lifts it, when it interprets the instruction, e.g., of
    the tainted or the symbolic values, or [None], if the bytes aren't an
    instruction. The instruction is in the Thumb state of ARM, if [thumb], by
    default, if the lower bit of [addr] is set, as in the program counter.

    The jumps to the addresses outside of the instruction are the indirect jumps
    to the constant addresses, and the instruction, that falls through, has no
    jump to the next one. The instructions are cached by their addresses and
    bytes, see [Primus.Lift], in the knowledge of the emulator. In a hook, e.g.,
    of {!on_code}, the machine runs the program, so the instruction is lifted
    outside of it, as [Primus.Lift.instruction] does, in the knowledge, that the
    emulator keeps for the hooks, and is cached there.

    Raises [Invalid_argument], if [addr] is not mapped, e.g., in a hook, if its
    page is not in Unicorn yet. *)

(** The traces of the program counters, which the native hooks of Unicorn record
    in a ring, with no call to OCaml. The trace of the blocks costs the least,
    the program runs about three times slower, and {!Trace.insns} gives the
    instructions of its blocks, while the trace of each instruction makes it run
    tens of times slower, as Unicorn calls its hook for each one, which is still
    faster, than {!on_code}, whose closure runs for each one. The instructions,
    that Primus runs, e.g., the Lisp stubs, or the code, that uses the tainted
    or the symbolic values, aren't in the trace.

    {[
    let trace = Emu.Trace.start ~blocks:true emu in
    ignore (Emu.run emu);
    Emu.Trace.insns trace
    ]} *)
module Trace : sig
  type emu := t
  type t

  val start :
    ?size:int ->
    ?every:int ->
    ?blocks:bool ->
    ?accesses:int ->
    ?first:int64 ->
    ?last:int64 ->
    emu ->
    t
  (** [start emu] records the program counters of the last [size] instructions,
      at least, by default of 2{^ 20}, from [first] to [last], by default of
      all, every [every]-th one, by default each, or of the first instructions
      of the blocks, with their sizes, if [blocks], which costs the least, and
      the last [accesses] accesses to the memory, by default none, which
      {!slice} needs to follow the memory, and which only the traces of all
      instructions, or of the blocks, record.

      The instruction, that Unicorn stops at, before it runs it, e.g., at a
      stop, or at a fault, which it repeats, isn't recorded, and the block, that
      it leaves there, ends there, unless only every [every]-th instruction is
      recorded, which may record it twice.

      Raises [Invalid_argument], if [accesses] is positive, and the instructions
      are sampled, or the ones of a range are recorded. *)

  val stop : t -> unit
  (** [stop trace] stops recording, the trace keeps the records *)

  val count : t -> int64
  (** the number of the recorded instructions, or blocks, also of those, that
      the ring doesn't keep anymore *)

  val clear : t -> unit
  val blocks : t -> bool

  val pcs :
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the last program counters, at most [last], by default all, that the ring
      keeps, the oldest first *)

  val sizes :
    ?last:int ->
    t ->
    (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the sizes of the last blocks, as {!pcs}, of the trace of the blocks *)

  val save : ?last:int -> t -> string -> int64
  (** [save trace file] writes the last program counters, as {!pcs}, one in hex
      a line, and returns their number *)

  type access = {
    insn : int64;
        (** the index of the record of the instruction, or of its block, as
            {!step.index} *)
    pc : int64;  (** of the instruction, in a trace of the blocks *)
    addr : int64;
    size : int;
    write : bool;
    value : int64;  (** the written value *)
    old : int64;
        (** the bytes, that a write of at most 8 bytes overwrote, the first one
            in the lowest byte *)
  }

  val accesses : ?last:int -> t -> access list
  (** the last accesses to the memory, the oldest first *)

  val insns :
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the program counters of the instructions of the last [last] records, by
      default of all, that the ring keeps, the oldest first, of the blocks too,
      whose instructions are decoded once, from the bytes, that they have now *)
end

type location =
  | Reg of string
  | Mem of int64 * int
      (** a register, by the name of the variable of BIR, e.g., [RAX], the case
          of which doesn't matter, or the bytes from an address *)

type step = {
  index : int64;
      (** the position of the instruction in the trace, from the first recorded
          one *)
  pc : int64;
}

type slice = {
  steps : step list;  (** the oldest first *)
  live : location list;
      (** the locations, whose values come from before the window *)
  gaps : int64 list;
      (** the indices of the records, the latest first, before which, or before
          one of whose instructions, e.g., in a hook, the registers, or the
          memory, were written outside of the trace, e.g., by the code, that
          Primus runs, or by the script, while the slice had live registers, or
          memory, respectively, whose values may come from there *)
  complete : bool;
      (** if nothing comes from before the window, or from outside of the trace,
          and the memory, that the steps load, is in the trace *)
}

val slice : ?addresses:bool -> ?window:int -> Trace.t -> location list -> slice
(** [slice trace locations] the dynamic backward slice of the values of the
    [locations], as the paused program has them, over the last [window]
    instructions of the trace, by default all, that it keeps: the instructions,
    whose values flow to them, through the registers, and, if the trace has the
    accesses, through the memory, at the addresses, that they had, and through
    the addresses of the loads and the stores, if [addresses].

    It is a slice of the data: the jumps aren't followed, but the conditions of
    the defs, that an instruction may skip, e.g., of a compare and exchange,
    are, as of a conditional move, and the registers stay live. The instructions
    are lifted from the bytes, that they had, if the trace has the writes, that
    patched them, or else that they have now, in their modes, e.g., A32 or Thumb
    of ARM, that the trace records, and the IT blocks of Thumb in their order.
    The loads and the stores of an instruction are its accesses, if their sizes
    are the same, e.g., of the multiple registers of ARM. The code, that Primus
    runs, e.g., the Lisp stubs, isn't in the trace, so the values, that it
    computes, are missed, and the slice has the [gaps]: the bytes, that were
    written there, come from it, and the registers, which aren't known, are
    followed further.

    The instructions of a trace of the blocks are those of {!Trace.insns}, and
    their steps have the indices of their blocks. *)

val primus : t -> Bap_primus.Std.Primus.Machine.component -> unit
(** [primus emu component] runs the [init] of the [component] in the Primus
    machine of the program, which is paused, or ended, so that the script uses
    the whole API of Primus, e.g., its environment, memory, linker, Lisp, or the
    taint tracker, whose results the script gets, e.g., with references, and
    whose changes, e.g., of the registers and the memory, the program sees, when
    it continues, e.g.,

    {[
    let rax = ref Word.b0 in
    Bap_emu.primus emu
      (module functor
                (Machine : Primus.Machine.S)
                ->
                struct
                  module Env = Primus.Env.Make (Machine)
                  open Machine.Syntax

                  let init () =
                    Env.get (Var.create "RAX" reg64_t) >>| fun x ->
                    rax := Primus.Value.to_word x
                end)
    ]}

    The [init] may observe the program, e.g., with
    [Machine.Observation.observe], as the components do, and its observers stay.
    Raises [Invalid_argument], if the program is not paused, e.g., in a hook. *)

val on_code : ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> unit) -> unit
(** [on_code emu f] calls [f emu addr] before each instruction from [first] to
    [last], inclusive, by default of all. The instruction, that the hook saw,
    when the program paused before it, e.g., as the hook stopped it, is not seen
    again, when the program continues from it, so the hook may stop the program
    unconditionally. *)

val on_read :
  ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> int -> unit) -> unit
(** [on_read emu f] calls [f emu addr size] before each load. *)

val on_write :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  (t -> int64 -> int -> int64 -> unit) ->
  unit
(** [on_write emu f] calls [f emu addr size value] before each store. *)

val on_call : t -> string -> (t -> action) -> unit
(** [on_call emu name f] calls [f emu] when the program calls the function,
    e.g., an external one, before its stub, or one of the program, which [f] may
    replace, see {!action}, and whose arguments {!arg} reads. *)

val arg : t -> int -> int64
(** [arg emu n] the [n]th argument of the function, which is called, from 0, as
    its prototype tells, e.g., from the api files. *)

val exit_code : t -> int option
(** the code, with which the program exited *)

val knowledge : t -> Bap_knowledge.Knowledge.state option
(** the knowledge of the system, when it finished, e.g., of the instructions,
    that it lifted, see [Primus.Lift], and what its components computed, or
    [None], while the program runs, e.g., when it is paused. The system, whose
    program ended, finishes, after which its snapshots are not restored. The
    system starts from the toplevel knowledge, see [Toplevel.current], and its
    knowledge doesn't go there, as each emulator has its own knowledge. *)

type snapshot
(** the saved state of the paused program, its registers and its memory *)

val snapshot : t -> snapshot
(** [snapshot emu] saves the state of the paused program, which the program
    continues from, when it is restored, as many times, as the script restores
    it. *)

val restore : t -> snapshot -> unit
(** [restore emu snapshot] drops the state of the paused program, which
    continues from the [snapshot], paused at its address. The hooks of the
    script stay.

    Raises [Invalid_argument], if the [snapshot] is of another emulator. *)

val save : t -> string -> unit
(** [save emu file] saves the checkpoint of the paused program to the [file],
    from which {!create} continues it, in another run of bap too, e.g.,

    {[
      ignore (Bap_emu.run emu ~until:after_unpack);
      Bap_emu.add_symbol emu "decrypt" 0x602000L;
      Bap_emu.save emu "unpacked.ckpt";
      ...
      let emu = Bap_emu.create ~restore:"unpacked.ckpt" proj in
      Bap_emu.on_call emu "decrypt" (fun _ -> ...)
    ]}

    The checkpoint has the registers, the memory, as the program and the script
    changed it, the names of {!add_symbol}, the functions of {!unstub}, the
    states of the components, that extend the checkpoints, see
    [Primus.Checkpoint], e.g., the channels of Primus Lisp, which are opened
    anew, with the positions of their inputs, the digest of the file of the
    program, which the checkpoint is of, and the runs of Unicorn, that Primus
    called, with the stubs, that called them. The names of the program and its
    stubs are of its file, which is loaded anew.

    The program, that continues from the checkpoint, continues the innermost
    run, after which the stub, that called it, completes, if it is known, see
    {!complete}, e.g., __libc_start_main exits with the result of main, as the
    code of the stubs is not data, and the program ends.

    Raises [Invalid_argument], if the program is not paused, e.g., in a hook,
    and [Failure], if the checkpoint can't be saved. *)

(** what a stub does, after the function, that it called, returns, see
    {!complete} *)
module type Completion = functor
  (Machine : Bap_primus.Std.Primus.Machine.S)
  -> sig
  val complete : callee:string option -> unit Machine.t
  (** [complete ~callee] completes the stub, after [callee], the function of the
      program, that it called, if its name is known, returned, e.g., exits with
      its result. *)
end

val complete : string -> (module Completion) -> unit
(** [complete stub completion] completes the [stub], e.g., the Lisp stub of
    [__libc_start_main], whose run of the program, that continues from a
    checkpoint, see {!save}, returned, as [__libc_start_main] does by default,
    which exits with the result of [main]. *)

val add_symbol : t -> string -> int64 -> unit
(** [add_symbol emu name addr] names the function at the address of its first
    instruction, e.g., in the code, that the program unpacked, or moved, which
    replaces the name, that the address had, so that {!on_call} hooks it by the
    name, also the hooks that are already there, and the checkpoints have it,
    see {!save}. *)

val symbols : t -> (string * int64) list
(** the names of the functions and their addresses, of the program and of
    {!add_symbol}, in the order of the addresses *)

val unstub : t -> string -> unit
(** [unstub emu name] runs the code of the function of the program in Unicorn
    again, instead of the stub, that replaced it, e.g., the Lisp stub of
    [malloc] of a static program, e.g., after the script patched the code, see
    {!write}, also when Primus calls the function, e.g., from another stub. The
    checkpoints keep it, see {!save}.

    Raises [Invalid_argument], if the program has no code of the function, e.g.,
    if it is external, or if it is not paused, e.g., in a hook. *)

(** The taint of the values, that the program computes.

    Primus tracks the taint, see the [bap-taint] library, as the program runs in
    Unicorn, which leaves the instructions, that use the tainted values, to
    Primus, so that the taint propagates through the computations, the loads and
    the stores, e.g.,

    {[
      let emu = Bap_emu.create ~components:Bap_emu.Taint.components proj in
      ignore (Bap_emu.run emu ~until:after_read);
      Bap_emu.Taint.introduce emu ~kind:"input" (Mem (buf, len));
      Bap_emu.Taint.on_jump emu (fun _ ~kinds dst -> ...);
      Bap_emu.run emu
    ]}

    The functions, except the callbacks, run, when the program is paused, or
    ended, see {!primus}. *)
module Taint : sig
  (** the place of the values, whose taint is introduced or queried *)
  type place =
    | Reg of string
        (** the value of the register, e.g., [RAX], or of its base register, if
            it is an alias, e.g., the whole [R0] for [X0] or [W0] of AArch64, or
            for [V0] of MIPS, as the code reads the base registers *)
    | Mem of int64 * int
        (** the values of the bytes of the memory from the address *)

  val components : string list
  (** the components of the system, that propagate the taint, by the
      computations, which {!create} needs *)

  val introduce : t -> kind:string -> place -> unit
  (** [introduce emu ~kind place] taints the values of the [place] with a new
      taint of the [kind], e.g., ["input"], the value of the register directly,
      and the bytes of the memory indirectly, i.e., the values, that the program
      loads from them. *)

  val kinds : t -> place -> string list
  (** [kinds emu place] the kinds of the taints of the values of the [place],
      i.e., of the value of the register, or of the locations of the memory. *)

  val is_tainted : t -> kind:string -> place -> bool
  (** [is_tainted emu ~kind place] if the [place] has a taint of the [kind] *)

  val sanitize : t -> kind:string -> place -> unit
  (** [sanitize emu ~kind place] removes the taints of the [kind] of the
      [place], from all values, that they taint. *)

  val on_jump : t -> (t -> kinds:string list -> int64 -> unit) -> unit
  (** [on_jump emu f] calls [f emu ~kinds dst] when the program jumps to [dst]
      on a condition, that the taints of the [kinds] taint. The callback runs,
      when the program runs, so it may only {!stop} it. *)
end

(** The symbolic execution of the values, that the program computes.

    Primus computes the formulas of the values, that the program computes from
    the inputs, which the script makes symbolic, see the
    [bap-primus-symbolic-executor] plugin, as the program runs in Unicorn, which
    leaves the instructions, that use the symbolic values, to Primus, and
    collects the constraints of the path, i.e., the conditions of the branches,
    that the program takes, whose models the SMT solver finds, e.g.,

    {[
    let emu = Bap_emu.create ~components:Bap_emu.Symbolic.components proj in
    ignore (Bap_emu.run emu ~until:after_getchar);
    Bap_emu.Symbolic.symbolize emu (Reg "RAX");
    Bap_emu.Symbolic.on_branch emu (fun _ b -> branches := b :: !branches);
    ignore (Bap_emu.run emu);
    List.map !branches ~f:Bap_emu.Symbolic.flip
    ]}

    The functions, except the callbacks and {!flip}, run, when the program is
    paused, or ended, see {!primus}. The solver has the [timeout] milliseconds,
    by default 16, to find a model. *)
module Symbolic : sig
  (** the place of the values, see {!Taint.place} *)
  type place = Taint.place = Reg of string | Mem of int64 * int

  type model = (string * int64) list
  (** the values of the inputs, e.g., [RAX], or [mem[0x7ffffff0]] for a byte of
      the memory, that satisfy the constraints *)

  type branch
  (** a branch of the program on a symbolic condition *)

  val components : string list
  (** the components of the system, that compute the formulas and collect the
      constraints of the path, which {!create} needs *)

  val symbolize : t -> place -> unit
  (** [symbolize emu place] makes the values of the [place] the inputs, named
      after the place, whose values are symbolic, i.e., the value of the
      register, or each byte of the memory, whose concrete values stay. *)

  val formula : t -> place -> string option list
  (** [formula emu place] the formulas of the values of the [place], one for a
      register, and one per byte of the memory, [None] for a concrete value. *)

  val solve : ?timeout:int -> t -> model option
  (** [solve emu] a model of the constraints of the path, that the program took,
      [None], if the solver finds none, e.g., in time. *)

  val on_branch : t -> (t -> branch -> unit) -> unit
  (** [on_branch emu f] calls [f emu branch] when the program decides a branch
      on a symbolic condition. The callback runs, when the program runs, so it
      may only {!stop} it. *)

  val addr : branch -> int64
  (** the address of the instruction of the branch *)

  val taken : branch -> bool
  (** if the condition of the branch held *)

  val condition : branch -> string
  (** the formula of the condition *)

  val flip : ?timeout:int -> branch -> model option
  (** [flip branch] a model of the inputs, with which the program takes the path
      to the branch, and decides the branch otherwise, [None], if the solver
      finds none. *)
end
