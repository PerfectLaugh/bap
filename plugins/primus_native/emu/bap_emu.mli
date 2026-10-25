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
  | Running
      (** the program runs, e.g., in a hook, which may {!stop} it, or {!defer}
          an action to the pause *)
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
  ?engine:[ `Unicorn | `Lifted ] ->
  project ->
  t
(** [create project] starts the program of [project], from [entry], by default
    its entry point, or [_start], in the [system], by default
    [bap:lifted-executor], or [bap:unicorn-executor] of the Unicorn [engine],
    with the [components], e.g., [bap:debugger], the program arguments [args],
    without the name of the program, and the environment [envp], and pauses it
    before its first instruction runs in Unicorn.

    The components of [init], e.g., [Bap_script_debugger.component], and the
    [redirects] of the channels of the program, e.g.,
    [[ ("<stdin>", "input.txt") ]], run in the machine after the components of
    the system, before the program starts.

    The [redirects] serve the files of the host to the program, by the paths,
    that it opens, which are the only files, that it may open, e.g.,

    {[
    Emu.create
      ~redirects:[ ("/data/app/base.apk", "app.apk"); ("<stdout>", "out.txt") ]
      proj
    ]}

    and the stubs of Primus Lisp, [open], [fopen], [read], [fread], [fgets],
    [lseek], [fseek], [ftell], and [close], read them, also the read-only ones,
    with the descriptors, that [open] returns, or [-1], for the paths, that
    aren't redirected. The program, that maps a file with [mmap], gets [ENODEV],
    and a script, that serves its own descriptors, e.g., of the file, that the
    program reads with the system calls, replaces their functions with
    {!on_call}.

    With [restore] the program continues from the checkpoint in the file, see
    {!save}, instead of the [entry], and pauses before its address.

    The native code runs in the [engine]: [`Unicorn], or [`Lifted], the lifted
    engine, see [Bap_lifted], which runs the semantics of the instructions, that
    BAP lifts. By default, it is the engine of the [system], e.g., [`Unicorn] of
    [bap:unicorn-executor], or, without the [system], [`Unicorn], if the
    environment variable [BAP_EMU_ENGINE] is [unicorn], e.g., in the testsuite,
    or else [`Lifted]. The options of the plugin of the engine, e.g.,
    [--primus-lifted-timeout], apply to the program. *)

val run : ?until:int64 -> t -> status
(** [run emu] continues the program, until it pauses, e.g., before the
    instruction at [until], or by {!stop}, or exits. *)

val step : t -> status
(** [step emu] runs one instruction in Unicorn. *)

val interpret : t -> status
(** [interpret emu] runs the instruction, at which the program paused, in
    Primus, which interprets its lifted semantics, e.g., to compare them with
    {!step}, after which the program pauses at the next one, or the status
    tells, why it failed, e.g., an instruction without semantics. Raises
    [Invalid_argument], if the program is not paused. *)

val status : t -> status
(** the state of the program *)

val stop : t -> unit
(** [stop emu] pauses the program, e.g., in a hook, before the next instruction.
*)

val defer : t -> (t -> unit) -> unit
(** [defer emu f] runs [f emu], when the program is paused: at once, if it is,
    or, in a hook, where the machine runs the program and serves no request of
    the script, so that most of the functions raise, at the pause, that the hook
    asks for, i.e., before the instruction, that a hook of the code sees, or
    after the one, that accessed the memory, in a hook of {!on_read} or
    {!on_write}, after which the program continues, unless a hook also
    {!stop}ped it. [f] may do what a paused program allows, e.g., {!save},
    {!read} a page, that is not in Unicorn yet, {!regions}, {!project}, or
    {!snapshot}, and raises from the function, that runs the program, e.g.,
    {!run}, if it raises:

    {[
      Emu.on_code emu ~first:decrypted ~last:decrypted (fun emu _ ->
          Emu.defer emu (fun emu ->
              let proj = Emu.project emu in
              ...))
    ]}

    Raises [Invalid_argument], if the program ended. *)

val shell :
  ?input:In_channel.t -> ?output:Out_channel.t -> ?prompt:string -> t -> status
(** [shell emu] reads the commands of the debugger, see [bap:debugger], from
    [input], the standard input by default, and runs them on the paused program,
    until [q], or the end of the input, after which it returns the status of the
    program, so that the script goes on, e.g., at a breakpoint:

    {[
    match Emu.run emu ~until:suspicious with
    | Paused -> ignore (Emu.shell emu)
    | _ -> ()
    ]}

    The commands continue and step the program, set and delete breakpoints, show
    and set the registers, dump and write the memory, show the instruction the
    lifted engine ran at an address, see {!insn_at}, and its BIR, see {!bir},
    call a function, see {!call}, list the functions and the regions, take and
    restore snapshots, save a checkpoint, and exit bap; [help] lists them. An
    address is a number, e.g., [0x400000], the name of a function, or a
    register, whose value it is, e.g., [x RDI 16]. The breakpoints stay, while
    the emulator does, and stop the program, also when the script runs it. A
    command, that fails, says so, and the shell stays. The commands of a file
    are shown after the prompt, as the ones, that are typed, are. The prompt,
    [(emu) ] by default, and the output go to [output], the standard output by
    default.

    In a hook, the shell opens at the pause, that the hook asks for, see
    {!defer}, and returns [Running] at once. *)

val pc : t -> int64
(** the address of the next instruction, with the lower bit set in the Thumb
    state of ARM, or, in a hook, e.g., of {!on_write}, of the instruction, that
    runs, e.g., the one, that stores *)

val set_pc : t -> int64 -> unit
(** [set_pc emu addr] continues the program from [addr], when it is paused *)

val registers : t -> string list
(** the names of the registers of the target, e.g., [RAX] *)

val reg : t -> string -> int64
(** [reg emu name] the value of the register, at most 64 bits wide, raises
    [Invalid_argument] for the unknown register. *)

val set_reg : t -> string -> int64 -> unit
(** [set_reg emu name x] writes [x] to the register. *)

val reg_word : t -> string -> word
(** [reg_word emu name] the whole value of the register, of its width, e.g., of
    the 256 bits of YMM0, raises [Invalid_argument] for the unknown register. *)

val set_reg_word : t -> string -> word -> unit
(** [set_reg_word emu name x] writes the bits of [x], of the width of the
    register, to the register. *)

val read : t -> int64 -> int -> string
(** [read emu addr n] reads [n] bytes from [addr], raises [Invalid_argument], if
    Primus would fault on any of them, or, in a hook, if their page is not in
    Unicorn yet, which a paused program copies, as the machine runs the program
    and can't be asked for the page: {!defer} the read to the pause, to read it.
    A read never makes bytes up: the bytes, that it returns, are the ones, that
    the program has. *)

val write : t -> int64 -> string -> unit
(** [write emu addr data] stores the bytes to the memory of the machine in
    Primus, also to the read-only pages, e.g., to the code, from which they go
    to Unicorn, which translates the changed code anew, so that they stay, as
    the program changed them, e.g., after {!snapshot} or {!restore} of a later
    snapshot, and the instructions, that Primus interprets, or whose registers
    the executor tracks, are decoded and lifted anew from them.

    Raises [Invalid_argument] as {!read} does, or if the program is not paused,
    as it runs, e.g., in a hook, where {!write_direct} writes, or {!defer}
    writes at the pause. *)

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
    default, if the lower bit of [addr] is set, as in the program counter. The
    instruction of an IT block of Thumb has its condition, as the block is
    decoded from its IT instruction.

    The jumps to the addresses outside of the instruction are the indirect jumps
    to the constant addresses, and the instruction, that falls through, has no
    jump to the next one. The instructions are cached by their addresses and
    bytes, see [Primus.Lift], in the knowledge of the emulator. In a hook, e.g.,
    of {!on_code}, the machine runs the program, so the instruction is lifted
    outside of it, as [Primus.Lift.instruction] does, in the knowledge, that the
    emulator keeps for the hooks, and is cached there.

    Raises [Invalid_argument], if [addr] is not mapped, e.g., in a hook, if its
    page is not in Unicorn yet. *)

type executed = {
  bytes : string;  (** the bytes of the instruction, from which it was lifted *)
  name : string;  (** the name of the instruction, e.g., [MOV64rr] *)
  thumb : bool;  (** if it is in the Thumb state of ARM *)
  bir : blk term list;  (** its semantics, that the engine runs *)
}
(** an instruction, that the lifted engine ran, see {!insn_at} *)

val insn_at : ?thumb:bool -> t -> int64 -> executed option
(** [insn_at emu pc] is the instruction, that the lifted engine lifted at [pc],
    to run it, in this run, from the bytes, that the program had there then,
    which the engine keeps, while the memory may not have them anymore, e.g.,
    when the program scrubbed the code, that it unpacked, after it ran, or
    overwrote it, so {!read} gives other bytes, and {!bir} lifts them. The
    instruction is the last one lifted at [pc]: the engine lifts the code anew,
    when its bytes change, before it runs it, and it lifts the instructions of a
    block, which it compiles, a few ahead of the one, that runs. [None], if the
    engine lifted nothing at [pc], or the engine is Unicorn, which translates
    the code in itself, where the script doesn't see it. The instruction is in
    the Thumb state, if [thumb], by default, if the lower bit of [pc] is set, as
    in {!bir}. Also in the hooks.

    The checkpoints keep the bytes of the instructions, that ran, see {!save},
    so the program, that continues from one, has the instructions, that ran
    before it, which are lifted anew from them, unless they ran again since. *)

val insns : t -> int64 list
(** [insns emu] the addresses of the instructions, that {!insn_at} has, in their
    order, also of the ones, that ran before the checkpoint, from which the
    program continues, with the lower bit set in the Thumb state of ARM, e.g.,
    to list the code, that the program unpacked and ran, after it scrubbed it,
    or none, if the engine is Unicorn. *)

val insns_since : t -> string -> int64 list
(** [insns_since emu file] the addresses of the instructions, that {!insns} has,
    and the checkpoint in the [file] doesn't, see {!Checkpoint.insns}, e.g., of
    the code, that an action ran for the first time, after the checkpoint was
    saved before it, in their order:

    {[
    Emu.save emu "before.ckpt";
    ignore (Emu.call emu handler ~args:[ request ]);
    List.iter (Emu.insns_since emu "before.ckpt") ~f:(fun pc ->
        printf "%Lx %s\n" pc
          (Option.value (Emu.function_at emu pc) ~default:"?"))
    ]}

    The instructions are the ones, that ran for the first time: an instruction,
    that ran before the checkpoint, and again since, is not there, which a trace
    of the action tells, see {!Trace}, as are the few, that the engine lifted
    after a branch, without running them. Raises [Failure], if the file is not a
    checkpoint. *)

val lifted_bytes : ?thumb:bool -> t -> int64 -> int -> string
(** [lifted_bytes emu addr n] are the bytes of the instructions, that the lifted
    engine ran, see {!insn_at}, from [addr], one after another, as far as they
    go, at most [n], e.g., of a function, that ran, whose bytes the program
    scrubbed: fewer, than [n], if an instruction after them didn't run, e.g.,
    after a branch, that was never taken, or none. *)

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
    ?watch:int64 * int64 ->
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

      With [watch], [(lower, upper)], only the accesses, whose first byte is
      from [lower] to [upper], inclusive, are recorded, by default the last
      2{^ 16} of them, natively, as the others, so that the ring keeps them over
      a long run, e.g., to find, who writes a slot of a queue, while the program
      spins on it, with a trace of the blocks, which costs the least, and
      {!slice} doesn't follow the memory in such a trace.

      Raises [Invalid_argument], if [accesses] is positive, or a range is
      watched, and the instructions are sampled, or the ones of a range are
      recorded. *)

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

  val hot : ?last:int -> ?top:int -> t -> (int64 * int) list
  (** [hot trace] the program counters of the last [last] records, by default of
      all, that the ring keeps, of the instructions, or of the blocks, with
      their numbers, the [top] ones, by default all, that run most, first, e.g.,
      the loop, in which the program spins *)

  val addresses : ?last:int -> ?top:int -> t -> (int64 * int * int) list
  (** [addresses trace] the addresses of the last [last] accesses, as {!hot},
      with the numbers of their reads and their writes, the [top] ones, that are
      accessed most, first, e.g., the slot, that a loop polls, in a trace, that
      records the accesses, or watches them *)

  val insns :
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the program counters of the instructions of the last [last] records, by
      default of all, that the ring keeps, the oldest first, of the blocks too,
      whose instructions are decoded once, from the bytes, that they have now *)

  type capture
  (** the registers at the sites, see {!capture} *)

  val capture : ?size:int -> ?regs:string list -> emu -> int64 list -> capture
  (** [capture emu sites] records the [regs], by default the registers, that the
      C ABI of the target passes the arguments in, in their order, e.g., X0 to
      X7 of AArch64, each time the program reaches one of the [sites], the
      addresses of the instructions, e.g., the sites of the calls of a function,
      see {!calls}, in a ring of the last [size] records, by default 2{^ 16},
      which is its own, so that a long run doesn't lose them, e.g., to map the
      arguments, that a function gets, in one run. The sites are hooked as
      {!Bap_emu.on_sites} does, so each record costs a call to OCaml, and the
      other instructions don't. *)

  val captured : ?last:int -> capture -> (int64 * int64 list) list
  (** [captured c] the last records, at most [last], by default all, that the
      ring keeps, the oldest first: the site, and the values of the registers,
      in the order of [regs] *)

  val captures : capture -> int64
  (** the number of the records, also of those, that the ring doesn't keep
      anymore *)

  val stop_capture : capture -> unit
  (** [stop_capture c] stops recording, the ring keeps the records *)

  val calls : ?last:int -> t -> (int64 * (int64 * int) list) list
  (** [calls trace] the calls of the last [last] records, by default of all,
      that the ring keeps, by their sites, the instructions, that call, in the
      order of their addresses, with the addresses, that they called, which the
      next instructions are at, and how many times each, the most often first,
      e.g., the targets, that the indirect call of a dispatcher took. The call,
      whose next instruction is the one after it, isn't taken, e.g., a
      conditional one. The instructions are those of {!insns}, so a trace of the
      blocks has them. *)

  val branches : ?last:int -> t -> (int64 * int64 * bool) list
  (** [branches trace] the conditional branches of the last [last] records, by
      default of all, that the ring keeps, in their order: the address of the
      branch, the address, that the program went to, and if the branch was
      taken, i.e., the program didn't fall through, e.g., the path, that a call
      took, see {!Bap_emu.record}, whose branches tell, which check rejected its
      inputs. A branch is an instruction, whose jump on a condition leaves it,
      so a conditional instruction of ARM, which jumps over its own body, isn't
      one. The instructions are those of {!insns}, so a trace of the blocks has
      them. *)
end

type 'a recorded = {
  result : ('a, string) result;
      (** what the function returned, or the message of the [Failure], that it
          raised, e.g., of a call, whose function failed *)
  trace : Trace.t;  (** the trace of the instructions, that ran *)
}

val record : ?size:int -> t -> (unit -> 'a) -> 'a recorded
(** [record emu f] runs [f], e.g., a {!call}, with a trace of all instructions
    of its own, see {!Trace.start}, of the last [size] records, by default
    2{^ 20}, which stops, when [f] returns, or raises, so that the trace has the
    path, that the program took in [f] only, e.g., of the callee: its
    instructions, {!Trace.insns}, its conditional branches, {!Trace.branches},
    and its calls, {!Trace.calls}, also when the call failed, e.g., with a
    segmentation fault, whose message is the result, so that one call tells,
    which branch rejected its inputs, e.g.,

    {[
    let r = Emu.record emu (fun () -> Emu.call emu check ~args:[ stream ]) in
    List.iter (Emu.Trace.branches r.trace) ~f:(fun (site, dst, taken) ->
        printf "%Lx -> %Lx %s\n" site dst (if taken then "taken" else "fell"))
    ]}

    The other exceptions of [f], e.g., [Invalid_argument], are raised. *)

type location = Bap_emu_slice.location =
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
    Raises [Invalid_argument], if the program is not paused, as it runs, e.g.,
    in a hook. *)

val on_code : ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> unit) -> unit
(** [on_code emu f] calls [f emu addr] before each instruction from [first] to
    [last], inclusive, by default of all. The instruction, that the hook saw,
    when the program paused before it, e.g., as the hook stopped it, is not seen
    again, when the program continues from it, so the hook may stop the program
    unconditionally. *)

val on_sites : t -> int64 list -> (t -> int64 -> unit) -> unit
(** [on_sites emu sites f] calls [f emu addr] before each instruction at one of
    the [sites], with the lower bit set for Thumb, as {!on_code} does, at
    [addr], without the lower bit, with one hook, which the engine finds the
    sites of natively: the lifted engine looks the address up in a set, rather
    than checking each hook, and Unicorn has a hook for each cluster of the
    sites, that are close, which finds them in C, so that only the sites call
    OCaml, e.g., for a table of thousands of the addresses, that a script
    watches, which, with a hook of {!on_code} each, would cost a check of each
    hook at each of their instructions, and a change of the hooks of the engine
    each:

    {[
    Emu.on_sites emu (List.map handlers ~f:snd) (fun emu addr ->
        Hashtbl.incr hits addr)
    ]} *)

val on_read :
  ?first:int64 -> ?last:int64 -> t -> (t -> int64 -> int -> unit) -> unit
(** [on_read emu f] calls [f emu addr size] before each load. *)

val on_write :
  ?first:int64 ->
  ?last:int64 ->
  ?primus:bool ->
  t ->
  (t -> int64 -> int -> int64 -> unit) ->
  unit
(** [on_write emu f] calls [f emu addr size value] before each store, that the
    engine runs, from [first] to [last], inclusive, by default of all.

    With [primus], it also sees the stores, that the engine doesn't run: of
    Primus, e.g., of the Lisp stubs, e.g., [strcpy] or [fread], and of the
    instructions, that it interprets, e.g., of the tainted values, after each
    byte is stored, a byte at a time, and of the native functions of libc, which
    replace their Lisp stubs, e.g., [memcpy], before their bytes are stored, in
    the pieces of at most 8 bytes, whose values are of the endianness of the
    target, as the stores of the engine are, e.g., to watch a buffer, that the
    program fills with a function of libc:

    {[
    Emu.on_write emu ~first:buf
      ~last:Int64.(buf + 63L)
      ~primus:true
      (fun emu addr size _ ->
        printf "%Lx: %d bytes at %Lx\n" (Emu.pc emu) size addr)
    ]}

    The writes of the script, e.g., {!write}, aren't seen. A hook, that sees a
    store of Primus, runs in Primus, where the engine doesn't run, so {!pc} is
    of the instruction, that the engine ran last, e.g., the call of the stub,
    and {!stop} pauses the program before the next instruction, that runs in the
    engine. *)

val scoped : t -> (unit -> 'a) -> 'a
(** [scoped emu f] runs [f], and removes the hooks, that it added, when it
    returns, or raises: of {!on_code}, {!on_sites}, {!on_read}, {!on_write},
    {!on_call}, {!on_syscall}, and {!Trace.capture}, also the ones, that the
    scopes, that it runs, added, so that an experiment, e.g., of a {!call}, or
    of a {!drive}, doesn't leave its hooks to the program, that runs after it:

    {[
    let r =
      Emu.scoped emu (fun () ->
          Emu.on_call emu "getuid" (fun _ -> Return 0L);
          Emu.on_write emu ~first:buf ~last:Int64.(buf + 63L) ~primus:true log;
          Emu.drive emu handler ~args:[ request ] ~budget:100 ~service)
    ]}

    The function, that parked, see {!Parked}, continues without them, after the
    scope. The traces, see {!Trace.start}, the breakpoints of the shell, and the
    callbacks of {!Taint} and {!Symbolic} stay. *)

val on_call : t -> string -> (t -> action) -> unit
(** [on_call emu name f] calls [f emu] when the program calls the function,
    e.g., an external one, before its stub, or one of the program, which [f] may
    replace, see {!action}, and whose arguments {!arg} reads. *)

val on_syscall : t -> (t -> int64 -> int64 list -> action) -> unit
(** [on_syscall emu f] calls [f emu number args] at each system call of the
    program, that runs in Unicorn or in the lifted engine, e.g., [svc #0] of
    AArch64, or [syscall] of x86-64, with its [number], e.g., of [X8] of
    AArch64, and its six [args], as the ABI of Linux of the target passes them,
    whose result [Return x] returns from the call, as the ABI does, e.g., in
    [X0], and which the program then continues after, and [Default] serves, as
    without the hook: the calls of the threads, e.g., clone and futex, natively,
    and the others by the Lisp function of its intrinsic, e.g., [intrinsic:svc],
    if one is defined, or else the program fails, with the unbound function,
    e.g.,

    {[
    Emu.on_syscall emu (fun emu number args ->
        match (number, args) with
        | 64L, [ _; buf; len; _; _; _ ] ->
            print_string (Emu.read emu buf (Int64.to_int_exn len));
            Return len
        | 172L, _ -> Return 1000L (* getpid *)
        (* exit, exit_group, set_tid_address, futex, sched_yield, gettid,
           clone, and clone3 of AArch64, which the executor runs *)
        | (93L | 94L | 96L | 98L | 124L | 178L | 220L | 435L), _ -> Default
        | _ -> Return (-38L)
        (* ENOSYS *))
    ]}

    The hooks run, in the order of their adding, until one returns a value, so
    that a catch-all serves all calls, also of the code, that the program
    writes. The instructions, that Primus interprets, e.g., which read the
    tainted registers, call the Lisp function of the intrinsic without the
    hooks. The targets without an ABI of Linux, e.g., Windows, call no hook. *)

val arg : t -> int -> int64
(** [arg emu n] the [n]th argument of the function, which is called, from 0, as
    its prototype tells, e.g., from the api files. *)

val exit_code : t -> int option
(** the code, with which the program exited *)

val thread : t -> int
(** [thread emu] the TID of the thread, that the paused program runs, which is
    1, unless the program created threads with the system calls of Linux, e.g.,
    clone, on x86-64 and AArch64, which run one at a time, and are preempted.
    Raises [Invalid_argument], if the program is not paused. *)

val spawn_thread : ?stack:int64 -> t -> start:int64 -> arg:int64 -> int
(** [spawn_thread emu ~start ~arg] creates a thread of the paused program, which
    calls the function at [start], with the lower bit set for Thumb, with [arg]
    as its first argument, as the C ABI passes it, and exits with the result of
    the function, when it returns, and returns its TID. The thread runs, when
    the threads switch, after the program continues, as the threads, that the
    program creates, see {!thread}, on the [stack], whose top is the address, by
    default on its own, of 256 KB, which malloc allocates. It has the registers
    of the thread, that runs, e.g., its TLS, but the stack pointer, the
    argument, and the return address, also on Windows, where it is created as
    with CreateThread, whose stack is its own.

    Raises [Invalid_argument], if the program is not paused, and [Failure], if
    the threads of the target are not supported, e.g., of PowerPC64, or there
    are too many. *)

val call :
  ?stack:int ->
  ?args:int64 list ->
  ?regs:(string * int64) list ->
  ?thread:int ->
  ?service:(t -> int64 -> unit) ->
  t ->
  int64 ->
  int64 option
(** [call emu addr ~args] calls the function at [addr], with the lower bit set
    for Thumb, of the paused program, with the [args], which the C ABI of the
    target passes as the arguments of the type [long], in the registers, or on
    the stack, and the [regs], the registers by their names, with their values,
    which the ABI doesn't pass, e.g., [[ ("X8", ctx) ]] of a dispatcher, which
    are set after the arguments, on a new stack of [stack] bytes, by default 64
    KB, which malloc allocates, and which is zeroed, with the return address, at
    which the function returns to the script, e.g.,

    {[
      match Emu.call emu decrypt ~args:[ buf; 16L ] with
      | Some n -> printf "decrypted %Ld bytes: %S\n" n (Emu.read emu buf 16)
      | None -> ...
    ]}

    The function runs as the program does, e.g., the hooks see it, in the
    thread, that the program paused in, or in the context of the [thread], by
    its TID, see {!threads}, i.e., with its registers, e.g., its TLS, which the
    function reads, and returns its result, as the ABI returns a [long], after
    which the registers are as they were before the call, also of the thread,
    the memory as the function left it, e.g., its output buffers, which a
    {!snapshot} undoes, or {!diff} tells, and the program pauses where it was,
    so that a script runs a routine, e.g., a codec, or a dispatcher, with the
    inputs of its choice, as many times as it likes.

    Returns [None], if the program paused in the function, e.g., as a hook
    stopped it, or as it waits on a futex, which the other threads, that don't
    run in the call, would wake, see {!drive}, or ended, see {!status}; {!run}
    continues the function, after which the program pauses where it was, with
    the result in {!returned}. With [service], the function, that pauses, is
    served instead: [service emu pc] runs at each pause, e.g., the handlers of
    the script, that serve the system calls, or the imports, that the hooks
    stopped at, and the function continues, until it returns, or the program
    ends, so that a routine runs end to end in one expression, e.g.,

    {[
    Emu.call emu routine ~args:[ ctx ] ~service:(fun emu pc -> handle emu pc)
    ]}

    Raises [Invalid_argument], if the program is not paused, and [Failure], if
    the function can't be called, e.g., the C ABI of the target is not known,
    the target has no such register, or the program no such thread, or the
    function failed, e.g., with a segmentation fault, after which the program is
    paused where it was, as before the call. *)

(** the outcome of {!drive} *)
type called =
  | Returned of int64  (** the function returned the value *)
  | Parked of { pc : int64; thread : int }
      (** the function still runs, paused at [pc], in the [thread], e.g., as a
          hook stopped it, and [service] was not given, or the [budget] of the
          pauses, or the [timeout] ran out, e.g., as it waits, that another
          thread wakes it, which doesn't run in the call: a wait of a futex, or
          of an object of Windows, pauses then, after which the function
          continues, as if it was woken spuriously, and a spin runs out of the
          time; {!run} continues it, as after {!call} *)
  | Ended of status  (** the program ended in the function, e.g., it exited *)

val drive :
  ?budget:int ->
  ?timeout:float ->
  ?stack:int ->
  ?args:int64 list ->
  ?regs:(string * int64) list ->
  ?thread:int ->
  ?service:(t -> int64 -> unit) ->
  t ->
  int64 ->
  called
(** [drive emu addr] calls the function at [addr], as {!call} does, and serves
    at most [budget] of its pauses, by default all, with [service], for at most
    [timeout] seconds, by default without the limit, with the pauses, after
    which the function pauses, e.g., as it spins, and tells, how the call came
    out, also, where the function parked, if it still runs, e.g.,

    {[
    match Emu.drive emu routine ~args:[ ctx ] ~budget:100 ~service with
    | Returned x -> printf "returned %Ld\n" x
    | Parked { pc; thread } ->
        printf "parked at %Lx in the thread %d\n" pc thread;
        List.iter (Emu.thread_regs emu thread) ~f:(fun (r, x) ->
            printf "%s = %Lx\n" r x)
    | Ended _ -> print_endline "the program ended"
    ]}

    Raises as {!call}, and [Invalid_argument], if [budget], or [timeout], is
    negative. *)

val returned : t -> int64 option
(** the result of the last {!call}, that returned *)

type region = {
  lower : int64;
  upper : int64;  (** inclusive *)
  readable : bool;
  writable : bool;
  executable : bool;
}
(** a range of the mapped memory, with its protection *)

val regions : t -> region list
(** [regions emu] the memory map of the paused program: the ranges of its
    memory, the lowest first, which the program and the loader mapped, and which
    have the same protection, e.g., after the program unpacked itself, or
    changed the protection of its pages. Raises [Invalid_argument], if the
    program is not paused. *)

(** where a byte of the memory comes from, see {!provenance} *)
type provenance =
  | Stored
      (** a store of the program, of a stub, or of the script, i.e., the byte is
          of this run *)
  | Generated
      (** a load generated it, as the program never stored it, and the region
          has no bytes, e.g., the uninitialized memory, that the program reads,
          or it will be generated, when it is loaded *)
  | Mapped  (** the file of the program, or the fill of a region, e.g., BSS *)
  | Unmapped

val provenance : t -> int64 -> provenance
(** [provenance emu addr] where the byte at [addr] comes from, e.g., to tell, if
    a value, that looks like a pointer, is the data of the program, or the
    garbage of the uninitialized memory. The generated bytes are deterministic
    in a run, as the generator is seeded, but not between the runs, which load
    them in another order, so two runs from the same checkpoint differ in them,
    and the checkpoints keep them as stored, as they were loaded. Raises
    [Invalid_argument], if the program is not paused. *)

val project :
  ?symbols:(string * int64) list ->
  ?roots:int64 list ->
  ?cache:string ->
  t ->
  project
(** [project emu] the project of the memory of the paused program, as it is now,
    e.g., after the program unpacked, or wrote its code: its executable regions,
    see {!regions}, are disassembled and lifted from the bytes, that the program
    has there now, as the disassemble command does, from the subroutines of the
    symbols of the program, of {!add_symbol}, and of [symbols], e.g., the
    entries, that the script found in the tables, that the program built, which
    name the subroutines too, and of the [roots], the addresses of the code,
    that the disassembler starts from too, which it names by their addresses,
    e.g., the targets of the calls of a trace, see [Trace.calls], so that the
    functions, that the trace found, are of the project, and its other regions
    are its data, so that the analyses of the whole program, e.g., {!Xrefs}, or
    the passes, e.g., [recompile-optimize], see [Bap_script.run_pass], work on
    the code, that runs, rather than on the file, whose bytes differ, e.g.,

    {[
    ignore (Emu.run emu ~until:after_unpack);
    let proj = Emu.project emu in
    let xrefs = Emu.Xrefs.create proj in
    Emu.Xrefs.callers xrefs decrypt
    ]}

    The project has the specification of the file, with the names, and the
    memory of the program, which the analyses read, e.g., the tables of the
    pointers to the functions, in a unit of its own, as the memory changes
    between the projects, and the name of the file, with [#live] and the number
    of the project, so that the knowledge of the file isn't confused with it.
    The disassembly of a large program takes its time, e.g., a few seconds for a
    megabyte of code, so with [cache], the file of a saved project, see
    {!save_project}, the project is loaded from the file, if it is of the same
    code, see {!code_digest}, and else built, and saved there, so that the
    scripts, that run again and again, pay for the disassembly once, e.g.,

    {[
      let proj = Emu.project emu ~cache:"unpacked.proj" in
    ]}

    Raises [Invalid_argument], if the program is not paused, and [Failure], if
    the project can't be created. *)

val code_digest :
  ?symbols:(string * int64) list -> ?roots:int64 list -> t -> string
(** [code_digest emu] the digest of the code of the paused program: the bytes of
    its executable regions, its symbols and roots, with [symbols] and [roots],
    as {!project} takes them, and its target, which changes, when the program
    changes its code, so that a script tells, if a saved project, see
    {!save_project}, is of the code, that the program has now. Raises
    [Invalid_argument], if the program is not paused. *)

val project_digest : project -> string option
(** [project_digest proj] the digest of the code, that the project of
    {!project}, or of {!load_project}, was made of, see {!code_digest} *)

val save_project : project -> string -> unit
(** [save_project proj file] saves the project of {!project} to the [file]: its
    program, i.e., the subroutines, that were disassembled and lifted, its
    memory, its target, and its digest, so that the next script loads it with
    {!load_project}, instead of disassembling the memory again, e.g.,

    {[
    let proj =
      match Emu.load_project cache with
      | proj
        when Option.equal String.equal (Emu.project_digest proj)
               (Some (Emu.code_digest emu)) ->
          proj
      | _ | (exception Failure _) ->
          let proj = Emu.project emu in
          Emu.save_project proj cache;
          proj
    ]}

    which {!project} does with [cache]. The program is saved with the addresses
    of its terms only, as the instructions, that the terms carry, take most of
    the space, and the analyses of the saved projects, e.g., {!Xrefs} and
    {!Static}, don't read them, so a saved project is a few times the size of
    the memory, that it has. Raises [Sys_error], if the file can't be written.
*)

val load_project : string -> project
(** [load_project file] the project, that {!save_project} saved, with its
    program, its memory, its target, and its digest, see {!project_digest},
    without the disassembly state, so that it is as the project of the memory
    for the analyses of the program, e.g., {!Xrefs} and {!Static}. Raises
    [Failure], if the file is not a saved project, or is broken, e.g., of
    another version. *)

module Xrefs = Bap_emu_xrefs
(** the cross references of a program, e.g., of {!project}, see [Bap_emu_xrefs]
*)

module Static = Bap_emu_slice
(** the static slices of the code of a program, e.g., of {!project}, see
    [Bap_emu_slice] *)

(** the Java Native Interface model, see [Bap_emu_jni] *)
module Jni : sig
  type emulator = t

  include module type of Bap_emu_jni

  val install : t -> emulator -> layout -> unit
  val serve : t -> emulator -> unit
  val serve_vm : t -> emulator -> unit
  val read_string : emulator -> int64 -> string
end

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

    Raises [Invalid_argument], if the [snapshot] is of another emulator, or was
    dropped, see {!drop_snapshot}. *)

val drop_snapshot : t -> snapshot -> unit
(** [drop_snapshot emu snapshot] frees the [snapshot], which keeps the state of
    the program, as it was: its machine, and the pages, that the engine holds
    for it, so that a script, that snapshots each experiment, doesn't keep them
    all, see {!footprint}. Raises [Invalid_argument], if the snapshot is of
    another emulator, or the program is not paused. *)

val diff : t -> snapshot -> (int64 * int) list
(** [diff emu snapshot] the bytes of the memory, that differ between the
    [snapshot] and the paused program, as the ranges, the address and the number
    of the bytes, the lowest first, e.g., the outputs of a routine, that {!call}
    ran, in the static storage, or the memory, that a run from a checkpoint
    changed. The bytes are the ones, that the program, the stubs, or the script
    stored, without the bytes, that the loads generated, see {!provenance},
    which aren't changes, and may be loaded on one side only. Raises
    [Invalid_argument], if the program is not paused, or the snapshot is of
    another emulator. *)

val changed_since : t -> string -> (int64 * int) list
(** [changed_since emu file] the bytes, that differ between the checkpoint in
    the [file], see {!save}, and the paused program, as {!diff}, where the bytes
    of the checkpoint are compared with the bytes, that the program has, also
    the ones, that the loads generated, as the checkpoint keeps them as stored.
    Raises [Failure], if the file is not a checkpoint. *)

type change = {
  addr : int64;
  size : int;
  before : provenance;  (** in the snapshot *)
  after : provenance;  (** in the paused program *)
}
(** a range of the bytes, that changed, see {!changes} *)

val changes : t -> snapshot -> change list
(** [changes emu snapshot] the ranges of {!diff}, split where the provenance of
    the bytes differs, with the provenance of their first byte in the snapshot
    and in the paused program, e.g., a range from [Generated] to [Stored] is the
    first real write of the memory, e.g., an output of a routine, while a range
    from [Stored] to [Stored] overwrote the data of the program. Raises as
    {!diff}. *)

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
    program, which the checkpoint is of, the runs of Unicorn, that Primus
    called, with the stubs, that called them, and the bytes of the instructions,
    that the lifted engine ran, see {!insn_at}. The names of the program and its
    stubs are of its file, which is loaded anew.

    The program, that continues from the checkpoint, continues the innermost
    run, after which the stub, that called it, completes, if it is known, see
    {!complete}, e.g., __libc_start_main exits with the result of main, as the
    code of the stubs is not data, and the program ends.

    In a hook, where the machine runs the program, the checkpoint is saved at
    the pause, that the hook asks for, i.e., before the instruction, that a hook
    of the code sees, after which the program continues, unless a hook also
    {!stop}ped it, see {!defer}, so an error of the save raises from the
    function, that runs the program, e.g., {!run}.

    The program, that failed, e.g., at an instruction, that faulted, is saved at
    the address, from which Unicorn would continue, i.e., of that instruction,
    so the program, that continues from the checkpoint, in another run too,
    e.g., after the script fixed the pointer or patched the code, runs it again:

    {[
    match Bap_emu.run emu with
    | Failed _ -> Bap_emu.save emu "crash.ckpt"
    | _ -> ()
    ]}

    While a function, that the script called, runs, e.g., paused in it, see
    {!call}, the checkpoint is of the program at the call, with the registers,
    the runs, and the threads, that it had then, and the memory, as the function
    changed it, e.g., with the stack, that the call allocated, as the call is of
    the script, and not of the program, which continues from the address, at
    which it paused for the call.

    Raises [Invalid_argument], if the program exited, or its emulator failed,
    e.g., with an exception of the script, and [Failure], if the checkpoint
    can't be saved, e.g., as the program failed outside of a run of Unicorn. *)

val save_lifts : t -> unit
(** [save_lifts emu] saves the instructions, that the lifted engine lifted, to
    its cache, if bap has one, see [--cache-dir], and they changed, as the run
    does, when it exits, also when a signal terminates it, e.g., the timeout of
    a script, see [SIGTERM], and as {!save} does, so that the next run starts
    with them. *)

val forget_lifts : t -> unit
(** [forget_lifts emu] drops the instructions, that the lifted engine lifted,
    whose semantics it keeps for its engines, e.g., of the snapshots, and for
    its cache, to which {!save_lifts} saves them first, and the ones, that
    {!bir} lifted in the hooks, so that a long run of a program with much code
    gives their memory back, e.g., when {!footprint} crosses a line. The code,
    that the engine compiled, stays, so the program runs on, and the
    instructions, that are lifted again, e.g., in a new engine, cost a lift
    each, as at the start. *)

type footprint = {
  heap : int;  (** the bytes of the heap of OCaml *)
  top_heap : int;  (** the most, that the heap had *)
  rss : int option;
      (** the resident size of the process, in bytes, which Linux tells, see
          [/proc/self/status] *)
}

val footprint : unit -> footprint
(** [footprint ()] the memory, that bap takes, so that a long run tells, when to
    forget its lifts, see {!forget_lifts}, to drop its snapshots, see
    {!drop_snapshot}, or to save a checkpoint, see {!save}, and start anew, see
    [docs/emulation.md]. *)

(** The checkpoints, that {!save} wrote, which a script inspects, without
    loading their program, e.g., to choose one in a pipeline. *)
module Checkpoint : sig
  type thread = {
    tid : int;
    pc : int64;
        (** the address, from which it continues, with the lower bit set in the
            Thumb state of ARM *)
    waiting : int64 list option;
        (** the addresses, e.g., of the futexes, on which it waits, if it waits
            in a wait, that the executor runs, and in which it parked: a wait of
            a futex of Linux, or of an object, or of a lock, of Windows. A
            thread, that waits otherwise, runs, e.g., in a loop of the program,
            that polls a flag, in a [sched_yield], or in a stub of Primus Lisp,
            which models the wait without a futex, so it isn't waiting, but
            spinning, as {!Trace.hot} tells, nor is the thread, that runs, also
            when it paused in a wait, see {!Parked}. *)
  }

  type info = {
    target : string;  (** the target of the program, e.g., [bap:amd64] *)
    digest : string;  (** the hex MD5 digest of the file of the program *)
    pc : int64;  (** from which the thread, that ran, continues *)
    thread : int;  (** the TID of the thread, that ran *)
    threads : thread list;
        (** all threads, the one that ran first, the others by their TIDs *)
    frames : (string option * string option) list;
        (** the runs of the program, that Primus called, the innermost first,
            with the function, that runs, and the stub, that called it *)
    symbols : (string * int64) list;  (** of {!add_symbol} *)
    components : string list;
        (** the components, whose states are saved, see [Primus.Checkpoint] *)
  }

  val info : string -> info
  (** [info file] reads the checkpoint, raises [Failure], if it is not one, or
      of another version, or broken. *)

  val is_of : info -> project -> bool
  (** [is_of info proj] if the checkpoint is of the file of the program *)

  val insns : string -> int64 list
  (** [insns file] the addresses of the instructions, that the lifted engine
      ran, before the checkpoint was saved, in their order, with the lower bit
      set in the Thumb state of ARM, or none, if the program ran in Unicorn.
      Raises [Failure], if the file is not a checkpoint. *)

  val insns_diff : string -> string -> int64 list
  (** [insns_diff before after] the addresses of the instructions, that the
      checkpoint [after] has, and the checkpoint [before] doesn't, in their
      order, e.g., of the code, that an experiment ran for the first time,
      between the checkpoint of its baseline and the one after it, see
      {!insns_since}. *)
end

val thread_regs : t -> int -> (string * int64) list
(** [thread_regs emu tid] the registers, without the aliases, of the thread of
    the paused program, by its TID, see {!threads}, e.g., of the one, that waits
    on a lock, to tell, which lock it waits on, from its arguments: of the
    engine, for the thread, that runs, and else, as the thread had them, when it
    stopped running. Raises [Invalid_argument], if the program is not paused, or
    has no such thread. *)

val threads : t -> Checkpoint.thread list
(** [threads emu] the threads of the paused program, the one, that runs, at the
    address, at which it paused, first, and the others, with the addresses, from
    which they continue, and the addresses, on which they wait, e.g., their
    futexes, by their TIDs, e.g., to tell, why a program, that stops
    progressing, spins, with {!Trace.hot} and {!Trace.addresses}. The threads,
    that wait without a futex, e.g., on a flag, that they poll, aren't waiting,
    see {!Checkpoint.thread.waiting}. Raises [Invalid_argument], if the program
    is not paused. *)

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

type import = {
  slot : int64;  (** the address of the slot, e.g., of GOT *)
  name : string;
      (** the name of the function, which the loader resolved from the
          relocation of the slot, e.g., from [.rela.plt] and [.dynsym] *)
  value : int64 option;
      (** the address, that the slot holds now, or [None], if it is not
          readable, which {!function_at} names *)
}

val imports : t -> import list
(** [imports emu] the slots of the external functions of the program, in the
    order of their addresses, as the loader resolved them, and as the program
    left them, e.g., after its own resolver wrote them, so that a script
    compares them, between the runs, or with its own view of the relocations,
    e.g., of a program, whose protector rewrote the tables of the dynamic
    symbols. Raises [Invalid_argument], if the program is not paused. *)

val function_at : t -> int64 -> string option
(** [function_at emu addr] the name of the function at [addr], e.g., of the stub
    of an external function, to which the slots of {!imports} refer, or of the
    program, or of {!add_symbol} *)

val unstub : t -> string -> unit
(** [unstub emu name] runs the code of the function of the program in Unicorn
    again, instead of the stub, that replaced it, e.g., the Lisp stub of
    [malloc] of a static program, e.g., after the script patched the code, see
    {!write}, also when Primus calls the function, e.g., from another stub. The
    checkpoints keep it, see {!save}.

    Raises [Invalid_argument], if the program has no code of the function, e.g.,
    if it is external, or if it is not paused, as it runs, e.g., in a hook. *)

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
