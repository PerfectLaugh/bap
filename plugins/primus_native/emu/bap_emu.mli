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

(** encodings for synthetic AArch64 stubs *)
module AArch64 : sig
  val b : pc:int64 -> int64 -> int32
  (** [b ~pc target] is the word of an unconditional branch from the instruction
      at [pc] to [target]. Raises [Invalid_argument] if [pc] or the displacement
      is not four-byte aligned, or if the displacement is outside the signed
      28-bit byte range from -128MiB inclusive to 128MiB exclusive. *)

  val ret : int32
  (** the word of [ret], which returns to the address in [X30]. *)

  val bytes : int32 -> string
  (** [bytes word] is the four-byte little-endian encoding of [word]. *)
end

type t
(** the emulator *)

type checkpoint_models
(** the per-emulator registry of serializable script-model state *)

(** the state of the program *)
type status =
  | Paused  (** the program pauses, e.g., at the address of [until] *)
  | Running
      (** the program runs, e.g., in a hook, which may {!stop} it, or {!defer}
          an action to the pause *)
  | Exited of int option  (** the program exited, with the code, if known *)
  | Failed of string  (** the program or the emulator failed *)

type memory_operation = Read | Write | Fetch

type failure = {
  thread : int;
  pc : int64;
  addr : int64;
  operation : memory_operation;
}
(** the last unrecoverable memory fault, with its thread, instruction, address,
    and operation *)

val failure : t -> failure option
(** [failure emu] is the last unrecoverable memory fault, or [None] if the
    program has not had one. Recoverable page faults are not included. *)

type event = { kind : string; detail : string }

val record_event : t -> string -> string -> unit
(** [record_event emu kind detail] appends a model event, e.g., an allocator
    position, to the bounded journal kept in checkpoints. *)

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
  ?models:checkpoint_models ->
  ?engine:[ `Unicorn | `Lifted ] ->
  ?lifting:[ `Default | `Direct ] ->
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
    {!save}, instead of the [entry], and pauses before its address. [models]
    supplies the emulator's checkpoint models, registered before this call so
    required state and schemas can be preflighted.

    The native code runs in the [engine]: [`Unicorn], or [`Lifted], the lifted
    engine, see [Bap_lifted], which runs the semantics of the instructions, that
    BAP lifts. By default, it is the engine of the [system], e.g., [`Unicorn] of
    [bap:unicorn-executor], or, without the [system], [`Unicorn], if the
    environment variable [BAP_EMU_ENGINE] is [unicorn], e.g., in the testsuite,
    or else [`Lifted]. The options of the plugin of the engine, e.g.,
    [--primus-lifted-timeout], apply to the program.

    With [~lifting:`Direct], cold cache misses use the disassembler and target
    lifter without publishing fresh program labels and Ogre semantics. Missing
    direct semantics fall back to the default KB path; x86 selects that path
    directly. Direct and default policies have separate persistent caches. *)

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

val bir :
  ?executed_bytes:bool ->
  ?thumb:bool ->
  t ->
  int64 ->
  (int * blk term list) option
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
    page is not in Unicorn yet.

    If [executed_bytes], failed decoding falls back to {!insn_at} history, while
    current bytes remain primary. The default preserves the current-byte-only
    behavior. *)

val eval_sub : t -> sub term -> unit
(** [eval_sub emu sub] evaluates the blocks of [sub] with the real Primus
    interpreter, starting with the emulator's current registers and memory. It
    follows direct control transfers to blocks inside [sub] and suppresses
    control transfers to destinations outside it. The program must be paused;
    the resulting registers and memory remain available for comparison.

    This is an execution oracle, not by itself a proof of semantic equivalence:
    callers should compare calls, side effects, and final state. *)

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

type decode_failure = {
  index : int64;  (** the global index of the instruction's trace record *)
  pc : int64;  (** the instruction, that couldn't be decoded *)
  block : int64 option;
      (** the source block in a trace of blocks, or [None] in a trace of
          instructions *)
  thread : int;  (** the effective TID of the record *)
}
(** an instruction, that a slice or the expansion of a block couldn't decode *)

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
    ?read_values:bool ->
    ?watch:int64 * int64 ->
    ?watches:(int64 * int64) list ->
    ?watch_accesses:int ->
    ?first:int64 ->
    ?last:int64 ->
    ?journal:string ->
    ?journal_interval:int ->
    ?code_versions:int ->
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

      With [watches], each range has an independent native access ring while the
      parent trace retains its unfiltered instruction and memory history. Use
      {!watches} and {!watched} to access the per-range traces. The parent and
      every range are saved and restored by {!save_state} and {!restore_state}.
      [watch_accesses] bounds each watched ring independently of the parent's
      [accesses] ring, defaulting to 2{^ 16}. [watch] and [watches] are mutually
      exclusive; duplicate or reversed ranges are rejected.

      If [read_values], successful reads of one to eight bytes also record their
      loaded bytes, zero-extended with the byte at the lowest address in the
      lowest byte. Reads wider than eight bytes, failed or partial reads, and
      all writes have no loaded value. It is false by default, preserving the
      existing read hooks and access records.

      [code_versions] retains exact executed bytes in a ring of that many
      entries, keyed by absolute trace-record index. Instruction traces use an
      opt-in per-instruction OCaml callback; block traces capture block bytes
      and mode in the bounded block callback. Capture is disabled when the
      option is zero or absent, unless [journal] is present, which enables it
      with the native record-ring capacity by default.

      [journal = prefix] synchronously writes bounded, versioned trace-state
      snapshots to deterministic [prefix.NNNNNNNN.trace] segment names and
      appends their sequence and continuity metadata to [prefix.manifest].
      Rotation happens at native block boundaries, or instruction boundaries for
      instruction traces, every [journal_interval] records when possible. The
      default interval is bounded by the configured ring capacities. Each write
      checks instruction, access, capture, boundary, range, and code-version
      counter deltas against their ring capacities. Overflow or I/O failure is
      explicit and sticky; history is never silently discarded. The runtime
      retains only the current manifest cursor, not a list of segments.

      Raises [Invalid_argument], if [accesses] is positive, or a range is
      watched, and the instructions are sampled, or the ones of a range are
      recorded; for a negative code-version capacity or nonpositive journal
      interval; and when a journal disables code versions. Journal creation and
      manifest errors raise [Failure]. *)

  val stop : t -> unit
  (** [stop trace] stops recording, the trace keeps the records. It is safe to
      call [stop] on an already stopped or detached trace. A journal is flushed
      and closed, and any deferred overflow or I/O error raises [Failure], also
      on subsequent calls. *)

  val resume : t -> unit
  (** [resume trace] resumes recording with the configuration passed to
      {!start}, or restored by {!restore_state}, without resetting the retained
      records, absolute indices, or sampling cursors. It does nothing if the
      trace is already recording. A stopped journal continues its manifest with
      fresh, monotonically increasing segment sequence numbers. *)

  val save_state : t -> string -> unit
  (** [save_state trace file] atomically writes a versioned binary snapshot of
      the complete native trace, including retained records, absolute indices,
      ring and sampling cursors, accesses, slice boundaries, and embedded native
      captures, retained executed-code versions, and every independent watched
      range and its ring, together with the target, program identity, and hook
      configuration. The trace may be recording or stopped. State format 4 does
      not accept earlier formats. Raises [Failure] with the operation and file
      or program error on failure. *)

  val restore_state : emu -> string -> t
  (** [restore_state emu file] loads a snapshot written by {!save_state}, checks
      its format, version, target, program identity, metadata, and native
      shapes, and returns a detached trace with no live hooks. The saved trace
      is associated with [emu] for decoding and slicing; call {!resume} to
      continue recording on that emulator. Raises [Failure] with a clear error
      if the snapshot cannot be read, decoded, validated, or matched to [emu].
  *)

  type code_version = {
    index : int64;  (** absolute instruction or block trace-record index *)
    pc : int64;
    bytes : string;  (** exact bytes captured before this record executed *)
    thumb : bool;
    block : bool;  (** whether [bytes] cover a whole block record *)
  }

  val code_version : t -> int64 -> code_version option
  (** [code_version trace index] returns the retained version at exactly
      [index], or [None] if capture was disabled or that version was evicted. *)

  val versions : ?last:int -> t -> code_version list
  (** retained code versions, oldest absolute index first *)

  val retained_versions : t -> int
  (** the number of retained code versions, bounded by [code_versions] *)

  type journal_segment = {
    sequence : int;
    file : string;
    first : int64;
    next : int64;
  }

  val journal_segments : string -> journal_segment list
  (** [journal_segments prefix] validates and enumerates the on-disk manifest in
      sequence order. [first] and [next] delimit each segment's absolute record
      coverage; [file] is suitable for {!restore_state}. *)

  val load_journal : emu -> string -> t list
  (** [load_journal emu prefix] restores every manifest segment, in sequence
      order, as a detached trace. *)

  val count : t -> int64
  (** the number of the recorded instructions, or blocks, also of those, that
      the ring doesn't keep anymore *)

  val retained : t -> int
  (** the number of instruction or block records that the ring currently keeps
  *)

  val clear : t -> unit
  val blocks : t -> bool

  val pcs :
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the last program counters, at most [last], by default all, that the ring
      keeps, the oldest first *)

  val tids :
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the effective TIDs of the last records, aligned with {!pcs} *)

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
    read_value : int64 option;
        (** the successfully loaded bytes, zero-extended with the first one in
            the lowest byte, if {!start} enabled [read_values] and the read was
            one to eight bytes; otherwise [None] *)
    thread : int;  (** the effective TID, which made the access *)
  }

  val accesses : ?last:int -> t -> access list
  (** the last accesses to the memory, the oldest first *)

  val watches : t -> ((int64 * int64) * t) list
  (** the independent watched ranges and their traces, in configuration order *)

  val watched : t -> int64 * int64 -> t option
  (** [watched trace range] returns the trace of exactly [range], if configured
  *)

  val retained_accesses : t -> int
  (** the number of access records currently retained in this ring *)

  val accesses_count : t -> int64
  (** the absolute number of accesses recorded in this ring, including evictions
  *)

  val access_capacity : t -> int
  (** the native access-ring capacity, zero when accesses are not recorded *)

  val access_overflow : t -> bool
  (** whether older accesses were evicted from this ring *)

  type access_summary = {
    count : int64;
    retained : int;
    capacity : int;
    overflow : bool;
  }

  type summary = {
    count : int64;
    retained : int;
    capacity : int;
    nonzero_pcs : int;
    nonzero_block_sizes : int;
    overflow : bool;
    accesses : access_summary;
    captures : int64;
    code_versions : int;
    watches : ((int64 * int64) * access_summary) list;
  }

  val summarize : t -> summary
  (** [summarize trace] reports absolute counts, current retention, capacities,
      nonzero metadata, evictions, captures, code versions, and every watched
      ring. It does not stop or mutate the trace. *)

  val describe : t -> string
  (** a human-readable rendering of {!summarize} *)

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
    ?executed_bytes:bool ->
    ?last:int ->
    t ->
    (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
  (** the program counters of the instructions of the last [last] records, by
      default of all, that the ring keeps, the oldest first, of the blocks too,
      whose instructions are decoded from current bytes by default, or from
      exact trace-local versions with [executed_bytes] *)

  type decode_status = Decoded | Decode_failed

  type window_instruction = {
    index : int64;  (** the global index of the instruction's trace record *)
    pc : int64;
    block : int64 option;
        (** the block, from which the instruction expands, or [None] in a trace
            of instructions *)
    thread : int;  (** the effective TID, which ran the instruction *)
    decode : decode_status;
  }

  val inspect :
    ?executed_bytes:bool ->
    ?thread:int ->
    ?last:int ->
    t ->
    window_instruction list
  (** [inspect trace] is the expanded instruction window, that {!slice} uses,
      with the global record indices, effective TIDs, and decode status of its
      instructions. In a trace of blocks, [block] is the address of the block,
      whose expansion produced the instruction, including when decoding stops at
      a failed instruction.

      Instructions are decoded from their current bytes by default. With
      [executed_bytes], an exact retained {!code_version} for the absolute
      record index takes precedence, including on Unicorn and after detached
      restore. Block expansion reads each instruction from its captured block.
      If no such version was recorded, current or reconstructed bytes remain the
      primary source; a failed lift may still use the executed-instruction
      history of the lifted engine, see {!insn_at}. That fallback keeps only the
      last instruction lifted at each address and mode, not every version that
      ran. *)

  type state_field = {
    base : string;
    offset : int64;
    size : int;
    value : int64 option;
  }

  type state = {
    site : int64;
    index : int64;
    thread : int;
    regs : (string * int64) list;
    fields : state_field list;
  }
  (** a pre-instruction state at [site], with its global instruction-trace
      [index], effective [thread], named register values, and indirect fields. A
      field [value] is [None] if any requested byte is unmapped or unreadable.
  *)

  type state_capture

  val capture_state :
    ?size:int ->
    ?regs:string list ->
    ?fields:(string * int64 * int) list ->
    emu ->
    int64 list ->
    state_capture
  (** [capture_state emu sites] captures [regs] and [fields], specified as
      [(base_register, offset, size)], before instructions at [sites], without
      per-site OCaml hooks. Fields are one to eight bytes, packed with the byte
      at the lowest address in the lowest byte, and read exactly with no partial
      result. The last [size] records are retained, by default 2{^ 16}. Unknown
      registers, non-byte-aligned or wider-than-64-bit values, and invalid field
      widths are rejected. *)

  val captured_states : ?last:int -> state_capture -> state list
  (** the retained states, oldest first, at most [last] if specified *)

  val stop_state_capture : state_capture -> unit
  (** stop recording and retain the captured states *)

  val save_states : state_capture -> string -> unit
  (** save the retained immutable states in a versioned binary format; live
      hooks and engine pointers are not serialized *)

  val load_states : string -> state list
  (** load states saved by {!save_states}, or fail clearly on another format or
      broken input *)

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

  type call = Bap_emu_xrefs.call = {
    site : int64;
    targets : (int64 * int) list;
    thread : int;
  }

  val calls : ?executed_bytes:bool -> ?thread:int -> ?last:int -> t -> call list
  (** [calls trace] the calls of the last [last] records, by default of all,
      that the ring keeps, grouped by their effective TIDs and sites. The
      targets are the next same-thread instructions, with their counts, the most
      often first. With [thread], only that TID is selected. A call, whose next
      instruction is the one after it, isn't taken. The instructions are those
      of {!insns}, so a trace of blocks has them. Adjacent instructions of
      different TIDs never make a call. *)

  type branch = { site : int64; target : int64; taken : bool; thread : int }

  val branches :
    ?executed_bytes:bool -> ?thread:int -> ?last:int -> t -> branch list
  (** [branches trace] the conditional branches of the last [last] records, by
      default of all, in their order, optionally only of [thread]. The target is
      the next same-thread instruction, and [taken] tells whether it isn't the
      fallthrough. Adjacent instructions of different TIDs never make a branch.
      The instructions are those of {!insns}, so a trace of blocks has them. *)
end

(** Reusable control-flow-flattening recovery and validation. *)
module Cff : sig
  type dispatch = {
    site : int64;
    state : int64;
    thread : int;
    regs : (string * int64) list;
    fields : Trace.state_field list;
  }

  val dispatchers : state:string -> Trace.state_capture -> dispatch list
  (** [dispatchers ~state capture] decodes each captured dispatcher state from
      the named register, preserving its site, TID, registers, and fields. *)

  type recovery = { sub : sub term; complete : bool; unresolved : int64 list }

  val recover : ?max_blocks:int -> t -> int64 list -> recovery
  (** [recover emu roots] reconstructs a synthetic subroutine from [roots],
      using executed bytes when current lifting fails. It adds conditional
      fallthroughs, retains external exits, and reports roots it could not lift.
      No unresolved indirect target is turned into an invented direct edge. *)

  type effects = {
    calls : string list;
    interrupts : string list;
    stores : string list;
    protection_changes : string list;
  }

  val effects : sub term -> effects
  (** inventory calls, interrupts, memory stores, and protection-related calls
  *)

  val validate_boundaries : sub term -> sub term -> bool
  (** whether two synthetic subroutines have exactly the same external exits *)

  type check_result = {
    ok : bool;
    effects : bool;
    boundaries : bool;
    registers : bool;
    memory : bool;
    continuation : bool;
  }

  val check :
    t ->
    regs:string list ->
    ?continuation:(int64 * int) list ->
    original:sub term ->
    simplified:sub term ->
    unit ->
    check_result
  (** [check emu ~regs ~original ~simplified] evaluates both subroutines from
      the same snapshot with {!eval_sub}. It compares their side-effect
      inventories, external boundaries, selected registers, final writes, and
      optional continuation-consumed byte ranges. The original snapshot is
      restored afterwards. External control transfers are suppressed by
      [eval_sub], so a dynamic continuation register should be included in
      [regs]. *)
end

(** Opt-in structured comparison of trace-derived execution events. *)
module Compare : sig
  include module type of Bap_emu_compare

  val instructions : ?thread:int -> Trace.t -> event list
  (** [instructions trace] converts the retained instructions, including the
      expansion of block records, preserving each instruction's effective TID.
      With [thread], selects only that TID. *)

  val blocks : ?thread:int -> Trace.t -> event list
  (** [blocks trace] converts the retained block records without expanding them.
  *)

  val branches : ?thread:int -> Trace.t -> event list
  (** [branches trace] converts the ordered conditional-branch decisions. *)

  val calls : ?thread:int -> Trace.t -> event list
  (** [calls trace] converts the existing call aggregates, grouped by effective
      TID and site, with target counts; these are not individual call records.
  *)

  val captures : thread:int -> Trace.capture -> event list
  (** [captures ~thread capture] converts register captures, attributing them to
      the caller-selected TID. *)

  val writes : ?thread:int -> Trace.t -> event list
  (** [writes trace] converts the retained memory writes with their PCs,
      addresses, sizes, values, and effective TIDs. *)
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
    List.iter (Emu.Trace.branches r.trace) ~f:(fun b ->
        printf "%Lx -> %Lx %s\n" b.site b.target
          (if b.taken then "taken" else "fell"))
    ]}

    The other exceptions of [f], e.g., [Invalid_argument], are raised. *)

type location = Bap_emu_slice.location =
  | Reg of string
  | Mem of int64 * int
      (** a register, by the name of the variable of BIR, e.g., [RAX], the case
          of which doesn't matter, or the bytes from an address *)

type step = {
  index : int64;
      (** the global position of the instruction's record in the trace, from the
          first recorded one *)
  pc : int64;
  thread : int;  (** the effective TID, which ran the instruction *)
}

type empty_slice_reason =
  | No_dataflow
      (** no location is live, no gap was crossed, and nothing failed *)
  | Unresolved_inputs  (** initial inputs remain live at the window boundary *)
  | Outside_trace_writes  (** a live location crossed an outside-write gap *)
  | Instruction_decode
      (** an instruction or block expansion couldn't be decoded *)

type control_dependency = {
  branch_index : int64;  (** the global index of the branch's trace record *)
  site : int64;  (** the conditional branch or call site *)
  target : int64;  (** the actual next same-TID instruction *)
  taken : bool;  (** whether control didn't fall through *)
  thread : int;  (** the effective TID, which took the branch *)
}

type control_unresolved_reason =
  | Unknown_outcome
      (** sampling, a code range, or no next same-TID instruction *)
  | Unknown_scope  (** no reliable historical post-dominator scope *)
  | Window_scope  (** the window begins inside a potentially guarded scope *)
  | Missing_producer  (** a condition input has no producer in the window *)
  | Access_history
      (** the access ring or a missing access trace limits the walk *)
  | Outside_writes  (** an outside write crossed a control demand *)
  | Control_decode
      (** an instruction needed for control analysis didn't decode *)

type control_unresolved = {
  control_index : int64;
  control_pc : int64;
  control_thread : int;
  reason : control_unresolved_reason;
}

type control_slice = {
  steps : step list;  (** control-only data producers, the oldest first *)
  dependencies : control_dependency list;
      (** selected guards, the oldest first *)
  live : location list;  (** condition inputs from before the window *)
  gaps : int64 list;
      (** outside writes crossed by control demands, latest first *)
  unresolved : control_unresolved list;  (** explicit limits, in window order *)
  complete : bool;
      (** no live inputs, gaps, untracked accesses, or unresolved limits *)
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
  reason : empty_slice_reason option;
      (** why [steps] is empty, or [None] when it isn't. Decode failure takes
          precedence over outside writes, which take precedence over unresolved
          inputs; the existing [live], [gaps], and [complete] retain all their
          independent information *)
  decode_failures : decode_failure list;
      (** the instructions, that couldn't be decoded, in window order *)
  control : control_slice option;
      (** the separate control closure, only with [~control:true] *)
}

val slice :
  ?addresses:bool ->
  ?executed_bytes:bool ->
  ?window:int ->
  ?thread:int ->
  ?control:bool ->
  Trace.t ->
  location list ->
  slice
(** [slice trace locations] the dynamic backward slice of the values of the
    [locations], as the paused program has them, over the last [window]
    instructions of the trace, by default all, that it keeps: the instructions,
    whose values flow to them, through the registers, and, if the trace has the
    accesses, through the memory, at the addresses, that they had, and through
    the addresses of the loads and the stores, if [addresses]. With [thread],
    only that TID's instructions and register flow are followed, and the step
    indices remain global. Stores to shared memory by other TIDs make
    conservative gaps rather than thread-local dataflow.

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
    their steps have the indices of their blocks. {!Trace.inspect} exposes the
    expanded window and its decode status without computing a slice.

    Current or reconstructed bytes remain the default. With [executed_bytes], an
    exact retained {!Trace.code_version} for the absolute record index takes
    precedence for instruction and block traces, including after detached
    restore. Without one, a failed lift falls back to the executed-instruction
    history of the lifted engine, see {!insn_at}. That history is unavailable
    with Unicorn and is the last lifted instruction at each address and mode,
    rather than a version for every execution.

    With [control], [control] is present and contains a separate backward
    closure over the guards of the selected data steps. Its [dependencies] are
    the exact dynamic branch occurrences, with actual outcomes from the next
    instruction of the same effective TID. Its [steps] are control-only data
    producers of the guard conditions, and of taken indirect targets; newly
    selected producers add their own guards until the fixed point. Branches that
    aren't needed aren't expanded, and conditions of conditional definitions
    stay in the data slice. The [live], [gaps], [unresolved], and [complete] of
    this result are independent of the data result.

    Guard scopes use static post-dominators of each relevant subroutine, not a
    presumed fallthrough join. Caller guards remain active in nested callees and
    callee guards are discarded at actual returns. This is a finite-path,
    observed-context approximation: it explains this retained execution, not all
    paths or unobserved calling contexts. Sampled and code-ranged traces,
    missing next same-TID outcomes, mid-scope windows, evicted accesses or
    producers, outside writes, decode failures, and unavailable or historically
    mismatched CFG scopes are explicit in [unresolved] and make control
    incomplete. In particular, current bytes are never presented as a historical
    CFG for changed code. *)

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

val on_code :
  ?first:int64 ->
  ?last:int64 ->
  ?deferred:bool ->
  t ->
  (t -> int64 -> unit) ->
  unit
(** [on_code emu f] calls [f emu addr] before each instruction from [first] to
    [last], inclusive, by default of all. The instruction, that the hook saw,
    when the program paused before it, e.g., as the hook stopped it, is not seen
    again, when the program continues from it, so the hook may stop the program
    unconditionally. With [deferred], the callback runs at the safe pause as by
    {!defer}, with [addr] captured at the event, and the program continues
    afterwards unless the callback stopped it. *)

val on_sites : ?deferred:bool -> t -> int64 list -> (t -> int64 -> unit) -> unit
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
    ]}

    With [deferred], the callback runs at the safe pause as {!on_code} does. *)

val on_read :
  ?first:int64 ->
  ?last:int64 ->
  ?deferred:bool ->
  t ->
  (t -> int64 -> int -> unit) ->
  unit
(** [on_read emu f] calls [f emu addr size] before each load. With [deferred],
    the callback runs after the load at the safe pause as by {!defer}, with the
    event arguments captured immediately. *)

type write_subscription = {
  first : int64 option;
  last : int64 option;
  primus : bool;
  deferred : bool;
  callback : t -> int64 -> int -> int64 -> unit;
}

val on_writes : t -> write_subscription list -> unit
(** [on_writes emu subscriptions] subscribes several callbacks with one native
    memory hook per distinct range. Each callback has independent exact-once
    replay state and, when [primus] is true, also sees Primus/native stores.
    With [deferred], its callback runs at the safe pause as by {!defer};
    replayed stores are not queued again. *)

type write_profile = { dispatches : int; callbacks : int; seconds : float }

val write_profile : t -> write_profile
(** [write_profile emu] is the number of native write dispatches, total callback
    invocations, and seconds spent in write callbacks for this emulator. *)

val on_write :
  ?first:int64 ->
  ?last:int64 ->
  ?primus:bool ->
  ?deferred:bool ->
  t ->
  (t -> int64 -> int -> int64 -> unit) ->
  unit
(** [on_write emu f] calls [f emu addr size value] before each store, that the
    engine runs, from [first] to [last], inclusive, by default of all. With
    [deferred], the callback runs after the store at the safe pause as by
    {!defer}, with the event arguments captured immediately.

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

    A store is reported once, even when an access fault makes the engine retry
    its instruction, and the engine's stores mirrored to Primus observers are
    not reported again as stores of Primus. The writes of the script, e.g.,
    {!write}, aren't seen. A hook, that sees a store of Primus, runs in Primus,
    where the engine doesn't run, so {!pc} is of the instruction, that the
    engine ran last, e.g., the call of the stub, and {!stop} pauses the program
    before the next instruction, that runs in the engine. *)

val scoped : t -> (unit -> 'a) -> 'a
(** [scoped emu f] runs [f], and removes the hooks, that it added, when it
    returns, or raises: of {!on_code}, {!on_sites}, {!on_read}, {!on_write},
    {!on_writes}, {!on_call}, {!on_import}, {!on_syscall}, and {!Trace.capture},
    also the ones, that the scopes, that it runs, added, so that an experiment,
    e.g., of a {!call}, or of a {!drive}, doesn't leave its hooks to the
    program, that runs after it:

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

val on_import : t -> site:int64 -> name:string -> (t -> action) -> unit
(** [on_import emu ~site ~name f] calls [f emu] at the import call [site].
    [Return x] returns [x] directly from the call site and records a relocation;
    [Default] runs the callee. The prototype of [name] remains available to
    {!arg}. *)

val relocation_journal : t -> event list
(** the relocation events recorded by {!on_import}, in call order. *)

val register_stub : t -> name:string -> address:int64 -> unit
(** [register_stub emu ~name ~address] names a harness-owned synthetic stub and
    warns if execution enters it before [name] is registered with {!on_call} or
    {!on_import}. *)

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
    hooks. The targets without an ABI of Linux, e.g., Windows, call no hook.

    A handler chooses [Return] or [Default] immediately. If serving the call
    needs a paused-only operation, e.g., {!write}, allocation, or {!save}, use
    {!defer} for it before returning from the handler. *)

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

    The stack pointer is checked against the allocated stack before and after
    native and Primus-interpreted instructions. If it leaves the stack, the call
    fails with [emulated call stack exhausted], identifying the instruction and
    outer call-site PCs, SP, and bounds. The check covers nested calls and
    engine recreation; no stack grows beyond its allocation.

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
    paused where it was, as before the call. A successful call frees its
    temporary stack and forgets its bytes. A call that starts and then fails
    restores the outer registers and frames but retains the stack allocation and
    its bytes, so failed-state reads and checkpoints preserve the callee's
    stack-local values for diagnosis. Setup failures use the same cleanup as
    returns. The retained allocation lives until the emulator is discarded. *)

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

val find_bytes :
  ?provenance:provenance list ->
  t ->
  pattern:string ->
  ranges:(int64 * int64) list ->
  int64 list
(** [find_bytes emu ~pattern ~ranges] searches the readable bytes of the paused
    program in the inclusive ranges and returns the unaligned match addresses,
    lowest first, without duplicates. Adjacent and overlapping ranges are
    merged. Every byte of a match must have an accepted [provenance], by default
    [Stored] or [Mapped]. [Generated] includes only values already materialized
    by earlier loads; searching never generates or stores bytes. Unmapped and
    unreadable holes are skipped. The scan uses page-sized chunks rather than
    materializing regions or per-byte maps. Empty ranges or provenance return no
    hits. Raises [Invalid_argument] for an empty pattern or if the program is
    not paused. *)

val project :
  ?regions:(region -> bool) ->
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

    With [regions], only the executable regions, for which the predicate returns
    [true], are disassembled. The other regions stay in the memory of the
    project, which the analyses read, but roots and symbols in them are not
    disassembly starts. The selected extents are part of the cache digest, so
    the same [cache] is safe to use with different scopes.

    Raises [Invalid_argument], if the program is not paused, and [Failure], if
    the project can't be created. *)

val code_digest :
  ?regions:(region -> bool) ->
  ?symbols:(string * int64) list ->
  ?roots:int64 list ->
  t ->
  string
(** [code_digest emu] the digest of the code of the paused program: the bytes of
    its executable regions, its symbols and roots, with [symbols] and [roots],
    as {!project} takes them, its target, and the extents selected by [regions],
    which changes, when the program changes its code, so that a script tells, if
    a saved project, see {!save_project}, is of the code, that the program has
    now. Use the same [regions], [symbols], and [roots] as for {!project}.
    Raises [Invalid_argument], if the program is not paused. *)

val project_digest : project -> string option
(** [project_digest proj] the digest of the code, that the project of
    {!project}, or of {!load_project}, was made of, see {!code_digest} *)

val save_project : project -> string -> unit
(** [save_project proj file] saves the project of {!project} to the [file]: its
    program, i.e., the subroutines, that were disassembled and lifted, its
    disassembly state and specification, memory, target, and digest, so that the
    next script loads it with {!load_project}, instead of disassembling the
    memory again, e.g.,

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
    program, disassembly state and symbols, specification, memory, target, and
    digest, see {!project_digest}, so that it is as the project of the memory
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

  include
    module type of Bap_emu_jni
      with type t = Bap_emu_jni.t
       and type object_id = Bap_emu_jni.object_id
       and type call = Bap_emu_jni.call
       and type answer = Bap_emu_jni.answer
       and type handler = Bap_emu_jni.handler
       and type method_decl = Bap_emu_jni.method_decl
       and type field_decl = Bap_emu_jni.field_decl
       and type class_decl = Bap_emu_jni.class_decl
       and type object_decl = Bap_emu_jni.object_decl
       and type call_record = Bap_emu_jni.call_record
       and type identity = Bap_emu_jni.identity
       and type kind = Bap_emu_jni.kind
       and type event = Bap_emu_jni.event
       and type layout = Bap_emu_jni.layout

  val install : t -> emulator -> layout -> unit
  val serve : t -> emulator -> unit
  val serve_vm : t -> emulator -> unit
  val read_string : emulator -> int64 -> string

  val bind_checkpoint :
    ?package:string ->
    ?version:int ->
    ?required:bool ->
    checkpoint_models ->
    t ->
    unit
  (** [bind_checkpoint models jni] registers JNI state as [user:jni], required
      and at schema version 1 by default. *)
end

(** reusable Android ServiceManager, IBinder, and Parcel models *)
module Android : sig
  include module type of Bap_emu_android

  val bind_checkpoint :
    ?package:string ->
    ?version:int ->
    ?required:bool ->
    checkpoint_models ->
    t ->
    unit
  (** [bind_checkpoint models android] registers Android state as
      [user:android], required and at schema version 1 by default. *)
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

val set_snapshot_limit : t -> int option -> unit
(** [set_snapshot_limit emu limit] retains at most [limit] snapshots, or all of
    them with [None], which is the default. Snapshots are managed in creation
    order; creating a snapshot or lowering the limit drops the oldest snapshots
    through {!drop_snapshot}. [Some 0] drops every snapshot as it is created.
    Explicit drops and snapshots made by the interactive shell share the same
    bookkeeping. Restoring a retained snapshot does not consume it or change its
    age. Raises [Invalid_argument] for a negative limit or if the program is not
    paused. *)

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

val save : ?parent:string -> t -> string -> unit
(** [save emu file] saves the checkpoint of the paused program to the [file],
    from which {!create} continues it, in another run of bap too. With [parent],
    saves a versioned delta whose sparse memory changes are relative to that
    checkpoint, while retaining the complete non-memory state. The parent is
    resolved, and its canonical path and actual file digest are recorded;
    relative parent paths in deltas are resolved from the delta's directory.
    Delta publication is atomic and refuses any existing destination. Without
    [parent], the existing full format and its atomic replacement behavior are
    unchanged, e.g.,

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
    [Primus.Checkpoint] and {!Checkpoint.register}, e.g., the channels of Primus
    Lisp, which are opened anew, with the positions of their inputs, and the
    states of script models, the digest of the file of the program, which the
    checkpoint is of, the runs of Unicorn, that Primus called, with the stubs,
    that called them, and the bytes of the instructions, that the lifted engine
    ran, see {!insn_at}. The names of the program and its stubs are of its file,
    which is loaded anew.

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

val set_lift_cache_limit : t -> int option -> unit
(** [set_lift_cache_limit emu limit] bounds the session lifter to the [limit]
    least-recently-used entries, or makes it unbounded with [None]. [Some 0]
    retains no entries. Eviction does not remove code already retained by the
    lifted engine, and executed instructions keep their raw-byte checkpoint
    history. Ordinary eviction defers disk writes to scheduled maintenance,
    checkpoints, {!forget_lifts}, {!save_lifts}, and clean exit, with one
    coalesced save if 1024 entries are archived. This conservative high-water
    bound replaces the former 64-entry save cadence; {!maintenance_stats}
    exposes save counts, durations, entries, and bytes for evaluating it. Every
    save merges retained and archived entries with the existing disk cache.
    Raises [Invalid_argument] for a negative limit. *)

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

type deadline

val start_deadline : ?code:int -> float -> deadline
(** [start_deadline ~code seconds] starts a native watchdog that terminates the
    actual BAP process with [code] (124 by default) after [seconds], including
    during native execution that holds the OCaml runtime lock. This is an
    immediate operating-system process exit, not a guest pause. Raises
    [Invalid_argument] for a negative or non-finite duration. *)

val cancel_deadline : deadline -> unit
(** [cancel_deadline deadline] prevents an active deadline from expiring. *)

type component_footprint = {
  lifter_entries : int;  (** retained session-lifter instructions *)
  lifter_blocks : int;  (** BIR blocks retained by the session lifter *)
  knowledge_objects : int;
      (** live [Theory.Program.cls] objects in the session lifter's retained
          [Knowledge.state], or zero if no state is retained *)
  lift_history : int;  (** raw-byte history entries, including restored ones *)
  engine_entries : int;  (** instructions retained by the lifted engine *)
  engine_blocks : int;  (** BIR blocks retained by the lifted engine *)
  jit_blocks : int;  (** live compiled blocks of the lifted engine *)
  hook_entries : int;  (** shared and paused script-hook lift entries *)
  stored_bytes : int;  (** logical stored byte entries, not heap bytes *)
  sparse_pages : int;  (** sparse pages of the current machine *)
  snapshots : int;  (** live snapshots created by the script *)
  snapshot_bytes : int;  (** logical stored byte entries of live snapshots *)
  snapshot_pages : int;  (** sparse pages of live snapshots *)
  parked_pages : int;  (** native pages retained for snapshots *)
  trace_records : int;
      (** records in live trace rings owned by this emulator *)
  trace_accesses : int;  (** access records in those rings *)
  decoded_blocks : int;  (** cached block expansions of those traces *)
  script_models : int;  (** checkpoint models registered for this emulator *)
}

val components : t -> component_footprint
(** [components emu] is a logical retention inventory of the paused emulator.
    [knowledge_objects] is computed on demand and is independent of the lift
    entries: {!forget_lifts} doesn't discard the lifter's retained semantics
    state. Counts are not estimated heap sizes and are not additive: hook lifts
    may be shared between emulators, persistent byte maps and snapshot sparse
    pages may share structure and contents, and raw-byte history may overlap
    after restore. Snapshot counts aggregate the live snapshots' logical states;
    [parked_pages] separately counts their native backing pages. Trace counts
    include live rings owned by the emulator, whether recording or stopped, and
    [decoded_blocks] counts their cached block expansions. Unicorn does not
    expose its internal translation inventory, so engine counts are zero there.
    Raises [Invalid_argument] if the program is not paused. *)

(** The checkpoints, that {!save} wrote, which a script inspects, without
    loading their program, e.g., to choose one in a pipeline. *)
module Checkpoint : sig
  type registry = checkpoint_models

  val create : unit -> registry
  (** [create ()] constructs an empty per-emulator model registry. Pass it to
      {!Bap_emu.create} with [~models]. Independent registries may reuse model
      names without sharing callbacks or state. *)

  val register :
    ?package:string ->
    ?version:int ->
    ?required:bool ->
    registry ->
    string ->
    save:(unit -> string option) ->
    restore:(string -> unit) ->
    unit
  (** [register models ?package ?version ?required name ~save ~restore]
      registers serializable model state under [package:name], where [package]
      is ["user"], [version] is 1, and [required] is [false] by default. Every
      checkpoint of an emulator using [models] saves [save ()], unless it is
      [None], and restore calls [restore]. Register the same name and schema
      before {!Bap_emu.create} restores a checkpoint. A required model must have
      state and a matching schema. Optional mismatches are skipped with a
      warning. Callback exceptions abort the operation. Host closures and
      handles are not serialized; scripts reinstall them and register only their
      serializable state. Raises [Invalid_argument] if the name is registered in
      this registry or is a built-in extension, or if the version is not
      positive. *)

  val register_ref :
    ?package:string ->
    ?version:int ->
    ?required:bool ->
    registry ->
    string ->
    (module Core.Binable.S with type t = 'a) ->
    'a ref ->
    unit
  (** [register_ref models name binable state] registers the contents of
      [state], as {!register} does with [binable]. *)

  val register_table :
    ?package:string ->
    ?version:int ->
    ?required:bool ->
    registry ->
    string ->
    (module Core.Binable.S with type t = ('key * 'value) list) ->
    ('key, 'value) Core.Hashtbl.t ->
    unit
  (** [register_table models name binable table] registers the bindings of
      [table]. The restored bindings are decoded before the table is changed. *)

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
    quantum_remaining : float;
        (** the active thread's remaining scheduler slice in seconds *)
  }

  val info : string -> info
  (** [info file] reads the checkpoint, raises [Failure], if it is not one, or
      of another version, or broken. *)

  val journal : string -> event list
  (** [journal file] is the saved thread creation, exit, and switch journal, in
      execution order. Raises as {!info}. *)

  type model_state = { name : string; version : int; required : bool }

  val models : string -> model_state list option
  (** [models file] is the model-state manifest of the checkpoint, or [None] for
      a legacy checkpoint without one. Raises as {!info}. *)

  val describe : string -> string
  (** [describe file] summarizes the target, program digest, every thread's
      resume PC and wait reason, and model names, versions, and requirements.
      Raises as {!info}. *)

  type link = {
    file : string;  (** the canonical checkpoint path *)
    version : int;  (** the full or delta envelope version *)
    digest : string;  (** the hex MD5 digest of this checkpoint file *)
    parent : (string * string) option;
        (** the stored parent path and expected file digest, or [None] at the
            root *)
    models : model_state list option;  (** this link's model-state manifest *)
  }

  val chain : string -> link list
  (** [chain file] resolves [file] and returns every link, root first. Parent
      paths are interpreted relative to the containing delta. Resolution rejects
      missing or truncated files, digest mismatches, cycles, unsupported
      versions, and malformed states. Raises [Failure] with the resolution
      error. *)

  type context = {
    thread : thread;
    frames : (string option * string option) list;
    models : model_state list option;
    failure : failure option;
    events : event list;
  }

  val context : string -> context
  (** [context file] is the active thread, native frames, model manifest, last
      unrecoverable fault, and last 32 model events in the checkpoint. *)

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

val backtrace : ?thread:int -> t -> (string option * string option) list
(** [backtrace emu ~thread:tid] is the run frames of the selected thread, the
    innermost first, with the function that runs and the stub that called it.
    These are Primus-to-native runs, not every native-to-native call. Threads
    switch at the same run depth, so active and parked threads share these
    surrounding frames. Raises [Invalid_argument] if the program is not paused,
    or for an unknown thread. *)

val thread_regs : t -> int -> (string * int64) list
(** [thread_regs emu tid] the registers, without the aliases, of the thread of
    the paused program, by its TID, see {!threads}, e.g., of the one, that waits
    on a lock, to tell, which lock it waits on, from its arguments: of the
    engine, for the thread, that runs, and else, as the thread had them, when it
    stopped running. The values preserve all 64 bits, including the highest bit.
    Registers whose values aren't representable in 64 bits are omitted;
    {!reg_word} reads the full-width value of a register of the active thread.
    Raises [Invalid_argument], if the program is not paused, or has no such
    thread. *)

val set_thread_reg : t -> int -> string -> int64 -> unit
(** [set_thread_reg emu tid name value] sets the register of an active or parked
    thread. Raises [Invalid_argument] for an unknown thread or register. *)

val set_thread_pc : t -> int -> int64 -> unit
(** [set_thread_pc emu tid addr] sets the address from which an active or parked
    thread continues. Raises [Invalid_argument] for an unknown thread. *)

val resume_thread : t -> int -> unit
(** [resume_thread emu tid] resumes a ready parked thread, or does nothing for
    the active thread. Raises [Invalid_argument] for an unknown or waiting
    thread. *)

val threads : t -> Checkpoint.thread list
(** [threads emu] the threads of the paused program, the one, that runs, at the
    address, at which it paused, first, and the others, with the addresses, from
    which they continue, and the addresses, on which they wait, e.g., their
    futexes, by their TIDs, e.g., to tell, why a program, that stops
    progressing, spins, with {!Trace.hot} and {!Trace.addresses}. The threads,
    that wait without a futex, e.g., on a flag, that they poll, aren't waiting,
    see {!Checkpoint.thread.waiting}. Raises [Invalid_argument], if the program
    is not paused. *)

val thread_journal : t -> event list
(** [thread_journal emu] is the last 256 thread creation, exit, and switch
    events, in execution order. Creation records the child TID, entry, and
    startup argument or raw-clone stack; exits record the TID and status;
    switches record both TIDs and the resume PC. This runtime journal is
    separate from the bounded model-event journal kept in checkpoints. *)

type stack_stats = {
  lower : int64;  (** inclusive lower bound of the call stack *)
  upper : int64;  (** exclusive upper bound of the call stack *)
  lowest_sp : int64;  (** lowest SP observed at an instruction boundary *)
  max_usage : int64;  (** [upper - lowest_sp] *)
}

type execution_stats = {
  instructions : int64;  (** fresh guest instructions since subscription *)
  lifted_blocks : int;  (** BIR blocks currently retained by the engine *)
  active_threads : int;  (** active and parked guest threads *)
  hook_dispatches : int;  (** cumulative native write-hook dispatches *)
  rss : int option;  (** process resident bytes, where available *)
  last_pc : int64;  (** guest PC at the report pause *)
  stack : stack_stats option;
      (** the innermost active or most recently finished {!call}/{!drive} stack
      *)
}

val execution_stats : t -> execution_stats
(** [execution_stats emu] captures the counters of the paused emulator. [stack]
    describes the innermost active call stack, or the most recently finished
    one, whose allocation is retained after failure and cleaned up after
    success; it is [None] before the first call. Raises [Invalid_argument] if
    the program is not paused. *)

type operation_stats = {
  count : int;  (** operations performed, or entries for entry eviction *)
  seconds : float;  (** cumulative monotonic duration of those operations *)
}

type maintenance_stats = {
  lru_reconstruction : operation_stats;
  entry_eviction : operation_stats;
  cache_load : operation_stats;
  cache_merge : operation_stats;
  cache_write : operation_stats;
  lift_cleanup : operation_stats;
  block_reclamation : operation_stats;
  heap_compaction : operation_stats;
  cache_entries_written : int;
      (** entries in all successfully written cache files, including entries
          written again by a merge *)
  cache_bytes_written : int;  (** bytes of those files, including their magic *)
}

val maintenance_stats : t -> maintenance_stats
(** [maintenance_stats emu] returns the cumulative maintenance telemetry of the
    paused emulator. It covers LRU reconstruction and entry eviction by
    {!set_lift_cache_limit}, cache loading, merging and writing, explicit and
    periodic {!forget_lifts} cleanup, and the block reclamation and heap
    compaction requested through {!start_maintenance}. Cache counters are zero
    without a persistent lift cache, and operations that do not run have zero
    count and duration.

    Counters start at zero when {!create} creates the emulator and are never
    reset individually. Snapshot restore keeps them; checkpoints do not
    serialize them, so an emulator created with [~restore] starts a fresh set.
    Creating a new emulator is the only reset. Raises [Invalid_argument] if the
    program is not paused. *)

type stats_subscription

val start_stats :
  t -> interval:float -> (execution_stats -> unit) -> stats_subscription
(** [start_stats emu ~interval f] counts fresh guest instructions and pauses
    briefly every [interval] seconds to call [f] with current statistics. The
    callback runs at a safe paused state, and execution continues unless the
    callback stops it. Raises [Invalid_argument] for a nonpositive or non-finite
    interval, or if the program is not paused. *)

val stop_stats : stats_subscription -> unit
(** [stop_stats subscription] removes the instruction hook and suppresses any
    deferred report. Statistics subscriptions also respect {!scoped}. *)

val start_maintenance :
  t ->
  interval:float ->
  ?lift_cache_limit:int ->
  ?forget_lifts:bool ->
  ?reclaim_blocks:bool ->
  ?compact_heap:bool ->
  unit ->
  stats_subscription
(** [start_maintenance emu ~interval ()] performs periodic maintenance at the
    safe paused reports of {!start_stats}. [lift_cache_limit] applies
    {!set_lift_cache_limit} once at startup. Every report saves dirty lifts,
    even when all cleanup and reclamation options are false. If [forget_lifts]
    is true, each report calls {!forget_lifts}, including its save; if
    [reclaim_blocks] is true, it drops the engine's translated blocks, which are
    translated again as execution continues; and if [compact_heap] is true, it
    calls [Gc.compact]. All maintenance actions default to false or absent, and
    no maintenance is installed unless this function is called.

    Stop the returned subscription with {!stop_stats}; subscriptions also
    respect {!scoped}. Stopping suppresses future maintenance but does not undo
    the lift-cache limit. Raises [Invalid_argument] for an invalid interval or
    negative lift-cache limit, or if the program is not paused. *)

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
