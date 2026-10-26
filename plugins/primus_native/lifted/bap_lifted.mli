(** The lifted engine, which runs the semantics of the instructions, that BAP
    lifts, with the interface of {!Bap_unicorn}.

    Each instruction is lifted, when it runs first, and compiled to the
    closures, and the blocks, that run often, are compiled by the JIT of LLVM to
    the native code of the host. The instruction, that the engine can't run,
    e.g., whose semantics call an intrinsic, calls the hooks of
    {!on_unsupported}, which stop the engine, so that it is interpreted, e.g.,
    by Primus. An instruction runs as a transaction: its writes are undone, if
    it faults, so that it runs again after the hooks of the invalid access, as
    in Unicorn.

    The registers are the ones of Unicorn, by their identifiers, and of their
    sizes, see {!Bap_unicorn.regs}, whose bits are the registers of BAP, see
    [config.locate], and the memory is the pages of 4 KB with their permissions.

    The program, that the engine runs, is untrusted: its accesses check the
    pages, and its code, that the JIT compiles, is limited, see
    bap_lifted_jit.ml.

    See {!Bap_unicorn} for the documentation of the functions. *)

type config = {
  lift :
    thumb:bool ->
    int64 ->
    string ->
    (int * string * Bap.Std.blk Bap.Std.term list) option;
      (** [lift ~thumb addr bytes] the size, the name, and the lifted blocks of
          the instruction, which starts the bytes at [addr], see
          [Bap_engine.Lifted.config] *)
  name : Bap.Std.tid -> string option;
      (** the name of the label, that an instruction calls, e.g., of an
          intrinsic *)
  policy : int;  (** the NaNs and the invalid integers of the target *)
  delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
      (** the delay slot of the branch of the bytes *)
  locate : string -> (int * int * int) option;
      (** the register of the engine, and its bits, of the register of BAP *)
  owner : string -> string option;
      (** the register of the basis, that holds the register of BAP, e.g., RAX
          for EAX, whose taint it has, see {!taint_start} *)
  pc : int;  (** the register, that is the program counter *)
  big_endian : bool;  (** the order of the bytes of the memory *)
  bits : int;  (** the size of an address *)
  jit : bool;  (** if the blocks, that run often, are compiled *)
  cache : string option;
      (** the folder of the objects of the blocks, that the JIT compiled, which
          the other runs of the same code read, rather than compile them *)
}

type t
type hook

val create : config -> Bap_unicorn.arch -> Bap_unicorn.Mode.t -> t
val close : t -> unit
val flush_tb : t -> unit

val insn_at :
  t -> int64 -> (string * string * bool * Bap.Std.blk Bap.Std.term list) option
(** [insn_at t pc] the bytes, the name, the mode, Thumb or not, and the
    semantics of the instruction, that the engine lifted at [pc], to run it,
    from the bytes, that the memory had then, which stay, when the memory
    changes, until the engine lifts the instruction anew, or [None], if none was
    lifted there. {!flush_tb} keeps the instructions, whose bytes are checked,
    when they run, and drops the blocks, that the JIT compiled. *)

val insn_addrs : t -> int64 list
(** the addresses of the instructions, that {!insn_at} has, in no order *)

val inventory : t -> int * int * int

(** {2 Memory} *)

val mem_map : t -> int64 -> int64 -> Bap_unicorn.Perm.t -> unit
val mem_unmap : t -> int64 -> int64 -> unit
val mem_protect : t -> int64 -> int64 -> Bap_unicorn.Perm.t -> unit
val mem_write : t -> int64 -> string -> unit
val mem_read : t -> int64 -> int -> string
val mem_regions : t -> (int64 * int64 * Bap_unicorn.Perm.t) list

(** {2 Registers} *)

val set_unmapped : t -> string -> Bap.Std.word -> unit
(** [set_unmapped t name x] sets the register [name] of BAP, that Unicorn
    hasn't, e.g., the base of a segment of x86, see [Bap_engine.set_unmapped].
*)

val reg_size : t -> int -> int
val reg_read : t -> int -> int64
val reg_write : t -> int -> int64 -> unit

val current : t -> int64
(** [current t] the address of the instruction, that runs, e.g., in a hook of
    the memory, or of the next one, when the engine is stopped, see
    [Bap_engine.current] *)

val reg_read_bytes : t -> int -> string
val reg_write_bytes : t -> int -> string -> unit
val registers_restored : t -> unit

(** {2 Emulation} *)

val start :
  ?until:int64 ->
  ?timeout:int ->
  ?count:int ->
  ?thread:int ->
  t ->
  int64 ->
  unit

val stop : t -> unit

val in_atomic : t -> bool
(** [in_atomic t] if the engine stopped between a load linked and its store
    conditional, e.g., ll and sc of MIPS, whose semantics have no reservation,
    so that the store succeeds, if another thread writes in between, which the
    threads must not do, see [Bap_engine.in_atomic]. *)

(** {2 Hooks} *)

val on_code : ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val on_block :
  ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val on_interrupt : t -> (int -> unit) -> hook
val on_invalid_insn : t -> (unit -> bool) -> hook

val on_unsupported : t -> (int64 -> unit) -> hook
(** [on_unsupported t f] calls [f addr], before the instruction at [addr], that
    the engine can't run, which stops it, see [Bap_engine.on_unsupported]. *)

val on_sites : t -> int64 list -> (int64 -> int -> unit) -> hook
(** [on_sites t sites f] calls [f addr size] before each instruction at one of
    the [sites], which a set keeps, so that many sites cost one lookup, rather
    than one range each. *)

val on_mem :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch | `read_after ] list ->
  (Bap_unicorn.access -> int64 -> int -> int64 -> unit) ->
  hook

val on_mem_invalid :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch ] list ->
  [ `unmapped | `prot ] list ->
  (Bap_unicorn.access -> int64 -> int -> int64 -> bool) ->
  hook

val delete : t -> hook -> unit

(** {2 Traces} *)

val trace :
  ?first:int64 ->
  ?last:int64 ->
  ?watch:int64 * int64 ->
  ?memory:bool ->
  t ->
  Bap_native_trace.t ->
  hook list
(** [trace t trace] records the trace, as {!Bap_unicorn.trace} does. *)

(** {2 Taint}

    The engine propagates the taint itself, rather than the interpreter, while
    it is started, as the sets of the labels, e.g., of the tainted objects, of
    the registers, by the names of their bases, see [config.owner], and of the
    bytes of the memory. A label propagates through the computations, e.g., the
    arithmetic, if its class is [`All], through the moves only, e.g., the loads,
    the stores, the casts, the extractions, and the concatenations, if it is
    [`Moves], or not at all. The instruction, that reads a tainted register, or
    accesses the memory, while a byte is tainted, runs in the closures, that
    propagate it, and the blocks, that the JIT compiled, run, unless they read a
    tainted register, as their accesses of the tainted pages stop them. The
    conditions of [Ite] don't taint its value. *)

val taint_start : ?jumps:bool -> t -> unit
(** [taint_start t] starts the propagation of the taint. With [jumps], the jump,
    whose condition is tainted, e.g., which its observers see, is unsupported,
    as the intrinsic of a tainted value always is, see {!on_unsupported}. *)

val taint_stop : t -> unit
(** [taint_stop t] stops it, and clears the taint *)

val taint_active : t -> bool

val taint_any : t -> bool
(** [taint_any t] if a register or a byte is tainted *)

val taint_clear : ?regs:bool -> ?mem:bool -> t -> unit
(** [taint_clear t] clears the taint of the registers, unless [regs] is [false],
    and of the memory, unless [mem] is [false] *)

val taint_labels : t -> (int * [ `All | `Moves | `None ]) list -> unit
(** [taint_labels t classes] the classes of the labels, the others are [`None]
*)

val reg_labels : t -> string -> int list
val set_reg_labels : t -> string -> int list -> unit
val mem_labels : t -> int64 -> int list
val set_mem_labels : t -> int64 -> int list -> unit
val tainted_regs : t -> string list
val tainted_mem : t -> int64 list

val taint_changes : t -> string list * int64 list
(** [taint_changes t] the registers and the bytes, whose taint the instructions
    changed, since it was called last, rather than [set_*_labels] *)

(** The taint of the values, that the engine doesn't compute, e.g., the native
    functions of the executor, whose changes are among the changes of
    {!taint_changes}. *)

type taint

val no_taint : taint
val tainted : taint -> bool
val taint_jumps : t -> bool
val union_taint : t -> taint -> taint -> taint

val moves_taint : t -> taint -> taint
(** [moves_taint t x] the labels of [x], that the moves propagate *)

val reg_taint : t -> string -> taint
(** [reg_taint t name] the taint of the register, by the name of its base *)

val mem_range_taint : t -> int64 -> int -> taint
(** [mem_range_taint t addr n] the taint of the bytes *)

val set_reg_taint : t -> string -> taint -> unit

val fill_mem_taint : t -> int64 -> int -> taint -> unit
(** [fill_mem_taint t addr n x] the bytes have the labels of [x], that the moves
    propagate *)

val copy_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
(** [copy_mem_taint t ~dst ~src n] the bytes have the taint of the source, as
    they are copied by one, from the first, by the moves *)

val move_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
(** [move_mem_taint t ~dst ~src n] as [copy_mem_taint], as if the source is read
    first *)

(** {2 Contexts} *)

type context

val save : t -> context
val restore : t -> context -> unit
