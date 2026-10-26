(** The engines, that run the native code of the programs.

    The interface of {!Bap_unicorn}, whose functions run in one of the engines:
    Unicorn, or the lifted engine, which runs the semantics of the instructions,
    that BAP lifts, see {!Lifted}. The engine, that can't run an instruction,
    e.g., as its semantics calls an intrinsic, calls the hooks of
    {!on_unsupported}, so that the instruction is interpreted, e.g., by Primus.

    See {!Bap_unicorn} for the documentation of the functions. *)

exception Error of int * string

type t
type arch = Bap_unicorn.arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

module Mode = Bap_unicorn.Mode
module Perm = Bap_unicorn.Perm
module Cpu = Bap_unicorn.Cpu

(** The lifted engine. *)
module Lifted : sig
  type config = {
    lift :
      thumb:bool ->
      int64 ->
      string ->
      (int * string * Bap.Std.blk Bap.Std.term list) option;
        (** [lift ~thumb addr bytes] the size, the name, e.g., [tBLXi] of LLVM,
            and the lifted blocks of the instruction, which starts the bytes at
            [addr], in the Thumb state of ARM, if [thumb], or [None] if it is
            not an instruction *)
    name : Bap.Std.tid -> string option;
        (** [name tid] the name of the label, that an instruction calls, e.g.,
            [intrinsic:fadd_rne_ieee754_binary_64], which the engine runs, as
            ieee754-intrinsics.lisp of Primus Lisp runs it *)
    policy : int;
        (** the NaNs and the invalid integers of the target, as the
            ieee754-policy of ieee754-intrinsics.lisp *)
    delay : string -> [ `None | `Delayed | `Likely | `Forbidden ];
        (** [delay code] if the instruction of the bytes is a branch, whose
            delay slot, e.g., of MIPS, runs before its target, if it is taken,
            or always, and else runs only if it is taken, if it is likely *)
    locate : string -> (int * int * int) option;
        (** [locate name] the register of the engine, and the bits of it, from
            the lowest, and their number, of the register [name] of BAP, as
            [Primus_native_target.Regs] maps them; the registers have the sizes
            of the registers of Unicorn *)
    owner : string -> string option;
        (** [owner name] the register of the basis, that holds the register
            [name], whose taint it has, see {!taint_start} *)
    pc : int;  (** the register of the engine, that is the program counter *)
    big_endian : bool;  (** the order of the bytes of the memory *)
    bits : int;  (** the size of an address *)
    jit : bool;
        (** if the blocks, that run often, are compiled to the native code, see
            {!Bap_lifted} *)
    cache : string option;
        (** the folder of the compiled blocks, see {!Bap_lifted.config} *)
  }
end

val version : unit -> int * int
val supported : arch -> bool

val create : arch -> Mode.t -> t
(** [create arch mode] opens Unicorn. *)

val create_lifted : Lifted.config -> arch -> Mode.t -> t
(** [create_lifted config arch mode] opens the lifted engine. *)

val is_lifted : t -> bool
(** [is_lifted t] if [t] is the lifted engine. *)

val close : t -> unit
val set_cpu_model : t -> int -> unit
val set_tlb_virtual : t -> unit
val flush_tb : t -> unit

val insn_at :
  t -> int64 -> (string * string * bool * Bap.Std.blk Bap.Std.term list) option
(** [insn_at t pc] the instruction, that the lifted engine lifted at [pc], to
    run it, see {!Lifted.insn_at}, or [None] in Unicorn, which translates the
    code in itself. *)

val insn_addrs : t -> int64 list
(** the addresses of the instructions, that {!insn_at} has, in no order, none in
    Unicorn *)

val inventory : t -> int * int * int

(** {2 Memory} *)

val mem_map : t -> int64 -> int64 -> Perm.t -> unit
val mem_unmap : t -> int64 -> int64 -> unit
val mem_protect : t -> int64 -> int64 -> Perm.t -> unit
val mem_write : t -> int64 -> string -> unit
val mem_read : t -> int64 -> int -> string
val mem_regions : t -> (int64 * int64 * Perm.t) list

(** {2 Registers} *)

val set_unmapped : t -> string -> Bap.Std.word -> unit
(** [set_unmapped t name x] sets the register [name] of BAP, that Unicorn
    hasn't, e.g., the base of a segment of x86, in the protected mode, which the
    lifted engine reads, as the semantics of BAP do, and which Unicorn reads
    from the descriptor of the segment. Unicorn ignores it. *)

val regs : arch -> (string * int) list
val reg : arch -> string -> int option
val reg_size : t -> int -> int
val reg_read : t -> int -> int64
val reg_write : t -> int -> int64 -> unit

val current : t -> pc:int -> int64
(** [current t ~pc] the address of the instruction, that runs, e.g., in a hook
    of the memory, which Unicorn has in its register [pc], or of the next one,
    when the engine is stopped *)

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
(** [in_atomic t] if the lifted engine stopped in an atomic sequence, e.g.,
    between ll and sc of MIPS, in which the threads don't switch, as its store
    conditional succeeds, whatever another thread wrote, see
    {!Bap_lifted.in_atomic}. Unicorn is never in one, as its store conditional
    fails, if the memory changed. *)

(** {2 Taint}

    The taint, that the lifted engine propagates itself, see
    {!Bap_lifted.taint_start}, which Unicorn doesn't, whose functions do
    nothing, but [taint_start], which raises [Invalid_argument]. *)

val taint_start : ?jumps:bool -> t -> unit
val taint_stop : t -> unit
val taint_active : t -> bool
val taint_any : t -> bool
val taint_clear : ?regs:bool -> ?mem:bool -> t -> unit
val taint_labels : t -> (int * [ `All | `Moves | `None ]) list -> unit
val reg_labels : t -> string -> int list
val set_reg_labels : t -> string -> int list -> unit
val mem_labels : t -> int64 -> int list
val set_mem_labels : t -> int64 -> int list -> unit
val tainted_regs : t -> string list
val tainted_mem : t -> int64 list
val taint_changes : t -> string list * int64 list

type taint = Bap_lifted.taint
(** see {!Bap_lifted.taint} *)

val no_taint : taint
val tainted : taint -> bool
val taint_jumps : t -> bool
val union_taint : t -> taint -> taint -> taint
val moves_taint : t -> taint -> taint
val reg_taint : t -> string -> taint
val mem_range_taint : t -> int64 -> int -> taint
val set_reg_taint : t -> string -> taint -> unit
val fill_mem_taint : t -> int64 -> int -> taint -> unit
val copy_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
val move_mem_taint : t -> dst:int64 -> src:int64 -> int -> unit
val interrupted : unit -> bool
val process_signals : unit -> unit

(** {2 Hooks} *)

type hook

type access = Bap_unicorn.access =
  | Read
  | Write
  | Fetch
  | Read_unmapped
  | Write_unmapped
  | Fetch_unmapped
  | Write_prot
  | Read_prot
  | Fetch_prot
  | Read_after

val on_code : ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val attempt : t -> int64 option
(** the instruction attempt number in Unicorn, or [None] in the lifted engine *)

val on_sites : t -> int64 list -> (int64 -> int -> unit) -> hook list
(** [on_sites t sites f] calls [f addr size] before each instruction at one of
    the [sites], which the engine finds natively, e.g., in a set, so that many
    sites cost about as much as one, rather than a hook each. *)

val on_block :
  ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val on_interrupt : t -> (int -> unit) -> hook
val on_x86_syscall : t -> (unit -> unit) -> hook list
val on_invalid_insn : t -> (unit -> bool) -> hook

val on_unsupported : t -> (int64 -> unit) -> hook
(** [on_unsupported t f] calls [f addr], before the instruction at [addr], that
    the engine can't run, e.g., whose semantics calls an intrinsic, which must
    stop the emulation, so that the instruction is interpreted, and the
    emulation continues after it. Unicorn never calls it. *)

val on_mem :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch | `read_after ] list ->
  (access -> int64 -> int -> int64 -> unit) ->
  hook

val on_mem_invalid :
  ?first:int64 ->
  ?last:int64 ->
  t ->
  [ `read | `write | `fetch ] list ->
  [ `unmapped | `prot ] list ->
  (access -> int64 -> int -> int64 -> bool) ->
  hook

val delete : t -> hook -> unit

(** {2 Traces} *)

module Trace = Bap_native_trace

val trace :
  ?first:int64 ->
  ?last:int64 ->
  ?watch:int64 * int64 ->
  ?memory:bool ->
  t ->
  Trace.t ->
  hook list
(** [trace t trace] records the trace, see {!Bap_unicorn.trace}, in either
    engine. *)

(** {2 Contexts} *)

type context

val save : t -> context
val restore : t -> context -> unit
