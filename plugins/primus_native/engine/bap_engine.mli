(** The common interface of the engines that run native code.

    A backend implements {!BACKEND} with concrete engine, hook, and context
    types. {!Make} exposes that typed implementation and erases an engine into a
    record of closures created once. Hooks and contexts own their backend
    instance, so deleting a hook or restoring a context needs no engine
    argument. Backend adapters provide construction and backend-specific
    operations. *)

exception Error of int * string

type t
type engine = t
type hook
type context
type arch = Arm | Arm64 | Mips | X86 | Ppc | Riscv

module Mode : sig
  type t = private int

  val ( + ) : t -> t -> t
  val little_endian : t
  val big_endian : t
  val arm : t
  val thumb : t
  val mclass : t
  val v8 : t
  val mips32 : t
  val mips64 : t
  val mode16 : t
  val mode32 : t
  val mode64 : t
  val ppc32 : t
  val ppc64 : t
  val riscv32 : t
  val riscv64 : t
end

module Perm : sig
  type t = private int

  val ( + ) : t -> t -> t
  val ( - ) : t -> t -> t
  val none : t
  val read : t
  val write : t
  val exec : t
  val all : t
  val mem : t -> t -> bool
end

module Cpu : sig
  val arm64_max : int
  val mips32r6_generic : int
  val mips64r2_generic : int
  val mips64_i6400 : int
end

(** Backend-neutral physical register layouts. *)
module Register : sig
  type t = {
    id : int;
    size : int;  (** the width in bytes, including wide registers *)
    reset : int64 option;
        (** the nonzero reset value, if the register has one *)
  }

  val by_name : arch -> bits:int -> string -> t option
  (** [by_name arch ~bits name] describes [name] in the [bits]-bit layout of
      [arch]. Names are case-insensitive. *)

  val by_id : arch -> bits:int -> int -> t option
  (** [by_id arch ~bits id] describes the physical register [id], including its
      width and reset state. *)
end

module Trace = Bap_native_trace

type taint = int
(** the integer identifier of a set of taint labels *)

type access =
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

(** The operations of a native engine with owned hooks and contexts. *)
module type S = sig
  type t
  type hook
  type context

  val close : t -> unit
  val set_cpu_model : t -> int -> unit
  val set_tlb_virtual : t -> unit
  val flush_tb : t -> unit

  val insn_at :
    t ->
    int64 ->
    (string * string * bool * Bap.Std.blk Bap.Std.term list) option

  val insn_addrs : t -> int64 list
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
  val reg_size : t -> int -> int
  val reg_read : t -> int -> int64
  val reg_write : t -> int -> int64 -> unit
  val current : t -> pc:int -> int64
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

  (** {2 Taint} *)

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

  (** {2 Hooks} *)

  val attempt : t -> int64 option

  val on_code :
    ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

  val on_sites : t -> int64 list -> (int64 -> int -> unit) -> hook list

  val on_block :
    ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

  val on_interrupt : t -> (int -> unit) -> hook
  val on_x86_syscall : t -> (unit -> unit) -> hook list
  val on_invalid_insn : t -> (unit -> bool) -> hook
  val on_unsupported : t -> (int64 -> unit) -> hook

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

  val delete : hook -> unit

  (** {2 Traces} *)

  val trace :
    ?first:int64 ->
    ?last:int64 ->
    ?watch:int64 * int64 ->
    ?memory:bool ->
    t ->
    Trace.t ->
    hook list

  (** {2 Contexts} *)

  val save : t -> context
  val restore : context -> unit
end

module type BACKEND = S

include S with type t := t and type hook := hook and type context := context

(** [Make (B)] is the typed backend [B], together with one-time erasure. *)
module Make (B : BACKEND) : sig
  include
    S with type t := B.t and type hook := B.hook and type context := B.context

  val erase : B.t -> engine
end
