(** The lifted engine, which runs the semantics of the instructions, that BAP
    lifts, with the interface of {!Bap_unicorn}.

    Each instruction is lifted, when it runs first, and compiled to the
    closures, and the blocks, that run often, are compiled by the JIT of LLVM
    to the native code of the host. The instruction, that the engine can't
    run, e.g., whose semantics call an intrinsic, calls the hooks of
    {!on_unsupported}, which stop the engine, so that it is interpreted, e.g.,
    by Primus. An instruction runs as a transaction: its writes are undone, if
    it faults, so that it runs again after the hooks of the invalid access, as
    in Unicorn.

    The registers are the ones of Unicorn, by their identifiers, and of their
    sizes, see {!Bap_unicorn.regs}, whose bits are the registers of BAP, see
    [config.locate], and the memory is the pages of 4 KB with their
    permissions.

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
  pc : int;  (** the register, that is the program counter *)
  big_endian : bool;  (** the order of the bytes of the memory *)
  bits : int;  (** the size of an address *)
  jit : bool;  (** if the blocks, that run often, are compiled *)
}

type t
type hook

val create : config -> Bap_unicorn.arch -> Bap_unicorn.Mode.t -> t
val close : t -> unit
val flush_tb : t -> unit

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
    hasn't, e.g., the base of a segment of x86, see
    [Bap_engine.set_unmapped]. *)

val reg_size : t -> int -> int
val reg_read : t -> int -> int64
val reg_write : t -> int -> int64 -> unit
val reg_read_bytes : t -> int -> string
val reg_write_bytes : t -> int -> string -> unit

(** {2 Emulation} *)

val start : ?until:int64 -> ?timeout:int -> ?count:int -> t -> int64 -> unit
val stop : t -> unit

(** {2 Hooks} *)

val on_code : ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val on_block :
  ?first:int64 -> ?last:int64 -> t -> (int64 -> int -> unit) -> hook

val on_interrupt : t -> (int -> unit) -> hook
val on_invalid_insn : t -> (unit -> bool) -> hook

val on_unsupported : t -> (int64 -> unit) -> hook
(** [on_unsupported t f] calls [f addr], before the instruction at [addr],
    that the engine can't run, which stops it, see
    [Bap_engine.on_unsupported]. *)

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
  ?memory:bool ->
  t ->
  Bap_unicorn.Trace.t ->
  hook list
(** [trace t trace] records the trace, as {!Bap_unicorn.trace} does. *)

(** {2 Contexts} *)

type context

val save : t -> context
val restore : t -> context -> unit
