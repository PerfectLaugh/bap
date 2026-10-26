(** Native execution traces recorded in rings without calls to OCaml. *)

type t
type pcs = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array1.t
type sizes = (int32, Bigarray.int32_elt, Bigarray.c_layout) Bigarray.Array1.t

type modes =
  (int, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

type accesses = (int64, Bigarray.int64_elt, Bigarray.c_layout) Bigarray.Array2.t
(** the accesses, a row each: the index of the instruction, that made it, in all
    instructions, that the trace recorded, the address, the written value, the
    size, with the bit 32 set, if it is a write, the program counter of the
    instruction, in a trace of blocks, the bytes, that a write of at most 8
    bytes overwrote, the first one in the lowest byte, and the TID *)

val create : ?every:int -> ?blocks:bool -> ?accesses:int -> int -> t
(** [create size] the trace of the last [size] instructions, at least, as the
    ring has the size of a power of two, of every [every] one, by default of
    all, or of the first instructions of the blocks, with their sizes, if
    [blocks], and of the last [accesses] accesses to the memory, at least, by
    default of none. *)

val blocks : t -> bool
(** if it is a trace of blocks *)

val count : t -> int64
(** the number of the recorded instructions, or blocks, also of those, that the
    ring doesn't keep anymore *)

val retained : t -> int
(** the number of instruction or block records that the ring currently keeps *)

val accesses_count : t -> int64
(** the number of the recorded accesses *)

val clear : t -> unit

val pcs : ?last:int -> t -> pcs
(** the last program counters, at most [last], the oldest first, by default all,
    that the ring keeps *)

val tids : ?last:int -> t -> pcs
(** the TIDs of the last records, aligned with {!pcs} *)

val set_thread : t -> int -> unit
(** [set_thread trace tid] sets the TID of the records made by the next native
    run *)

val sizes : ?last:int -> t -> sizes
(** the sizes of the last blocks, as {!pcs} *)

val modes : ?last:int -> t -> modes
(** the modes of the last records, as {!pcs}, [1] for Thumb, on ARM, whose
    program counters have no lower bit, or else zeros *)

val accesses : ?last:int -> t -> accesses
(** the last accesses, as {!pcs} *)

val bounds : t -> pcs
(** the boundaries, the oldest first, each as four words: the index of the
    record, which follows the registers, if the bit 62 is set, or the memory, if
    the bit 63 is, which were written, while the emulation was stopped, except
    the pages, that were filled, as they were mapped; the program counter; the
    number of the written ranges of the bytes, see {!ranges}, or [-1], if they
    are unknown, e.g., too many; and the TID. If the bit 61 is set, a hook wrote
    them, while the emulation ran, before the instruction at the program
    counter, in the record. *)

val ranges : t -> pcs
(** the addresses and the sizes of the written ranges of the {!bounds}, in their
    order *)

val save : ?last:int -> t -> string -> int64
(** [save trace file] writes the last program counters, as {!pcs}, one in hex a
    line, and returns their number. *)

(** The records of the engines, that record the traces themselves, as the native
    hooks do, e.g., the lifted engine of [Bap_engine]. *)
module Record : sig
  val prepare : t -> bool -> unit
  (** [prepare trace arm] the trace records the modes, if [arm]. *)

  val record : t -> int64 -> int -> bool -> unit
  (** [record trace pc size thumb] records the instruction, of every [every]
      one, or the block, of [size] bytes, that starts at [pc], in the mode. *)

  val extend : t -> int -> unit
  (** [extend trace size] the last block runs the next instruction of [size]
      bytes. *)

  val access : t -> bool -> int64 -> int -> int64 -> int64 -> int64 -> unit
  (** [access trace write addr size value old pc] records the access of the
      instruction at [pc], the [old] bytes of a write, as {!accesses}. *)

  val unrun : t -> int64 -> unit
  (** [unrun trace pc] the instruction at [pc], that the trace recorded last,
      didn't run, e.g., as it faulted, so that it is recorded again, when it
      runs. *)

  val bound : t -> bool -> bool -> bool -> int64 -> int64 array -> bool -> unit
  (** [bound trace regs mem running pc ranges unknown] the boundary of the
      written registers and memory, whose addresses and sizes are the pairs of
      [ranges], or are [unknown], as {!bounds}, made while the emulation runs,
      before the instruction at [pc], if [running]. *)
end
