(** Encodings for synthetic AArch64 stubs. *)

val b : pc:int64 -> int64 -> int32
(** [b ~pc target] is the word of an unconditional branch from the instruction
    at [pc] to [target]. Raises [Invalid_argument] if [pc] or the displacement
    is not four-byte aligned, or if the displacement is outside the signed
    28-bit byte range from -128MiB inclusive to 128MiB exclusive. *)

val ret : int32
(** the word of [ret], which returns to the address in [X30]. *)

val bytes : int32 -> string
(** [bytes word] is the four-byte little-endian encoding of [word]. *)
