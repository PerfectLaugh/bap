(** Helpers for the tests of the ARM lifters.

    An instruction is lifted through the knowledge base, as the [bap mc] command
    does, so the semantics is the one that the analyses see: the semantics of
    all lifters, including the Primus Lisp ones. The lifted BIL is evaluated
    with {!Primus_bil}. *)

open Bap.Std

type mode =
  | A64  (** AArch64 *)
  | A32  (** AArch32, the ARM encoding *)
  | T32  (** AArch32, the Thumb encoding *)

val addr : int
(** the address of the tested instruction *)

val case :
  mode ->
  string ->
  string ->
  init:(string * string) list ->
  expect:(string * string) list ->
  OUnit2.test
(** [case mode asm code ~init ~expect] is the test of the instruction [asm] with
    the little-endian encoding [code] (bytes in hex separated by spaces) at
    {!addr}.

    The [init] and [expect] lists bind locations to values given as hex or
    decimal numbers. A location is a register name of the base register, e.g.,
    [R0] or [V0] for AArch64, [R0] or [D0] for AArch32, a flag, e.g., [NF], a
    memory word [M<n>@<addr>] of [n] bytes at [addr], or [PC], the destination
    of the jump. The unbound registers and memory are initialized to zero. *)

val lift : mode -> string -> bil
(** [lift mode code] is the BIL of the instruction [code] at {!addr}. *)
