(** Helpers for the tests of the ARM lifters, see {!Lifter_test}. *)

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
    the little-endian encoding [code] at {!addr}, see {!Lifter_test.case} for
    the locations and the values. Besides the variables of the target, the
    locations include the AArch64 vector registers [V<n>] and the intrinsic
    arguments [intrinsic:x<n>]. *)

val lift : mode -> string -> bil
(** [lift mode code] is the BIL of the instruction [code] at {!addr}. *)
