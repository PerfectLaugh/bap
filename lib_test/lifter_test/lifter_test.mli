(** Tests of the lifters.

    An instruction is lifted through the knowledge base, as the [bap mc] command
    does, so that the tested semantics is the semantics that the analyses see,
    the semantics of all lifters, including the Primus Lisp ones. The lifted BIL
    is type-checked and evaluated with {!Primus_bil}. *)

open Bap_core_theory
open Bap.Std

type mode
(** the target and the encoding of the tested instructions *)

val mode :
  ?typ:(string -> Type.t option) ->
  ?addr:int ->
  target:string ->
  encoding:string ->
  unit ->
  mode
(** [mode ~target ~encoding ()] are the instructions of the [target] in the
    [encoding], both are names in the [bap] package. The tested instructions are
    at [addr], [0x10000] by default.

    The type of a location is the type of the variable of the target with the
    same name, if there is one, otherwise it is [typ name], if [typ] returns it,
    and a word otherwise. *)

val target : mode -> Theory.Target.t

val lift : mode -> string -> bil
(** [lift mode code] is the BIL of the instruction with the encoding [code], the
    bytes in hex separated by spaces, at the address of the [mode]. *)

val case :
  mode ->
  string ->
  string ->
  ((string * string) list * (string * string) list) list ->
  OUnit2.test
(** [case mode asm code vectors] is the test of the instruction [asm] with the
    encoding [code] that is evaluated for each [(init, expect)] in [vectors].

    The [init] and [expect] lists bind locations to values given as hex or
    decimal numbers. A location is a register name, e.g., [RAX], a flag, e.g.,
    [CF], a memory word [M<n>@<addr>] of [n] bytes at [addr], or [PC], the
    destination of the jump, or the address of the next instruction if the
    instruction doesn't jump. The unbound registers and memory are initialized
    to zero.

    The instructions of each target are lifted in a knowledge base of their own,
    so the modes may put the instructions at the same addresses. *)

val vectors : string -> ((string * string) list * (string * string) list) list
(** [vectors s] parses the vectors in [s], one per line, as space-separated
    [name=value] bindings, the inputs and the outputs separated by [|]. *)
