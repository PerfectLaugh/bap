(** Evaluates BIL programs using the Primus interpreter.

    Primus evaluates expressions and IR terms, so this module adds the BIL
    statements on top of it. All free variables that are read before they are
    written evaluate to zero and all memories are fully mapped and
    zero-initialized. *)

open Bap_core_theory
open Bap.Std

type t
(** the state of the machine after the evaluation *)

val eval : ?target:Theory.Target.t -> bil -> t
(** [eval bil] evaluates [bil] in a fresh machine.

    The evaluation follows the jumps semantics of the old BIL interpreter, i.e.,
    a jump only records the destination and the evaluation continues with the
    next statement. Fails if the evaluation terminates with an exception. *)

val lookup : t -> var -> word option
(** [lookup s v] is the value of [v] if it was assigned. *)

val pc : t -> word option
(** [pc s] the destination of the last jump, if there was one. *)
