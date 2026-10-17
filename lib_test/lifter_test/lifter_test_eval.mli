(** A direct evaluator of the BIL of an instruction, with the semantics of
    {!Primus_bil}, which is much faster than a Primus machine. *)

open Bap.Std

type t
(** the state after the evaluation *)

val eval : bil -> t
(** [eval bil] evaluates [bil], the unassigned variables and memory are zero.

    A jump only records the destination and the evaluation continues with the
    next statement, a goto continues at the label of the instruction. *)

val lookup : t -> var -> word option
(** [lookup s v] is the value of [v], which is zero if it was not assigned. *)

val pc : t -> word option
(** [pc s] the destination of the last jump, if there was one. *)
