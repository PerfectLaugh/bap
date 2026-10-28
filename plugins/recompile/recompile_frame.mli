open Bap.Std
open Bap_core_theory

type t
type state

module Var_state : sig
  val empty : state
end

val analyze : target:Theory.Target.t -> sub term -> (t, string) result
val entry : t -> tid -> state
val step : t -> state -> def term -> state
val slot : t -> state -> exp -> int -> int option
val slots : t -> (int * int) list
val stack_pointer : t -> var
val pointer_width : t -> int
val big_endian : t -> bool
