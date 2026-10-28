open Bap.Std
open Bap_core_theory

type t = {
  sub : sub term;
  frame : Bap_recompile.Frame.t option;
  frame_error : string option;
}

val normalize : target:Theory.Target.t -> sub term -> t
val successors : sub term -> blk term -> tid list
val live_out : sub term -> Var.Set.t Tid.Map.t -> blk term -> Var.Set.t
val live_in : sub term -> blk term -> Var.Set.t
val copies : sub term -> tid -> tid -> (var * exp) list
val pure : exp -> bool
