open Bap.Std

type t

val top : int -> t
val constant : Word.t -> t
val value : t -> Word.t option
val sign_nonnegative : t -> bool
val sign_negative : t -> bool
val join_ranges : t -> t -> t
val eval : t Var.Map.t -> exp -> t
val simplify_sub : sub term -> sub term
