open Bap.Std

type t

val create : sub term -> t
val representative : t -> var -> var
