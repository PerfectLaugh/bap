open Core
open Bap.Std

type t

val of_sub : sub term -> t Or_error.t
val of_blks : ?next:addr -> blk term list -> t Or_error.t
val of_range : sub term -> lo:addr -> hi:addr -> t Or_error.t
val entry : t -> blk term
val blks : t -> blk term list
val with_blks : t -> blk term list -> t
val update : sub term -> t -> sub term
