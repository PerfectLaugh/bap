open Bap.Std
module Context = Bap_primus_lisp_context
module Program = Bap_primus_lisp_program

type error

val program :
  ?paths:string list -> Project.t -> string list -> (Program.t, error) result

val with_features : ?paths:string list -> Project.t -> string list -> Project.t
val requested : Project.t -> string list * string list
val pp_error : Format.formatter -> error -> unit
val pp_program : Format.formatter -> Program.t -> unit
