open Bap_primus_types

module type S = functor (Machine : Machine) -> sig
  val save : string option Machine.t
  val restore : string -> unit Machine.t
end

type policy = { version : int; required : bool }

val register :
  ?package:string ->
  ?version:int ->
  ?required:bool ->
  string ->
  (module S) ->
  unit

val find : string -> (module S) option
val policy : string -> policy option
val names : unit -> string list
