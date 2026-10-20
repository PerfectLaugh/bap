open Bap_primus_types

module type S = functor (Machine : Machine) -> sig
  val save : string option Machine.t
  val restore : string -> unit Machine.t
end

val register : ?package:string -> string -> (module S) -> unit
val find : string -> (module S) option
val names : unit -> string list
