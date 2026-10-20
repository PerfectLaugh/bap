(** The binary program, and the code, that it changes or writes, which runs, as
    it is in the memory, see [Primus.Lift]. *)

open Bap_primus_types

module LinkBinaryProgram (Machine : Machine) : sig
  val init : unit -> unit Machine.t
end
