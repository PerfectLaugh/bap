open Bap.Std
open Bap_primus_types

val marked : addr Bap_primus_observation.t

module Make (Machine : Machine) : sig
  val track : value -> unit Machine.t
  val untrack : value -> unit Machine.t
  val is_tracked : value -> bool Machine.t
  val mark : addr -> unit Machine.t
  val unmark : addr -> unit Machine.t
  val is_marked : addr -> bool Machine.t
  val page_marked : addr -> bool Machine.t
  val stored : addr -> value -> unit Machine.t
  val active : bool Machine.t
  val has_marks : bool Machine.t
  val version : int Machine.t
  val cover : 'a Bap_primus_observation.t -> unit Machine.t
  val uncovered : 'a Bap_primus_observation.t -> bool Machine.t
end
