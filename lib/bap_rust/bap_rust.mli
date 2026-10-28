(** Native Rust OGRE implementation. *)

module Ogre : sig
  val normalize : string -> (string, string) result
  val merge : string -> string -> (string, string) result
  val yaml : string -> (string, string) result
  val json : string -> (string, string) result
end
