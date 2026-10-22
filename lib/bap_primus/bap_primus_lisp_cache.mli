(** The cache of the Lisp programs, see the implementation. *)

open Core

val variable : string
(** [variable] the variable of the folder, that the processes share. *)

val load :
  (module Binable.S with type t = 'a) -> kind:string -> string list -> 'a option
(** [load (module T) ~kind parts] the entry of the [kind] by the [parts] of its
    key, if it is cached. *)

val store :
  (module Binable.S with type t = 'a) ->
  kind:string ->
  string list ->
  'a ->
  unit
(** [store (module T) ~kind parts x] caches [x], if there is a cache. *)
