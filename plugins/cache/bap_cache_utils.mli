open Core
open Regular.Std

val binable_from_file : (module Binable.S with type t = 't) -> string -> 't
val read_from_file : 'a Data.Read.t -> string -> 'a

val binable_to_file :
  ?temp_dir:string ->
  (module Binable.S with type t = 't) ->
  string ->
  't ->
  unit
(** [binable_to_file ?temp_dir b file data] - provides an atomic writing of
    [data] into [file] using [Binable] interface. The atomic property is hold if
    the provided [temp_dir] and [file] share the same filesystem. If [temp_dir]
    is not provided then parent directory for [file] is used instead. *)

val write_to_file : ?temp_dir:string -> 'a Data.Write.t -> string -> 'a -> unit
(** [write_to_file ?temp_dir writer file data] same as [binable_to_file] above,
    but writes using [Regular.Data.Write] interface *)
