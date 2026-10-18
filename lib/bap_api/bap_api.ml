open Core
open Bap.Std

type filename = string
type api = string

module type S = sig
  type t

  val language : string
  val parse : (string -> string option) -> string list -> t Or_error.t
  val mapper : t -> Term.mapper
end

type t = (module S)

let registry = ref []
let process api = registry := api :: !registry
let processors () = !registry
let noreturn_readers = String.Table.create ()

let provide_noreturn ~language read =
  Hashtbl.set noreturn_readers ~key:language ~data:read

let noreturn_reader language = Hashtbl.find noreturn_readers language
