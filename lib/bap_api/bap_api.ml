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

(* the folders of the api files of the project, besides those of the
   options *)
module Paths = struct
  type t = string list [@@deriving bin_io, compare, sexp]

  let pp ppf paths = Format.pp_print_string ppf (String.concat ~sep:":" paths)
end

let project_paths =
  Value.Tag.register
    (module Paths)
    ~uuid:"2f6c1e43-7d6b-4b9e-9a51-3c0e8d4f7a62" ~name:"api-paths"

let paths proj = Option.value (Project.get proj project_paths) ~default:[]
let with_paths proj ps = Project.set proj project_paths (paths proj @ ps)
