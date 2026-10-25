(* The states of the components, that the checkpoints of the machines
   keep, e.g., the channels of Primus Lisp, as the components save and
   restore them, see [Primus.Checkpoint] *)

open Core
open Bap_primus_types

module type S = functor (Machine : Machine) -> sig
  val save : string option Machine.t
  val restore : string -> unit Machine.t
end

type policy = { version : int; required : bool }
type entry = { extension : (module S); policy : policy }

let extensions : entry String.Table.t = String.Table.create ()

let register ?(package = "user") ?(version = 1) ?(required = false) name
    extension =
  if version <= 0 then
    invalid_argf "Primus.Checkpoint: invalid schema version %d" version ();
  let name = sprintf "%s:%s" package name in
  if Hashtbl.mem extensions name then
    invalid_argf "Primus.Checkpoint: %s is already registered" name ();
  Hashtbl.set extensions ~key:name
    ~data:{ extension; policy = { version; required } }

let find name =
  Option.map (Hashtbl.find extensions name) ~f:(fun e -> e.extension)

let policy name =
  Option.map (Hashtbl.find extensions name) ~f:(fun e -> e.policy)

let names () = Hashtbl.keys extensions |> List.sort ~compare:String.compare
