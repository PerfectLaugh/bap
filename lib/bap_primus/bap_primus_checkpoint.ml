(* The states of the components, that the checkpoints of the machines
   keep, e.g., the channels of Primus Lisp, as the components save and
   restore them, see [Primus.Checkpoint] *)

open Core
open Bap_primus_types

module type S = functor (Machine : Machine) -> sig
  val save : string option Machine.t
  val restore : string -> unit Machine.t
end

let extensions : (module S) String.Table.t = String.Table.create ()

let register ?(package = "user") name ext =
  let name = sprintf "%s:%s" package name in
  if Hashtbl.mem extensions name then
    invalid_argf "Primus.Checkpoint: %s is already registered" name ();
  Hashtbl.set extensions ~key:name ~data:ext

let find = Hashtbl.find extensions
let names () = Hashtbl.keys extensions |> List.sort ~compare:String.compare
