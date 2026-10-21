#require "bap-primus"

open Bap.Std
open Bap_primus.Std

module Watch (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Env = Primus.Env.Make (Machine)
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let stopped _ =
    Env.get (Var.create "RAX" (Type.imm 64)) >>| fun x ->
    Printf.printf "RAX = %s\n%!" (Word.string_of_value (Primus.Value.to_word x))

  (* the stops, but not every address, see [stop_reached] *)
  let init () =
    Stops.add (Addr.of_int64 ~width:64 0x4004c0L) >>= fun () ->
    Primus.Interpreter.stop_reached >>> stopped
end

let () =
  let file = List.hd (Bap_script.args ()) in
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor"
       ~init:[ (module Watch) ]
       (Bap_script.project file))
