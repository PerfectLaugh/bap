#require "bap-primus, bap-frontend.script-debugger"

open Bap_primus.Std
module Debugger = Bap_script_debugger

let stops = ref 0

module Step_on (Machine : Primus.Machine.S) = struct
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let init () = Stops.set_stepping true
end

module Step_off (Machine : Primus.Machine.S) = struct
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let stopped _ =
    incr stops;
    if !stops = 3 then Stops.set_stepping false else Machine.return ()
end

let () =
  Debugger.on_stop (module Step_off);
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor"
       ~init:[ Debugger.component; (module Step_on) ]
       (Bap_script.project (List.hd (Bap_script.args ()))));
  Printf.printf "stopped %d times\n" !stops
