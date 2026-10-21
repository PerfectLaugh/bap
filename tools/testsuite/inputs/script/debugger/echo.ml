#require "bap-primus, bap-frontend.script-debugger"

open Bap_primus.Std
module Debugger = Bap_script_debugger

let calls = ref 0

module Count (Machine : Primus.Machine.S) = struct
  let stopped _ =
    incr calls;
    Machine.return ()
end

let () =
  let system, file =
    match Bap_script.args () with
    | [ system; file ] -> (system, file)
    | _ -> failwith "expected SYSTEM FILE"
  in
  Debugger.break "print_endline";
  Debugger.on_stop (module Count);
  ignore
    (Bap_script.run ~system ~init:[ Debugger.component ]
       (Bap_script.project ~disassemble:true file));
  Printf.printf "print_endline was called %d times\n" !calls
