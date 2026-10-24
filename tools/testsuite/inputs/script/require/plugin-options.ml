#require "bap-primus-native.emu"

(* the library uses the library of the primus-lisp plugin, whose options
   are still its own, e.g., the redirection of the standard input *)
let () =
  let file = List.hd (Bap_script.args ()) in
  ignore
    (Bap_script.run ~system:"bap:stubbed-executor"
       (Bap_script.project ~disassemble:true file))
