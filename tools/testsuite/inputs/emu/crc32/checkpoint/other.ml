#require "bap-primus-native.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  match
    Emu.status (Emu.create ~restore:"crc.ckpt" (Bap_script.project ~disassemble:true file))
  with
  | Failed msg -> print_endline msg
  | _ -> print_endline "restored"
