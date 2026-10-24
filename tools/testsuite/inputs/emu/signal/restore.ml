#require "bap-primus-native.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~restore:"signal.ckpt" (Bap_script.project file) in
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | _ -> print_endline "not exited"
