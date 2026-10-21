#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let status = function
  | Emu.Exited _ -> print_endline "exited"
  | Paused -> print_endline "paused"
  | Running -> print_endline "running"
  | Failed m -> print_endline ("failed: " ^ m)

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
  ignore (Emu.run emu ~until:0x40076bL);
  (* mov $0xa, %edi, which prints the newline, prints + instead *)
  Emu.patch emu 0x400727L "\xbf\x2b";
  let snapshot = Emu.snapshot emu in
  status (Emu.run emu);
  Emu.restore emu snapshot;
  status (Emu.run emu)
