#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~restore:"crc.ckpt" (Bap_script.project ~disassemble:true file) in
  match Emu.run emu ~until:0x80cL with
  | Paused ->
      Printf.printf "buf2 %S\n%!"
        (Emu.read emu (Int64.sub (Emu.reg emu "RBP") 0x30L) 4)
  | _ -> print_endline "fgets didn't return"
