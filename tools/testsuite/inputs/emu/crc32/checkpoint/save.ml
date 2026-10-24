#require "bap-primus-native.emu"

module Emu = Bap_emu

let () =
  let file, stdin =
    match Bap_script.args () with
    | [ file; stdin ] -> (file, stdin)
    | _ -> failwith "expected FILE INPUT"
  in
  let emu =
    Emu.create ~redirects:[ ("<stdin>", stdin) ] (Bap_script.project ~disassemble:true file)
  in
  (match Emu.run emu ~until:0x7efL with
  | Paused -> ()
  | _ -> failwith "fgets didn't return");
  Printf.printf "buf1 %S\n%!"
    (Emu.read emu (Int64.sub (Emu.reg emu "RBP") 0x40L) 4);
  Emu.save emu "crc.ckpt";
  print_endline "saved"
