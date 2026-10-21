#require "bap-primus-unicorn.emu"

module Emu = Bap_emu
module Sym = Emu.Symbolic

let () =
  let file, stdin =
    match Bap_script.args () with
    | [ file; stdin ] -> (file, stdin)
    | _ -> failwith "expected FILE INPUT"
  in
  let emu =
    Emu.create ~components:Sym.components
      ~redirects:[ ("<stdin>", stdin) ]
      (Bap_script.project file)
  in
  (match Emu.run emu ~until:0x80cL with
  | Paused -> ()
  | _ -> failwith "fgets didn't return");
  Sym.symbolize emu (Mem (Int64.sub (Emu.reg emu "RBP") 0x40L, 4));
  Emu.save emu "symbolic.ckpt";
  print_endline "saved"
