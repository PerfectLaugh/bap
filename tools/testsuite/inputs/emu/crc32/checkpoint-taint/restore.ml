#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create ~components:Emu.Taint.components ~restore:"taint.ckpt"
      (Bap_script.project ~disassemble:true file)
  in
  let rbp = Emu.reg emu "RBP" in
  Printf.printf "buf1 %s\n%!"
    (String.concat "," (Emu.Taint.kinds emu (Mem (Int64.sub rbp 0x40L, 4))));
  let jumps = ref [] in
  Emu.Taint.on_jump emu (fun _ ~kinds dst -> jumps := (dst, kinds) :: !jumps);
  ignore (Emu.run emu);
  Printf.printf "jumps:";
  List.iter
    (fun (dst, kinds) -> Printf.printf " %Lx:%s" dst (String.concat "," kinds))
    (List.rev !jumps);
  print_newline ()
