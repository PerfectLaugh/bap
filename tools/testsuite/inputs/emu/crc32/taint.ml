#require "bap-primus-native.emu"

module Emu = Bap_emu

let () =
  let file, stdin =
    match Bap_script.args () with
    | [ file; stdin ] -> (file, stdin)
    | _ -> failwith "expected FILE INPUT"
  in
  let emu =
    Emu.create ~components:Emu.Taint.components
      ~redirects:[ ("<stdin>", stdin) ]
      (Bap_script.project ~disassemble:true file)
  in
  (match Emu.run emu ~until:0x80cL with
  | Paused -> ()
  | _ -> failwith "fgets didn't return");
  let rbp = Emu.reg emu "RBP" in
  Emu.Taint.introduce emu ~kind:"input" (Mem (Int64.sub rbp 0x40L, 16));
  Emu.Taint.introduce emu ~kind:"input" (Mem (Int64.sub rbp 0x30L, 16));
  Printf.printf "buf1 %s, RAX %s\n%!"
    (String.concat "," (Emu.Taint.kinds emu (Mem (Int64.sub rbp 0x40L, 4))))
    (String.concat "," (Emu.Taint.kinds emu (Reg "RAX")));
  let jumps = ref [] in
  Emu.Taint.on_jump emu (fun _ ~kinds dst -> jumps := (dst, kinds) :: !jumps);
  ignore (Emu.run emu);
  Printf.printf "jumps:";
  List.iter
    (fun (dst, kinds) -> Printf.printf " %Lx:%s" dst (String.concat "," kinds))
    (List.rev !jumps);
  print_newline ()
