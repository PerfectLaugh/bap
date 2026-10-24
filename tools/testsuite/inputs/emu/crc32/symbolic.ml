#require "bap-primus-native.emu"

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
      (Bap_script.project ~disassemble:true file)
  in
  (match Emu.run emu ~until:0x80cL with
  | Paused -> ()
  | _ -> failwith "fgets didn't return");
  let buf1 = Int64.sub (Emu.reg emu "RBP") 0x40L in
  Sym.symbolize emu (Mem (buf1, 4));
  let branches = ref [] in
  Sym.on_branch emu (fun _ b -> branches := b :: !branches);
  ignore (Emu.run emu);
  Printf.printf "branches:";
  List.iter (fun b -> Printf.printf " %Lx" (Sym.addr b)) (List.rev !branches);
  print_newline ();
  match Sym.flip ~timeout:10_000 (List.hd !branches) with
  | None -> print_endline "no collision"
  | Some m ->
      print_string "collision: ";
      List.iter (fun (_, v) -> print_char (Char.chr (Int64.to_int v))) m;
      print_newline ()
