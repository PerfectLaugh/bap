#require "bap-primus-unicorn.emu"

module Emu = Bap_emu
module Sym = Emu.Symbolic

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create ~components:Sym.components ~restore:"symbolic.ckpt"
      (Bap_script.project ~disassemble:true file)
  in
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
