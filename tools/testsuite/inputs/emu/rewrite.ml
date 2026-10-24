#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* the result of each call of the code at 0x405000, at its ret, and of
   the program *)
let () =
  match Bap_script.args () with
  | [ rewrite ] ->
      let emu = Emu.create (Bap_script.project rewrite) in
      Emu.on_code emu ~first:0x405005L ~last:0x405005L (fun emu _ ->
          printf "returns %Ld\n%!" (Emu.reg emu "RAX"));
      ignore (Emu.run emu);
      (* the result of main, which runs in Unicorn, is the exit code *)
      printf "exited %s\n"
        (Option.value_map (Emu.exit_code emu) ~default:"none" ~f:Int.to_string)
  | _ -> failwith "expected REWRITE"
