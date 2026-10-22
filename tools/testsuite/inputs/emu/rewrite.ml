#require "bap-primus-unicorn.emu"

open Core
module Emu = Bap_emu

(* the result of each call of the code at 0x405000, at its ret *)
let () =
  match Bap_script.args () with
  | [ rewrite ] ->
      let emu = Emu.create (Bap_script.project rewrite) in
      Emu.on_code emu ~first:0x405005L ~last:0x405005L (fun emu _ ->
          printf "returns %Ld\n%!" (Emu.reg emu "RAX"));
      ignore (Emu.run emu)
  | _ -> failwith "expected REWRITE"
