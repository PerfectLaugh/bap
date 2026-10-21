#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let disassemble = Sys.getenv_opt "DISASSEMBLE" = Some "1" in
  let emu = Emu.create ~args:[ "hi" ] (Bap_script.project ~disassemble file) in
  let pcs =
    List.init 3 (fun _ ->
        ignore (Emu.step emu);
        Printf.sprintf "%Lx" (Emu.pc emu))
  in
  Printf.printf "steps: %s\n%!" (String.concat " " pcs);
  match Emu.run emu with
  | Exited c ->
      Printf.printf "exited %s\n"
        (match c with Some c -> string_of_int c | None -> "?")
  | Paused -> print_endline "paused"
  | Running -> print_endline "running"
  | Failed m -> print_endline ("failed: " ^ m)
