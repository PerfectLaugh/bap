#require "bap-primus-native.emu"

module Emu = Bap_emu

(* the pauses of the program, until it exits *)
let rec pauses emu run acc =
  match run emu with
  | Emu.Paused when List.length acc < 32 -> pauses emu run (Emu.pc emu :: acc)
  | Paused -> print_endline "doesn't exit"
  | Exited _ ->
      Printf.printf "paused at %s, exited\n%!"
        (String.concat " " (List.rev_map (Printf.sprintf "%Lx") acc))
  | Failed m -> Printf.printf "failed %s\n%!" m
  | Running -> print_endline "runs"

let () =
  let file = List.hd (Bap_script.args ()) in
  let create () =
    Emu.create ~args:[ "hello"; "cruel" ] (Bap_script.project file)
  in
  (* the hook stops the program at each iteration of the loop of main,
     which calls the stubs, and not again, when it continues from there *)
  let emu = create () in
  Emu.on_code emu ~first:0x40080bL ~last:0x40080bL (fun emu _ -> Emu.stop emu);
  pauses emu (fun emu -> Emu.run emu) [];
  (* the program stops at each iteration of the loop of print_strings,
     which calls print_endline *)
  let emu = create () in
  pauses emu (fun emu -> Emu.run emu ~until:0x400749L) []
