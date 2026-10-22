#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* the program pauses in a thread of threads.c, whose checkpoint isn't
   saved, as the checkpoints keep one thread, and continues *)
let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project file) in
  let worker = List.assoc "worker" (Emu.symbols emu) in
  (match Emu.run emu ~until:worker with
  | Paused -> (
      Printf.printf "paused in the thread %d\n%!" (Emu.thread emu);
      try Emu.save emu "threads.ckpt" with Failure msg -> print_endline msg)
  | _ -> print_endline "not paused");
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | _ -> print_endline "not exited"
