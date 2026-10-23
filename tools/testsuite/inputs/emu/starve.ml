#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* Creates the thread of starve.c, that spins on tick, at which the
   script pauses the program each time, much more often, than the time
   slice of the thread ends, and continues it, until it exits, so that
   main runs again, only if the pauses don't renew the slice. *)

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project file) in
  let addr name = List.assoc name (Emu.symbols emu) in
  (match Emu.run emu ~until:(addr "main") with
  | Paused -> ()
  | _ -> failwith "doesn't pause at main");
  ignore (Emu.spawn_thread emu ~start:(addr "spinner") ~arg:0L : int);
  let pauses = ref 0 in
  Emu.on_code emu ~first:(addr "tick") ~last:(addr "tick") (fun emu _ ->
      Emu.stop emu);
  let rec go () =
    match Emu.run emu with
    | Paused when !pauses < 1_000_000 ->
        incr pauses;
        go ()
    | Paused -> print_endline "starved"
    | Exited (Some 0) -> print_endline "exited"
    | _ -> print_endline "failed"
  in
  go ()
