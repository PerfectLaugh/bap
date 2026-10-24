#require "bap-primus-native.emu"

module Emu = Bap_emu

(* Creates two threads at the entry of main of spawn.c, which call
   worker with 1 and 2, and return, while main waits for them, with
   api=DIR, the api of the target, e.g., of PowerPC. *)

let api, file =
  List.partition
    (fun arg -> String.starts_with ~prefix:"api=" arg)
    (Bap_script.args ())

let () =
  let api = List.map (fun a -> String.sub a 4 (String.length a - 4)) api in
  let emu = Emu.create (Bap_script.project ~api (List.hd file)) in
  let addr name = List.assoc name (Emu.symbols emu) in
  (match Emu.run emu ~until:(addr "main") with
  | Paused -> ()
  | _ -> failwith "doesn't pause at main");
  let worker = addr "worker" in
  let first = Emu.spawn_thread emu ~start:worker ~arg:1L in
  let second = Emu.spawn_thread emu ~start:worker ~arg:2L in
  Printf.printf "spawned %d and %d\n%!" first second;
  List.iter
    (fun ({ tid; pc; waiting } : Emu.Checkpoint.thread) ->
      Printf.printf "thread %d at %s%s\n" tid
        (if Int64.equal (Int64.logand pc (-2L)) (addr "main") then "main"
         else if Int64.equal (Int64.logand pc (-2L)) worker then "worker"
         else Printf.sprintf "%Lx" pc)
        (if Option.is_some waiting then ", waiting" else ""))
    (Emu.threads emu);
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | Failed msg -> print_endline ("failed: " ^ msg)
  | _ -> print_endline "not exited"
