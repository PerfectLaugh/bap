#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let create ~engine file = Emu.create ~engine (Bap_script.project file)

let stats file =
  let emu = create ~engine:`Lifted file in
  let reports = ref 0 in
  let valid = ref true in
  let last = ref None in
  let subscription =
    Emu.start_stats emu ~interval:0.1 (fun stats ->
        incr reports;
        last := Some stats;
        valid :=
          !valid
          && Int64.(stats.instructions > 0L)
          && stats.lifted_blocks > 0 && stats.active_threads = 1
          && stats.hook_dispatches >= 0 && Option.is_some stats.rss
          && Int64.(stats.last_pc <> 0L))
  in
  ignore (Emu.run emu : Emu.status);
  Emu.stop_stats subscription;
  printf "stats: reports %b, valid %b, captured %b\n" (!reports > 0) !valid
    (Option.exists !last ~f:(fun stats -> Int64.(stats.instructions > 0L)))

let deadline file =
  let emu = create ~engine:`Unicorn file in
  ignore (Emu.start_deadline ~code:124 0.05);
  ignore (Emu.run emu : Emu.status)

let cancel file =
  let deadline = Emu.start_deadline ~code:124 0.02 in
  Emu.cancel_deadline deadline;
  Caml_unix.sleepf 0.05;
  print_endline "deadline cancelled";
  (match Emu.start_deadline (-1.) with
  | exception Invalid_argument _ -> print_endline "negative deadline rejected"
  | _ -> print_endline "negative deadline accepted");
  let emu = create ~engine:`Lifted file in
  match Emu.start_stats emu ~interval:0. (fun _ -> ()) with
  | exception Invalid_argument _ -> print_endline "invalid stats rejected"
  | _ -> print_endline "invalid stats accepted"

let () =
  match Bap_script.args () with
  | [ "stats"; file ] -> stats file
  | [ "deadline"; file ] -> deadline file
  | [ "cancel"; file ] -> cancel file
  | _ -> failwith "expected stats FILE, deadline FILE, or cancel FILE"
