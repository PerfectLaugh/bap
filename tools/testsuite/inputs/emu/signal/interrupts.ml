#require "bap-primus-native.emu"

module Emu = Bap_emu

(* the signals, whose handler doesn't pause the program, stop Unicorn,
   which continues, as the handler runs *)
let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project file) in
  let handled = ref 0 in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> incr handled));
  ignore
    (Unix.setitimer Unix.ITIMER_REAL { it_interval = 0.001; it_value = 0.001 });
  let status = Emu.run emu in
  ignore (Unix.setitimer Unix.ITIMER_REAL { it_interval = 0.; it_value = 0. });
  Printf.printf "%s, the handler ran %s\n"
    (match status with Exited (Some 0) -> "exited" | _ -> "not exited")
    (if !handled >= 10 then "while it ran" else "after it ran")
