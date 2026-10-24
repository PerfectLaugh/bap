#require "bap-primus-native.emu"

module Emu = Bap_emu

(* the signal stops the loop of signal-loop.c, which runs in Unicorn
   without calls, and the script saves the checkpoint there *)
let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create (Bap_script.project file) in
  Sys.set_signal Sys.sigalrm (Sys.Signal_handle (fun _ -> Emu.stop emu));
  ignore (Unix.setitimer Unix.ITIMER_REAL { it_interval = 0.; it_value = 0.2 });
  (match Emu.run emu with
  | Paused ->
      let pc = Emu.pc emu in
      if pc >= 0x201440L && pc < 0x2014dbL then
        print_endline "paused in the loop"
      else Printf.printf "paused at %Lx\n%!" pc;
      Emu.save emu "signal.ckpt";
      print_endline "saved"
  | _ -> print_endline "not paused");
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | _ -> print_endline "not exited"
