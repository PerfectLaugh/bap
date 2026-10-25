#require "bap-primus-native.emu"

module Emu = Bap_emu

let run name engine interpret file =
  let emu = Emu.create ~engine (Bap_script.project ~disassemble:true file) in
  let pc = Emu.pc emu in
  Emu.write emu pc "\x73\x50\xa1\x00\x73\x25\xa0\x00";
  Emu.set_reg emu "FCSR" 0L;
  Emu.set_pc emu pc;
  let step () =
    match if interpret then Emu.interpret emu else Emu.step emu with
    | Emu.Paused -> ()
    | Emu.Running -> failwith (name ^ " is running")
    | Emu.Exited _ -> failwith (name ^ " exited")
    | Emu.Failed message -> failwith (name ^ ": " ^ message)
  in
  step ();
  step ();
  let result = Emu.reg emu "X10" in
  if result <> 2L then
    failwith (Printf.sprintf "%s read vxrm = %Ld" name result);
  if Emu.reg emu "FCSR" <> 0L then failwith (name ^ " changed FCSR");
  Printf.printf "%s: vxrm write/read passed\n" name

let () =
  match Bap_script.args () with
  | [ file ] ->
      run "primus" `Unicorn true file;
      run "lifted" `Lifted false file
  | _ -> failwith "usage: riscv_vxrm.ml PROGRAM"
