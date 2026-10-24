#require "bap-primus-native.emu"

module Emu = Bap_emu

let word emu addr =
  let s = Emu.read emu addr 8 in
  let r = ref 0L in
  for i = 7 downto 0 do
    r := Int64.(logor (shift_left !r 8) (of_int (Char.code s.[i])))
  done;
  !r

let show emu = function
  | Emu.Paused -> Printf.printf "paused at %Lx\n%!" (Emu.pc emu)
  | Exited c ->
      Printf.printf "exited %s\n%!"
        (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "failed %s\n%!" m

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
  show emu (Emu.run emu ~until:0x40076bL);
  let snap = Emu.snapshot emu in
  let arg1 () = word emu Int64.(add (Emu.reg emu "RSI") 8L) in
  Printf.printf "snapshot at %Lx, RDI = %Ld, argv[1] = %s\n%!" (Emu.pc emu)
    (Emu.reg emu "RDI")
    (Emu.read emu (arg1 ()) 5);
  print_endline "== first run";
  show emu (Emu.run emu);
  Emu.restore emu snap;
  Printf.printf "restored at %Lx, RDI = %Ld, argv[1] = %s\n%!" (Emu.pc emu)
    (Emu.reg emu "RDI")
    (Emu.read emu (arg1 ()) 5);
  Emu.write emu (arg1 ()) "WORLD";
  Emu.set_reg emu "RDI" 2L;
  print_endline "== second run, argv[1] = WORLD, argc = 2";
  show emu (Emu.run emu);
  Emu.restore emu snap;
  Printf.printf "restored again, RDI = %Ld, argv[1] = %s\n%!"
    (Emu.reg emu "RDI")
    (Emu.read emu (arg1 ()) 5);
  print_endline "== third run";
  show emu (Emu.run emu ~until:0x400733L);
  show emu (Emu.run emu)
