#require "bap-primus-unicorn.emu"

open Bap.Std
module Emu = Bap_emu

let word emu addr =
  let s = Emu.read emu addr 8 in
  let r = ref 0L in
  for i = 7 downto 0 do
    r := Int64.(logor (shift_left !r 8) (of_int (Char.code s.[i])))
  done;
  !r

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create
      ~args:[ "hello"; "cruel"; "world" ]
      (Bap_script.project ~bare:true file)
  in
  Printf.printf "paused at the entry %Lx\n%!" (Emu.pc emu);
  (match Emu.run emu ~until:0x40076bL with
  | Paused ->
      Printf.printf "paused at main %Lx, argc = %Ld\n%!" (Emu.pc emu)
        (Emu.reg emu "RDI")
  | _ -> failwith "main is not reached");
  let argv = Emu.reg emu "RSI" in
  let arg1 = word emu Int64.(add argv 8L) in
  Printf.printf "argv[1] = %s\n%!" (Emu.read emu arg1 5);
  Emu.write emu arg1 "HELLO";
  let stores = ref 0 in
  Emu.on_write emu (fun _ _ _ _ -> incr stores);
  Emu.on_call emu "putchar" (fun emu ->
      if Emu.arg emu 0 = Int64.of_int (Char.code 'l') then Return 108L
      else Default);
  match Emu.run emu with
  | Exited code ->
      Printf.printf "exited with %s after %d stores\n"
        (match code with Some c -> string_of_int c | None -> "?")
        !stores
  | Paused -> print_endline "paused"
  | Running -> print_endline "running"
  | Failed msg -> print_endline ("failed: " ^ msg)
