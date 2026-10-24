#require "bap-primus-native.emu"

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
    Emu.create ~args:[ "hello"; "cruel" ] (Bap_script.project file)
  in
  ignore (Emu.run emu ~until:0x40076bL);
  Emu.write emu (word emu Int64.(add (Emu.reg emu "RSI") 8L)) "HELLO";
  let say = List.assoc "print_endline" (Emu.symbols emu) in
  Emu.add_symbol emu "say" say;
  Emu.save emu "echo.ckpt";
  Printf.printf "saved at %Lx, say at %Lx\n%!" (Emu.pc emu) say;
  (try Emu.save emu "missing/echo.ckpt"
   with Failure _ -> print_endline "can't save");
  match Emu.run emu with
  | Exited c ->
      Printf.printf "exited %s\n"
        (match c with Some c -> string_of_int c | None -> "?")
  | _ -> print_endline "not exited"
