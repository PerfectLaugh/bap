#require "bap-primus-native.emu"

module Emu = Bap_emu

let word emu addr =
  let s = Emu.read emu addr 8 in
  let r = ref 0L in
  for i = 7 downto 0 do
    r := Int64.(logor (shift_left !r 8) (of_int (Char.code s.[i])))
  done;
  !r

let show name emu = function
  | Emu.Paused -> Printf.printf "%s paused at %Lx\n%!" name (Emu.pc emu)
  | Exited c ->
      Printf.printf "%s exited %s\n%!" name
        (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "%s failed %s\n%!" name m
  | Running -> Printf.printf "%s running\n%!" name

let () =
  let echo, crc =
    match Bap_script.args () with
    | [ echo; crc ] -> (echo, crc)
    | _ -> failwith "expected ECHO CRC"
  in
  let a = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
  let b = Emu.create ~args:[ "hi" ] (Bap_script.project crc) in
  let c =
    Emu.create ~args:[ "world"; "again" ] (Bap_script.project echo)
  in
  show "a" a (Emu.run a ~until:0x40076bL);
  show "c" c (Emu.run c ~until:0x40076bL);
  Printf.printf "argc: a %Ld, c %Ld\n%!" (Emu.reg a "RDI") (Emu.reg c "RDI");
  Emu.write a (word a Int64.(add (Emu.reg a "RSI") 8L)) "HELLO";
  Emu.add_symbol a "only_a" 0x400733L;
  Printf.printf "names: a %b, c %b\n%!"
    (List.mem_assoc "only_a" (Emu.symbols a))
    (List.mem_assoc "only_a" (Emu.symbols c));
  (try Emu.restore c (Emu.snapshot a)
   with Invalid_argument _ -> print_endline "the snapshot of a is not of c");
  let calls_a = ref 0 and calls_c = ref 0 in
  Emu.on_call a "print_endline" (fun _ ->
      incr calls_a;
      Default);
  Emu.on_call c "print_endline" (fun _ ->
      incr calls_c;
      Default);
  let pcs = ref [] in
  for _ = 1 to 3 do
    ignore (Emu.step a);
    ignore (Emu.step b);
    ignore (Emu.step c);
    pcs := Printf.sprintf "%Lx/%Lx/%Lx" (Emu.pc a) (Emu.pc b) (Emu.pc c) :: !pcs
  done;
  Printf.printf "steps: %s\n%!" (String.concat " " (List.rev !pcs));
  print_endline "== b";
  show "b" b (Emu.run b);
  print_endline "== c";
  show "c" c (Emu.run c);
  print_endline "== a";
  show "a" a (Emu.run a);
  Printf.printf "print_endline: a %d, c %d\n" !calls_a !calls_c;
  Printf.printf "knowledge: a %b, b %b\n"
    (Option.is_some (Emu.knowledge a))
    (Option.is_some (Emu.knowledge b))
