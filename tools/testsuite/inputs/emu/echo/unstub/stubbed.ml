#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let show emu = function
  | Emu.Paused -> Printf.printf "paused at %Lx\n%!" (Emu.pc emu)
  | Exited c ->
      Printf.printf "exited %s\n%!"
        (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "failed %s\n%!" m
  | Running -> print_endline "running"

(* the arguments are the program, and the directory of quiet.lisp *)
let file, lisp =
  match Bap_script.args () with
  | [ file; lisp ] -> (file, lisp)
  | _ -> failwith "expected FILE LISP"

let project file =
  Bap_script.project
    ~lisp:{ Bap_script.paths = [ lisp ]; features = [ "quiet" ] }
    file

let () =
  let emu = Emu.create ~args:[ "hello" ] (project file) in
  show emu (Emu.run emu ~until:0x40076bL);
  let snap = Emu.snapshot emu in
  print_endline "== stubbed";
  show emu (Emu.run emu);
  Emu.restore emu snap;
  (try Emu.unstub emu "putchar"
   with Invalid_argument _ -> print_endline "putchar is external");
  Emu.unstub emu "print_endline";
  (* mov $0xa, %edi, which prints the newline, prints + instead *)
  Emu.write emu 0x400727L "\xbf\x2b";
  Emu.save emu "echo.ckpt";
  print_endline "== unstubbed";
  show emu (Emu.run emu)
