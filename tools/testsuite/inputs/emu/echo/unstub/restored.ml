#require "bap-primus-native.emu"

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
  let emu = Emu.create ~restore:"echo.ckpt" (project file) in
  print_endline "== restored";
  show emu (Emu.run emu)
