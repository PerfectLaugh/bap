#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* pthreads.c, whose functions of the threads the executor runs, in the
   engine of the argument, prints its lines, and ok, if the threads of
   pthread_create, and of clone, are the same to them. *)

let () =
  match Bap_script.args () with
  | [ file; engine ] -> (
      let engine =
        if String.equal engine "unicorn" then `Unicorn else `Lifted
      in
      let emu = Emu.create ~engine (Bap_script.project file) in
      match Emu.run emu with
      | Exited (Some 0) -> print_endline "exited 0"
      | Failed msg -> printf "failed: %s\n" msg
      | _ -> print_endline "didn't exit 0")
  | _ -> failwith "expected FILE ENGINE"
