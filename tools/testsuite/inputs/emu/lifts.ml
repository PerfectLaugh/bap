#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The instructions, that the lifted engine lifts, are saved to the
   cache of bap, see BAP_CACHE_DIR, by Emu.save_lifts, and when a
   signal terminates the run: the first run saves them, the second
   starts without them, as the script removed them, and is terminated
   by SIGTERM, after which they are saved again, see the exit code 143. *)
let lifts () =
  let dir =
    Stdlib.Filename.concat (Sys.getenv_exn "BAP_CACHE_DIR") "lifted/lifts"
  in
  match Stdlib.Sys.readdir dir with
  | files -> List.map (Array.to_list files) ~f:(Stdlib.Filename.concat dir)
  | exception Sys_error _ -> []

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  let run () =
    let emu = Emu.create ~engine:`Lifted (Bap_script.project file) in
    ignore (Emu.run emu : Emu.status);
    emu
  in
  let emu = run () in
  printf "before saving: %d\n%!" (List.length (lifts ()));
  Emu.save_lifts emu;
  printf "after saving: %d\n%!" (List.length (lifts ()));
  List.iter (lifts ()) ~f:Stdlib.Sys.remove;
  ignore (run ());
  printf "before the signal: %d\n%!" (List.length (lifts ()));
  Caml_unix.kill (Caml_unix.getpid ()) Stdlib.Sys.sigterm
