#require "bap-primus-native.emu"

module Emu = Bap_emu

(* bap script script.ml ENGINE PROGRAM: counts the reads and the writes,
   that the hooks of the memory see, which are the same in Unicorn and in
   the lifted engine, whose blocks run compiled, also with the hooks, and
   whose reads, that fault, e.g., of a page, that the executor maps then,
   the hooks see once *)
let () =
  match Bap_script.args () with
  | [ engine; file ] ->
      let engine = if engine = "lifted" then `Lifted else `Unicorn in
      let emu =
        Emu.create ~engine (Bap_script.project ~disassemble:true file)
      in
      let reads = ref 0 and writes = ref 0 in
      Emu.on_read emu (fun _ _ _ -> incr reads);
      Emu.on_write emu (fun _ _ _ _ -> incr writes);
      ignore (Emu.run emu);
      Printf.printf "reads %d writes %d\n" !reads !writes
  | _ -> failwith "usage: script.ml ENGINE PROGRAM"
