#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* the calls of main of smc-text.c, from the traces of the instructions,
   and of the blocks, which call f, g, print and putc *)
let () =
  let file = List.hd_exn (Bap_script.args ()) in
  List.iter
    [ (false, "instructions"); (true, "blocks") ]
    ~f:(fun (blocks, name) ->
      let emu = Emu.create (Bap_script.project file) in
      let trace = Emu.Trace.start ~blocks emu in
      ignore (Emu.run emu : Emu.status);
      let calls =
        Emu.Trace.calls trace
        |> List.filter ~f:(fun (c : Emu.Trace.call) ->
            Int64.(c.site >= 0x402100L))
      in
      printf "%s:%s\n" name
        (String.concat
           (List.map calls ~f:(fun c ->
                sprintf " %Lx->%s" c.site
                  (String.concat ~sep:","
                     (List.map c.targets ~f:(fun (target, n) ->
                          sprintf "%Lx(%d)" target n)))))))
