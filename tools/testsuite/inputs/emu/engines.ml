#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* the traces of the program, of the instructions and of the blocks, with
   the accesses, in Unicorn and in the lifted engine, which record the
   same instructions and accesses, while the blocks may end elsewhere *)
let () =
  let file = List.hd_exn (Bap_script.args ()) in
  let run engine blocks =
    let emu = Emu.create ~engine ~args:[ "hi" ] (Bap_script.project file) in
    let trace =
      Emu.Trace.start ~size:(1 lsl 16) ~blocks ~accesses:4096 ~read_values:true
        emu
    in
    ignore (Emu.run emu);
    (Emu.Trace.insns trace, Emu.Trace.accesses trace)
  in
  List.iter [ false; true ] ~f:(fun blocks ->
      let insns, accesses = run `Unicorn blocks in
      let insns', accesses' = run `Lifted blocks in
      let key (a : Emu.Trace.access) =
        ( a.addr,
          a.size,
          a.write,
          a.value,
          a.read_value,
          if blocks then a.pc else 0L )
      in
      let valid (a : Emu.Trace.access) =
        if a.write || a.size < 1 || a.size > 8 then Option.is_none a.read_value
        else Option.is_some a.read_value
      in
      printf
        "blocks %b: the instructions are the same %b, the accesses %b, read \
         values %b\n"
        blocks (Poly.equal insns insns')
        (Poly.equal (List.map accesses ~f:key) (List.map accesses' ~f:key))
        (List.for_all accesses ~f:valid && List.for_all accesses' ~f:valid))
