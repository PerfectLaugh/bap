#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* the trace of the blocks of taint-bss.c, which watches buf, from
   403040 to 40313f, records its 512 reads only, after the CRC of a
   million bytes, whose accesses aren't recorded, with the instructions,
   that read it, in either engine, and the block, that runs most, and
   the byte, that is accessed most, the first one of buf, as all are
   read twice *)
let () =
  let file = List.hd_exn (Bap_script.args ()) in
  List.iter [ `Unicorn; `Lifted ] ~f:(fun engine ->
      let emu = Emu.create ~engine (Bap_script.project file) in
      let trace =
        Emu.Trace.start ~blocks:true ~watch:(0x403040L, 0x40313fL) emu
      in
      ignore (Emu.run emu : Emu.status);
      let accesses = Emu.Trace.accesses trace in
      let reads, writes =
        List.partition_tf accesses ~f:(fun a -> not a.write)
      in
      let inside =
        List.for_all accesses ~f:(fun a ->
            Int64.(a.addr >= 0x403040L && a.addr <= 0x40313fL))
      in
      let pcs =
        List.map reads ~f:(fun a -> a.pc)
        |> List.dedup_and_sort ~compare:Int64.compare
      in
      printf "%s: reads %d, writes %d, inside %b, by %s\n"
        (match engine with `Unicorn -> "unicorn" | `Lifted -> "lifted")
        (List.length reads) (List.length writes) inside
        (String.concat ~sep:" " (List.map pcs ~f:(sprintf "%Lx")));
      let block, n = List.hd_exn (Emu.Trace.hot ~top:1 trace) in
      let addr, reads, writes =
        List.hd_exn (Emu.Trace.addresses ~top:1 trace)
      in
      printf "hot block %Lx, %d times, hot address %Lx, %d reads, %d writes\n"
        block n addr reads writes)
