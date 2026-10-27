#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let engine = function
  | "unicorn" -> `Unicorn
  | "lifted" -> `Lifted
  | name -> failwithf "unknown engine %s" name ()

let ranges = [ (0x403040L, 0x40307fL); (0x4030c0L, 0x40313fL) ]

let inside range (a : Emu.Trace.access) =
  let lower, upper = range in
  Int64.(a.addr >= lower && a.addr <= upper)

let snapshot trace =
  ( Emu.Trace.accesses trace,
    Emu.Trace.accesses_count trace,
    Emu.Trace.retained_accesses trace,
    Emu.Trace.access_overflow trace )

let () =
  Bap_script.init ();
  match Bap_script.args () with
  | [ file; work; kind ] ->
      let engine_name = kind in
      let kind = engine kind in
      let create () = Emu.create ~engine:kind (Bap_script.project file) in
      let emu = create () in
      let trace =
        Emu.Trace.start ~size:1024 ~blocks:true ~accesses:65536
          ~read_values:true ~watches:ranges ~watch_accesses:8 emu
      in
      check "watch count differs" (Int.equal (List.length (Emu.Trace.watches trace)) 2);
      ignore (Emu.run emu);
      List.iter ranges ~f:(fun range ->
          let watched = Option.value_exn (Emu.Trace.watched trace range) in
          let accesses = Emu.Trace.accesses watched in
          check "watch escaped its range" (List.for_all accesses ~f:(inside range));
          check "watch is empty" (not (List.is_empty accesses));
          check "watch did not overflow" (Emu.Trace.access_overflow watched);
          check "watch lost absolute count" (Int64.(Emu.Trace.accesses_count watched > 8L));
          check "watch retention exceeds capacity"
            (Emu.Trace.retained_accesses watched <= Emu.Trace.access_capacity watched));
      let parent_accesses = Emu.Trace.accesses trace in
      check "parent lost general memory history"
        (List.exists parent_accesses ~f:(fun a -> not (List.exists ranges ~f:(fun r -> inside r a))));
      let summary = Emu.Trace.summarize trace in
      check "summary lost nonzero PCs" (summary.nonzero_pcs > 0);
      check "summary lost nonzero block sizes" (summary.nonzero_block_sizes > 0);
      check "summary lost watches" (Int.equal (List.length summary.watches) 2);
      List.iter summary.watches ~f:(fun (_, watched) ->
          check "summary lost watch overflow" watched.overflow);
      check "summary text lost watch ranges"
        (String.is_substring (Emu.Trace.describe trace) ~substring:"watch 403040-40307f");
      let file = Filename.concat work (engine_name ^ ".trace") in
      Emu.Trace.save_state trace file;
      let restored = Emu.Trace.restore_state (create ()) file in
      check "restored watch count differs"
        (Int.equal (List.length (Emu.Trace.watches restored)) 2);
      check "restored parent accesses differ"
        (Poly.equal (snapshot trace) (snapshot restored));
      List.iter ranges ~f:(fun range ->
          let expected = Option.value_exn (Emu.Trace.watched trace range) in
          let actual = Option.value_exn (Emu.Trace.watched restored range) in
          check "restored watch differs" (Poly.equal (snapshot expected) (snapshot actual)));
      Emu.Trace.stop restored;
      Emu.Trace.resume restored;
      Emu.Trace.stop restored;
      print_endline "independent watch ranges restored"
  | _ -> failwith "expected PROGRAM WORK ENGINE"
