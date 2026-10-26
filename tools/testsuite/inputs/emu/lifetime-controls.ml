#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let create ~engine file = Emu.create ~engine (Bap_script.project file)

let stats file =
  let emu = create ~engine:`Lifted file in
  let reports = ref 0 in
  let valid = ref true in
  let last = ref None in
  let subscription =
    Emu.start_stats emu ~interval:0.1 (fun stats ->
        incr reports;
        last := Some stats;
        valid :=
          !valid
          && Int64.(stats.instructions > 0L)
          && stats.lifted_blocks > 0 && stats.active_threads = 1
          && stats.hook_dispatches >= 0 && Option.is_some stats.rss
          && Int64.(stats.last_pc <> 0L))
  in
  ignore (Emu.run emu : Emu.status);
  Emu.stop_stats subscription;
  printf "stats: reports %b, valid %b, captured %b\n" (!reports > 0) !valid
    (Option.exists !last ~f:(fun stats -> Int64.(stats.instructions > 0L)))

let snapshots file =
  List.iter [ `Unicorn; `Lifted ] ~f:(fun engine ->
      let emu = create ~engine file in
      let main =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main"
      in
      ignore (Emu.run emu ~until:main : Emu.status);
      let oldest = Emu.snapshot emu in
      let kept = Emu.snapshot emu in
      let extra = Emu.snapshot emu in
      Emu.drop_snapshot emu extra;
      let explicit = (Emu.components emu).snapshots = 2 in
      Emu.set_snapshot_limit emu (Some 1);
      let managed = (Emu.components emu).snapshots = 1 in
      let evicted =
        match Emu.restore emu oldest with
        | exception Invalid_argument _ -> true
        | () -> false
      in
      Emu.restore emu kept;
      let first = (Emu.components emu).snapshots = 1 in
      Emu.restore emu kept;
      let second =
        (Emu.components emu).snapshots = 1 && Int64.(Emu.pc emu = main)
      in
      let negative =
        match Emu.set_snapshot_limit emu (Some (-1)) with
        | exception Invalid_argument _ -> true
        | () -> false
      in
      Emu.set_snapshot_limit emu None;
      Emu.drop_snapshot emu kept;
      let empty = (Emu.components emu).snapshots = 0 in
      printf
        "%s snapshots: explicit %b, managed %b, evicted %b, restores %b, \
         negative %b, empty %b\n"
        (match engine with `Unicorn -> "unicorn" | `Lifted -> "lifted")
        explicit managed evicted (first && second) negative empty)

let maintenance file =
  List.iter [ `Unicorn; `Lifted ] ~f:(fun engine ->
      let emu = create ~engine file in
      let main =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main"
      in
      let subscription =
        Emu.start_maintenance emu ~interval:0.000001 ~lift_cache_limit:2
          ~forget_lifts:true ~reclaim_blocks:true ~compact_heap:true ()
      in
      ignore (Emu.run emu ~until:main : Emu.status);
      Emu.stop_stats subscription;
      let inventory = Emu.components emu in
      let telemetry = Emu.maintenance_stats emu in
      let knowledge =
        match engine with
        | `Unicorn -> inventory.knowledge_objects = 0
        | `Lifted -> inventory.knowledge_objects > 0
      in
      let measured =
        telemetry.lift_cleanup.count > 0
        && telemetry.lift_cleanup.count = telemetry.block_reclamation.count
        && telemetry.lift_cleanup.count = telemetry.heap_compaction.count
        && List.for_all
             [
               telemetry.lru_reconstruction;
               telemetry.entry_eviction;
               telemetry.cache_load;
               telemetry.cache_merge;
               telemetry.cache_write;
               telemetry.lift_cleanup;
               telemetry.block_reclamation;
               telemetry.heap_compaction;
             ] ~f:(fun operation ->
               operation.count >= 0 && Float.(operation.seconds >= 0.))
      in
      printf
        "%s maintenance: bounded %b, sparse %b, knowledge %b, at main %b, \
         telemetry %b\n"
        (match engine with `Unicorn -> "unicorn" | `Lifted -> "lifted")
        (inventory.lifter_entries <= 2)
        (inventory.sparse_pages > 0)
        knowledge
        Int64.(Emu.pc emu = main)
        measured)

let deadline file =
  let emu = create ~engine:`Unicorn file in
  ignore (Emu.start_deadline ~code:124 0.05);
  ignore (Emu.run emu : Emu.status)

let cancel file =
  let deadline = Emu.start_deadline ~code:124 0.02 in
  Emu.cancel_deadline deadline;
  Caml_unix.sleepf 0.05;
  print_endline "deadline cancelled";
  (match Emu.start_deadline (-1.) with
  | exception Invalid_argument _ -> print_endline "negative deadline rejected"
  | _ -> print_endline "negative deadline accepted");
  let emu = create ~engine:`Lifted file in
  match Emu.start_stats emu ~interval:0. (fun _ -> ()) with
  | exception Invalid_argument _ -> print_endline "invalid stats rejected"
  | _ -> print_endline "invalid stats accepted"

let () =
  match Bap_script.args () with
  | [ "stats"; file ] -> stats file
  | [ "snapshots"; file ] -> snapshots file
  | [ "maintenance"; file ] -> maintenance file
  | [ "deadline"; file ] -> deadline file
  | [ "cancel"; file ] -> cancel file
  | _ ->
      failwith
        "expected stats, snapshots, maintenance, deadline, or cancel FILE"
