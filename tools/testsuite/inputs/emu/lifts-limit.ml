#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let normalize text =
  let is_hex = function
    | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true
    | _ -> false
  in
  let rec loop i acc =
    if i = String.length text then String.of_char_list (List.rev acc)
    else if Char.equal text.[i] '%' then
      let rec skip i =
        if i < String.length text && is_hex text.[i] then skip (i + 1) else i
      in
      loop (skip (i + 1)) ('%' :: acc)
    else loop (i + 1) (text.[i] :: acc)
  in
  loop 0 []

let bir blks =
  String.concat ~sep:"\n" (List.map blks ~f:Blk.to_string)
  |> String.split_lines
  |> List.map ~f:(fun line ->
      let rec digits i =
        if i < String.length line then
          match line.[i] with
          | '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> digits (i + 1)
          | _ -> i
        else i
      in
      let i = digits 0 in
      if i > 0 && i < String.length line && Char.equal line.[i] ':' then
        String.drop_prefix line i |> normalize
      else normalize line)
  |> String.concat ~sep:"\n"

let create file output =
  Emu.create ~engine:`Lifted ~args:[ "hello" ]
    ~redirects:[ ("<stdout>", output) ]
    (Bap_script.project file)

let expect_exit emu =
  match Emu.run emu with
  | Exited (Some 0) -> ()
  | _ -> failwith "the cache test program didn't exit 0"

let lifts_dir () =
  Filename.concat (Sys.getenv_exn "BAP_CACHE_DIR") "lifted/lifts"

let clear_lifts () =
  match Stdlib.Sys.readdir (lifts_dir ()) with
  | files ->
      Array.iter files ~f:(fun file ->
          Stdlib.Sys.remove (Filename.concat (lifts_dir ()) file))
  | exception Sys_error _ -> ()

let valid (stats : Emu.maintenance_stats) =
  List.for_all
    [
      stats.lru_reconstruction;
      stats.entry_eviction;
      stats.cache_load;
      stats.cache_merge;
      stats.cache_write;
      stats.lift_cleanup;
      stats.block_reclamation;
      stats.heap_compaction;
    ] ~f:(fun operation ->
      operation.count >= 0 && Float.(operation.seconds >= 0.))
  && stats.cache_entries_written >= 0
  && stats.cache_bytes_written >= 0

let populate file output =
  let emu = create file output in
  for _ = 1 to 192 do
    match Emu.step emu with
    | Paused -> ()
    | _ -> failwith "the baseline ended before its cache was populated"
  done;
  let snapshot = Emu.snapshot emu in
  expect_exit emu;
  Emu.restore emu snapshot;
  let initial = (Emu.components emu).lifter_entries in
  if initial <= 64 then
    failwithf "expected substantially more than 64 entries, got %d" initial ();
  (emu, initial)

let executable_addresses emu =
  let regions = Emu.regions emu in
  List.filter (Emu.insns emu) ~f:(fun addr ->
      List.exists regions ~f:(fun region ->
          region.executable
          && Int64.(addr >= region.lower && addr <= region.upper)))

let samples emu =
  let addresses = executable_addresses emu in
  List.map
    [
      List.hd_exn addresses;
      List.nth_exn addresses (List.length addresses / 2);
      List.last_exn addresses;
    ]
    ~f:(fun addr ->
      match Emu.bir emu addr with
      | Some (_, blks) -> (addr, bir blks)
      | None -> failwithf "no baseline BIR at %Lx" addr ())

let same_samples emu samples =
  List.for_all samples ~f:(fun (addr, expected) ->
      match Emu.bir emu addr with
      | Some (_, blks) -> String.equal expected (bir blks)
      | None -> false)

let code_size = 1280
let exit_code = "\xb8\x3c\x00\x00\x00\x31\xff\x0f\x05\x0f\x0b"

let install_code emu =
  let executed = Emu.insns emu in
  let available (region : Emu.region) =
    region.executable
    && Int64.(region.upper - region.lower >= 1296L)
    && List.for_all executed ~f:(fun addr ->
        Int64.(addr < region.lower || addr >= region.lower + 1296L))
  in
  let start = (List.find_exn (Emu.regions emu) ~f:available).lower in
  Emu.write emu start (String.make code_size '\x90' ^ exit_code);
  Emu.set_pc emu start;
  start

let run_until emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwithf "the synthetic code didn't pause at %Lx" addr ()

let bulk_test baseline initial =
  Emu.save_lifts baseline;
  let saved = Emu.maintenance_stats baseline in
  Emu.set_lift_cache_limit baseline (Some 8);
  let bulk = Emu.maintenance_stats baseline in
  let trimmed = (Emu.components baseline).lifter_entries in
  printf "bulk trim: %d entries\n%!" trimmed;
  if trimmed <> 8 then failwith "bulk trimming didn't retain eight entries";
  let bulk_once =
    bulk.cache_write.count = saved.cache_write.count + 1
    && bulk.cache_entries_written > saved.cache_entries_written
    && bulk.cache_bytes_written > saved.cache_bytes_written
    && bulk.entry_eviction.count = initial - 8
    && valid saved && valid bulk
  in
  printf "bulk telemetry: %b\n%!" bulk_once;
  if not bulk_once then failwith "bulk trim telemetry differs";
  Emu.set_lift_cache_limit baseline (Some 0);
  let empty = (Emu.components baseline).lifter_entries in
  let totals = Emu.maintenance_stats baseline in
  let expected =
    totals.lru_reconstruction.count = 2
    && totals.entry_eviction.count = initial
    && totals.cache_load.count = 3
    && totals.cache_merge.count = 2
    && totals.cache_write.count = 3
    && totals.cache_entries_written = 3 * initial
    && totals.cache_bytes_written > 0
    && valid totals
  in
  printf "zero trim: %d entries\n%!" empty;
  printf "cache telemetry: %b\n%!" expected;
  if empty <> 0 then failwith "zero limit retained entries";
  if not expected then failwith "cumulative cache telemetry differs"

let incremental_test file dir initial =
  let output = Filename.concat dir "incremental.txt" in
  let emu = create file output in
  Emu.set_lift_cache_limit emu (Some 8);
  let bulk = Emu.maintenance_stats emu in
  let start = install_code emu in
  run_until emu Int64.(start + 192L);
  let deferred = Emu.maintenance_stats emu in
  let evictions = deferred.entry_eviction.count - bulk.entry_eviction.count in
  let no_periodic_save =
    evictions > 128 && deferred.cache_write.count = bulk.cache_write.count
  in
  printf "incremental eviction: %d entries, deferred %b\n%!" evictions
    no_periodic_save;
  if not no_periodic_save then
    failwith "incremental eviction saved before maintenance";
  let maintenance = Emu.start_maintenance emu ~interval:0.000001 () in
  (match Emu.step emu with
  | Paused -> ()
  | _ -> failwith "the maintenance step ended the synthetic code");
  Emu.stop_stats maintenance;
  let scheduled = Emu.maintenance_stats emu in
  let scheduled_union =
    scheduled.cache_write.count = deferred.cache_write.count + 1
    && scheduled.cache_entries_written - deferred.cache_entries_written
       = initial + scheduled.entry_eviction.count - bulk.entry_eviction.count
    && scheduled.cache_bytes_written > deferred.cache_bytes_written
  in
  printf "scheduled persistence: %b\n%!" scheduled_union;
  if not scheduled_union then
    failwith "scheduled save didn't preserve the cache union";
  let high_water = ref None in
  while Option.is_none !high_water && Int64.(Emu.pc emu < start + 1280L) do
    let next = Int64.(min (start + 1280L) (Emu.pc emu + 64L)) in
    run_until emu next;
    let stats = Emu.maintenance_stats emu in
    if stats.cache_write.count > scheduled.cache_write.count then
      high_water := Some stats
  done;
  let high_water = Option.value_exn !high_water ~message:"no high-water save" in
  let high_water_once =
    high_water.cache_write.count = scheduled.cache_write.count + 1
    && high_water.entry_eviction.count - scheduled.entry_eviction.count >= 1024
    && high_water.cache_entries_written - scheduled.cache_entries_written
       = initial + high_water.entry_eviction.count - bulk.entry_eviction.count
    && high_water.cache_bytes_written > scheduled.cache_bytes_written
  in
  printf "high-water persistence: %b\n%!" high_water_once;
  if not high_water_once then failwith "high-water save telemetry differs";
  let nop_sample =
    match Emu.bir emu start with
    | Some (_, blks) -> bir blks
    | None -> failwith "no synthetic BIR"
  in
  Emu.save_lifts emu;
  let final = Emu.maintenance_stats emu in
  let expected =
    initial + final.entry_eviction.count - bulk.entry_eviction.count
  in
  if not (valid final) then failwith "invalid incremental telemetry";
  (expected, start, nop_sample)

let cache_test file dir =
  clear_lifts ();
  let baseline_output = Filename.concat dir "baseline.txt" in
  let reused_output = Filename.concat dir "reused.txt" in
  let baseline, initial = populate file baseline_output in
  print_endline "baseline: exited 0";
  let samples = samples baseline in
  printf "populated: %d entries\n%!" initial;
  bulk_test baseline initial;
  let expected, start, nop_sample = incremental_test file dir initial in
  let reused = create file reused_output in
  let fresh = Emu.maintenance_stats reused in
  if fresh.cache_write.count <> 0 || fresh.lru_reconstruction.count <> 0 then
    failwith "a new emulator inherited maintenance telemetry";
  let restored = (Emu.components reused).lifter_entries in
  Emu.set_lift_cache_limit reused (Some expected);
  let exact = (Emu.components reused).lifter_entries in
  Emu.set_lift_cache_limit reused (Some (expected + 1));
  let greater = (Emu.components reused).lifter_entries in
  let original = Emu.snapshot reused in
  let synthetic_start = install_code reused in
  let same_bir =
    Int64.equal start synthetic_start
    && same_samples reused (samples @ [ (start, nop_sample) ])
  in
  printf "restored cache: %d entries, limits %b, BIR %b\n%!" restored
    (exact = expected && greater = expected)
    same_bir;
  if restored <> expected then
    failwithf "expected %d restored entries, got %d" expected restored ();
  if exact <> expected || greater <> expected then
    failwith "exact or greater limit evicted entries";
  if not same_bir then failwith "restored BIR differs";
  Emu.restore reused original;
  expect_exit reused;
  print_endline "reused execution: exited 0"

let clean_exit_test file dir =
  clear_lifts ();
  let baseline, initial =
    populate file (Filename.concat dir "clean-baseline.txt")
  in
  Emu.set_lift_cache_limit baseline (Some 8);
  let bulk = Emu.maintenance_stats baseline in
  let start = install_code baseline in
  run_until baseline Int64.(start + 192L);
  let deferred = Emu.maintenance_stats baseline in
  if deferred.cache_write.count <> bulk.cache_write.count then
    failwith "clean-exit setup saved incrementally";
  let expected =
    initial + deferred.entry_eviction.count - bulk.entry_eviction.count
  in
  Out_channel.write_all
    (Filename.concat dir "clean-expected")
    ~data:(sprintf "%d\n%Ld\n" expected start);
  Emu.write baseline (Emu.pc baseline) exit_code;
  expect_exit baseline;
  printf "clean exit: populated %d entries\n%!" expected

let clean_reuse_test file dir =
  let expected, start =
    match In_channel.read_lines (Filename.concat dir "clean-expected") with
    | [ expected; start ] -> (Int.of_string expected, Int64.of_string start)
    | _ -> failwith "invalid clean-exit expectation"
  in
  let reused = create file (Filename.concat dir "clean-reused.txt") in
  let restored = (Emu.components reused).lifter_entries in
  let original = Emu.snapshot reused in
  let synthetic_start = install_code reused in
  let nop =
    Int64.equal start synthetic_start
    &&
    match Emu.bir reused start with
    | Some (_, blks) -> not (String.is_empty (bir blks))
    | None -> false
  in
  printf "clean-exit reuse: %d entries, BIR %b\n%!" restored nop;
  if restored <> expected then
    failwithf "clean exit restored %d entries instead of %d" restored expected
      ();
  if not nop then failwith "clean exit didn't preserve synthetic BIR";
  Emu.restore reused original;
  expect_exit reused;
  print_endline "clean-exit execution: exited 0"

let () =
  Caml_unix.putenv "BAP_LIFTED_STATS" "1";
  match Bap_script.args () with
  | [ file; dir ] -> cache_test file dir
  | [ "clean"; file; dir ] -> clean_exit_test file dir
  | [ "check"; file; dir ] -> clean_reuse_test file dir
  | _ -> failwith "expected [clean|check] PROGRAM DIR"
