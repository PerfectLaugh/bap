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

let () =
  let file, dir =
    match Bap_script.args () with
    | [ file; dir ] -> (file, dir)
    | _ -> failwith "expected PROGRAM DIR"
  in
  Caml_unix.putenv "BAP_LIFTED_STATS" "1";
  let lifts = Filename.concat (Sys.getenv_exn "BAP_CACHE_DIR") "lifted/lifts" in
  (match Stdlib.Sys.readdir lifts with
  | files ->
      Array.iter files ~f:(fun file ->
          Stdlib.Sys.remove (Filename.concat lifts file))
  | exception Sys_error _ -> ());
  let baseline_output = Filename.concat dir "baseline.txt" in
  let reused_output = Filename.concat dir "reused.txt" in
  let baseline = create file baseline_output in
  for _ = 1 to 192 do
    match Emu.step baseline with
    | Paused -> ()
    | _ -> failwith "the baseline ended before its cache was populated"
  done;
  let snapshot = Emu.snapshot baseline in
  expect_exit baseline;
  print_endline "baseline: exited 0";
  Emu.restore baseline snapshot;
  let initial = (Emu.components baseline).lifter_entries in
  if initial <= 64 then
    failwithf "expected substantially more than 64 entries, got %d" initial ();
  let regions = Emu.regions baseline in
  let addresses =
    List.filter (Emu.insns baseline) ~f:(fun addr ->
        List.exists regions ~f:(fun region ->
            region.executable
            && Int64.(addr >= region.lower && addr <= region.upper)))
  in
  let samples =
    List.map
      [
        List.hd_exn addresses;
        List.nth_exn addresses (List.length addresses / 2);
        List.last_exn addresses;
      ]
      ~f:(fun addr ->
        match Emu.bir baseline addr with
        | Some (_, blks) -> (addr, bir blks)
        | None -> failwithf "no baseline BIR at %Lx" addr ())
  in
  printf "populated: %d entries\n%!" initial;
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
  in
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
  if not expected then failwith "cumulative cache telemetry differs";
  let reused = create file reused_output in
  let fresh = Emu.maintenance_stats reused in
  if fresh.cache_write.count <> 0 || fresh.lru_reconstruction.count <> 0 then
    failwith "a new emulator inherited maintenance telemetry";
  let restored = (Emu.components reused).lifter_entries in
  Emu.set_lift_cache_limit reused (Some initial);
  let exact = (Emu.components reused).lifter_entries in
  Emu.set_lift_cache_limit reused (Some (initial + 1));
  let greater = (Emu.components reused).lifter_entries in
  let same_bir =
    List.for_all samples ~f:(fun (addr, expected) ->
        match Emu.bir reused addr with
        | Some (_, blks) -> String.equal expected (bir blks)
        | None -> false)
  in
  printf "restored cache: %d entries, limits %b, BIR %b\n%!" restored
    (exact = initial && greater = initial)
    same_bir;
  if restored <> initial then
    failwithf "expected %d restored entries, got %d" initial restored ();
  if exact <> initial || greater <> initial then
    failwith "exact or greater limit evicted entries";
  if not same_bir then failwith "restored BIR differs";
  expect_exit reused;
  print_endline "reused execution: exited 0"
