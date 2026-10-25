#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The memory of a long run, see Emu.footprint: the lifted instructions
   are forgotten, see Emu.forget_lifts, after which the program runs on,
   as the engine keeps the code, that it compiled, and lifts the new
   instructions again, and a snapshot is dropped, see Emu.drop_snapshot,
   after which it can't be restored. *)

let show_inventory emu =
  let c = Emu.components emu in
  printf
    "inventory: lifter %b, engine %b, blocks %b, stored %b, models %b, \
     snapshots %d, pages %b\n"
    (c.lifter_entries > 0) (c.engine_entries > 0)
    (c.lifter_blocks > 0 && c.engine_blocks > 0)
    (c.stored_bytes > 0) (c.script_models > 0) c.snapshots (c.parked_pages > 0);
  c

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  let out = Filename.concat (List.nth_exn (Bap_script.args ()) 1) "out.txt" in
  let model = ref 42 in
  Emu.Checkpoint.register_ref "live-long" (module Int) model;
  let emu =
    Emu.create ~engine:`Lifted ~args:[ "hello" ]
      ~redirects:[ ("<stdout>", out) ]
      (Bap_script.project file)
  in
  let main = List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main" in
  ignore (Emu.run emu ~until:main : Emu.status);
  let f = Emu.footprint () in
  printf "footprint: heap %b, top %b, rss %s\n" (f.heap > 0)
    (f.top_heap >= f.heap)
    (match f.rss with
    | Some rss -> if rss >= f.heap then "known" else "small"
    | None -> "unknown");
  ignore (show_inventory emu);
  Emu.set_lift_cache_limit emu (Some 2);
  printf "lift cache bounded %b\n" ((Emu.components emu).lifter_entries <= 2);
  let lifted =
    Filename.concat (List.nth_exn (Bap_script.args ()) 1) "lifts.ckpt"
  in
  Emu.save emu lifted;
  printf "checkpoint keeps evicted lifts %b\n"
    (List.mem (Emu.Checkpoint.insns lifted) main ~equal:Int64.equal);
  Emu.set_lift_cache_limit emu (Some 0);
  printf "lift cache disabled %b\n" ((Emu.components emu).lifter_entries = 0);
  Emu.set_lift_cache_limit emu (Some 2);
  (match Emu.set_lift_cache_limit emu (Some (-1)) with
  | exception Invalid_argument _ -> print_endline "negative lift cache rejected"
  | () -> print_endline "negative lift cache accepted");
  let snap = Emu.snapshot emu in
  let kept = Emu.snapshot emu in
  let both = show_inventory emu in
  Emu.drop_snapshot emu snap;
  let remaining = show_inventory emu in
  printf "pages released %b\n" (remaining.parked_pages < both.parked_pages);
  (match Emu.restore emu snap with
  | exception Invalid_argument msg -> printf "%s\n" msg
  | () -> print_endline "restored a dropped snapshot");
  Emu.forget_lifts emu;
  let cleared = Emu.components emu in
  printf "forgotten: lifter %b, hooks %b\n"
    (cleared.lifter_entries = 0)
    (cleared.hook_entries = 0);
  (* the instruction is lifted again, in the hooks too *)
  printf "lifts main again %b\n" (Option.is_some (Emu.bir emu main));
  printf "hook lifts retained %b\n" ((Emu.components emu).hook_entries > 0);
  Emu.restore emu kept;
  ignore (show_inventory emu);
  printf "restored the kept snapshot at main %b\n" Int64.(Emu.pc emu = main);
  (* the instructions, that ran, as the engine lifted them, from the
     bytes, that they had, see Emu.insn_at: the first instruction of
     main runs, whose bytes stay, when the code is scrubbed *)
  let trace = Emu.Trace.start ~size:2 emu in
  ignore (Emu.step emu : Emu.status);
  Emu.Trace.stop trace;
  let retained = Emu.Trace.retained trace in
  printf "trace retained %b\n" (retained > 0 && retained <= 2);
  (match Emu.insn_at emu main with
  | Some insn ->
      let n = String.length insn.bytes in
      printf "ran main: %s of %d bytes, the ones in memory %b, lifted %b\n"
        insn.name n
        (String.equal insn.bytes (Emu.read emu main n))
        (not (List.is_empty insn.bir));
      printf "the bytes, that were lifted, from main: %d of 32\n"
        (String.length (Emu.lifted_bytes emu main 32));
      Emu.write emu main (String.make n '\000');
      printf "scrubbed: in memory %b, as they ran %b\n"
        (String.for_all (Emu.read emu main n) ~f:(Char.equal '\000'))
        (Option.exists (Emu.insn_at emu main) ~f:(fun i ->
             String.equal i.bytes insn.bytes))
  | None -> print_endline "main didn't run");
  Emu.restore emu kept;
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited 0"
  | Exited _ -> print_endline "exited otherwise"
  | Failed msg -> print_endline ("failed: " ^ msg)
  | _ -> print_endline "not exited"
