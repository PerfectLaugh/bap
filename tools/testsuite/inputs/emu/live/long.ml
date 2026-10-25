#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The memory of a long run, see Emu.footprint: the lifted instructions
   are forgotten, see Emu.forget_lifts, after which the program runs on,
   as the engine keeps the code, that it compiled, and lifts the new
   instructions again, and a snapshot is dropped, see Emu.drop_snapshot,
   after which it can't be restored. *)

let () =
  let file = List.hd_exn (Bap_script.args ()) in
  let out = Filename.concat (List.nth_exn (Bap_script.args ()) 1) "out.txt" in
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
  let snap = Emu.snapshot emu in
  let kept = Emu.snapshot emu in
  Emu.drop_snapshot emu snap;
  (match Emu.restore emu snap with
  | exception Invalid_argument msg -> printf "%s\n" msg
  | () -> print_endline "restored a dropped snapshot");
  Emu.forget_lifts emu;
  (* the instruction is lifted again, in the hooks too *)
  printf "lifts main again %b\n" (Option.is_some (Emu.bir emu main));
  Emu.restore emu kept;
  printf "restored the kept snapshot at main %b\n" Int64.(Emu.pc emu = main);
  (* the instructions, that ran, as the engine lifted them, from the
     bytes, that they had, see Emu.insn_at: the first instruction of
     main runs, whose bytes stay, when the code is scrubbed *)
  ignore (Emu.step emu : Emu.status);
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
