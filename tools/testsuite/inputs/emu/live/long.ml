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
  let emu =
    Emu.create ~engine:`Lifted ~args:[ "hello" ] (Bap_script.project file)
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
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited 0"
  | Exited _ -> print_endline "exited otherwise"
  | Failed msg -> print_endline ("failed: " ^ msg)
  | _ -> print_endline "not exited"
