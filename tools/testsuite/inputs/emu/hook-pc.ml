#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* the hooks of the memory see the instruction, that accesses it, in
   Emu.pc, in both engines: the instructions of f of smc-text.c, that
   store to its immediate at 40200b, are at 402004 and 40200f *)
let () =
  let file = List.hd_exn (Bap_script.args ()) in
  List.iter
    [ (`Unicorn, "unicorn"); (`Lifted, "lifted") ]
    ~f:(fun (engine, name) ->
      let emu = Emu.create ~engine (Bap_script.project file) in
      let stores = Int64.Table.create () in
      Emu.on_write ~primus:true ~first:0x40200bL ~last:0x40200bL emu
        (fun emu _ _ _ -> Hashtbl.incr stores (Emu.pc emu));
      ignore (Emu.run emu : Emu.status);
      printf "%s: stores to 40200b from%s\n" name
        (Hashtbl.to_alist stores
        |> List.sort ~compare:(fun (a, _) (b, _) -> Int64.compare a b)
        |> List.map ~f:(fun (pc, count) -> sprintf " %Lx:%d" pc count)
        |> String.concat))
