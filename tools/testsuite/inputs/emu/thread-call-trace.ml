#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let () =
  match Bap_script.args () with
  | [ file; engine ] ->
      let engine = if String.equal engine "unicorn" then `Unicorn else `Lifted in
      let emu = Emu.create ~engine (Bap_script.project file) in
      let worker =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "worker"
      in
      ignore (Emu.run emu ~until:worker : Emu.status);
      let current = Emu.thread emu in
      let r =
        Emu.record emu (fun () ->
            Emu.call emu worker ~thread:1 ~args:[ 7L ])
      in
      let tids = Emu.Trace.tids r.trace in
      let tagged =
        Bigarray.Array1.dim tids > 0
        && List.init (Bigarray.Array1.dim tids) ~f:(Bigarray.Array1.get tids)
           |> List.for_all ~f:(Int64.equal 1L)
      in
      printf "current %d; returned %b; call tids %b\n" current
        (match r.result with Ok (Some 70L) -> true | _ -> false)
        tagged
  | _ -> failwith "expected FILE ENGINE"
