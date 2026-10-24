#require "bap-primus-native.emu"

open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
  ignore (Emu.run emu ~until:0x40076bL);
  let argc = ref Word.b0 in
  let module Get (Machine : Primus.Machine.S) = struct
    module Env = Primus.Env.Make (Machine)
    module Value = Primus.Value.Make (Machine)
    open Machine.Syntax

    let init () =
      Env.get (Var.create "RDI" reg64_t) >>= fun x ->
      argc := Primus.Value.to_word x;
      Value.of_int ~width:64 7 >>= Env.set (Var.create "RDI" reg64_t)
  end in
  Emu.primus emu (module Get);
  Printf.printf "argc %s in Primus, %Ld in Unicorn\n%!" (Word.to_string !argc)
    (Emu.reg emu "RDI")
