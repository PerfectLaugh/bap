#require "bap-primus, bap-frontend.script-debugger"

open Bap.Std
open Bap_primus.Std
module Debugger = Bap_script_debugger

(* zeroes the CRC, at the breakpoint, and shows the next instruction *)
module Zero (Machine : Primus.Machine.S) = struct
  open Machine.Syntax
  module Eval = Primus.Interpreter.Make (Machine)
  module Stops = Primus.Interpreter.Stops.Make (Machine)

  let rax = Var.create "RAX" (Type.imm 64)
  let steps = ref 0

  let stopped addr =
    if !steps = 0 then begin
      incr steps;
      Stops.set_stepping true >>= fun () ->
      Eval.get rax >>= fun x ->
      Printf.printf "at %s RAX = %s, zeroing it\n%!"
        (Addr.string_of_value addr)
        (Word.string_of_value (Primus.Value.to_word x));
      Eval.const (Word.zero 64) >>= Eval.set rax
    end
    else begin
      Stops.set_stepping false >>= fun () ->
      Stops.remove (Addr.of_int64 ~width:64 0x4004c0L) >>| fun () ->
      Printf.printf "stepped to %s\n%!" (Addr.string_of_value addr)
    end
end

let () =
  Debugger.break "0x4004c0";
  Debugger.on_stop (module Zero);
  ignore
    (Bap_script.run ~system:"bap:unicorn-executor" ~init:[ Debugger.component ]
       (Bap_script.project ~disassemble:true (List.hd (Bap_script.args ()))))
