#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let subroutine () =
  let x0 = Var.create "R0" (Imm 64) in
  let word = Word.of_int64 ~width:64 in
  let first =
    Blk.create
      ~defs:[ Def.create x0 (Bil.int (word 1L)) ]
      ~jmps:[]
      ()
  in
  let second =
    Blk.create
      ~defs:[ Def.create x0 (Bil.BinOp (Bil.PLUS, Bil.Var x0, Bil.int (word 1L))) ]
      ~jmps:[ Jmp.create_goto (Label.indirect (Bil.int (word 0xdeadL))) ]
      ()
  in
  let first = Term.append jmp_t first (Jmp.create_goto (Label.direct (Term.tid second))) in
  Sub.create ~name:"eval-sub" ~blks:[ first; second ] ()

let evaluate emu sub =
  Emu.set_reg emu "X0" 0L;
  Emu.eval_sub emu sub;
  check "eval_sub did not execute both blocks" (Int64.equal (Emu.reg emu "X0") 2L)

let () =
  Bap_script.init ();
  match Bap_script.args () with
  | [ file ] ->
      let project () = Bap_script.project file in
      let sub = subroutine () in
      let emu = Emu.create ~engine:`Lifted (project ()) in
      evaluate emu sub;
      let checkpoint = "eval-sub-test.ckpt" in
      Emu.save emu checkpoint;
      let restored = Emu.create ~engine:`Lifted ~restore:checkpoint (project ()) in
      evaluate restored sub;
      Stdlib.Sys.remove checkpoint;
      print_endline "eval_sub internal CFG and restored state ok"
  | _ -> failwith "expected PROGRAM"
