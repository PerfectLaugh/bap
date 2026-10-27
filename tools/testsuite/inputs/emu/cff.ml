#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let check name ok = if not ok then failwith name

let subroutine ?(result = 2L) ?(call = false) () =
  let x0 = Var.create "RAX" (Imm 64) in
  let mem = Var.create "mem" (Type.Mem (`r64, `r8)) in
  let word = Word.of_int64 ~width:64 in
  let first =
    Blk.create
      ~defs:[ Def.create x0 (Bil.int (word 1L)) ]
      ~jmps:[]
      ()
  in
  let store =
    Bil.store ~mem:(Bil.Var mem) ~addr:(Bil.int (word 0x403000L))
      (Bil.int (Word.of_int64 ~width:8 0x42L)) LittleEndian `r8
  in
  let jmps =
    if call then
      [ Jmp.create_call
          (Call.create ~target:(Label.direct (Tid.for_name "mprotect")) ()) ]
    else [ Jmp.create_goto (Label.indirect (Bil.int (word 0xdeadL))) ]
  in
  let second =
    Blk.create
      ~defs:[ Def.create x0 (Bil.int (word result)); Def.create mem store ]
      ~jmps ()
  in
  let first = Term.append jmp_t first (Jmp.create_goto (Label.direct (Term.tid second))) in
  Sub.create ~name:"cff-test" ~blks:[ first; second ] ()

let () =
  Bap_script.init ();
  match Bap_script.args () with
  | [ file ] ->
      let emu = Emu.create ~engine:`Lifted (Bap_script.project file) in
      let entry = Emu.pc emu in
      let capture = Emu.Trace.capture_state ~size:8 ~regs:[ "RAX" ] emu [ entry ] in
      ignore (Emu.step emu);
      let dispatches = Emu.Cff.dispatchers ~state:"RAX" capture in
      check "dispatcher capture missing" (Int.equal (List.length dispatches) 1);
      check "dispatcher site differs" (Int64.equal (List.hd_exn dispatches).site entry);
      Emu.Trace.stop_state_capture capture;
      let recovery = Emu.Cff.recover ~max_blocks:4 emu [ entry ] in
      check "recovery found no blocks"
        (Term.length blk_t recovery.sub > 0);
      let original = subroutine () and simplified = subroutine () in
      let result =
        Emu.Cff.check emu ~regs:[ "RAX" ] ~continuation:[ (0x403000L, 1) ]
          ~original ~simplified ()
      in
      check "equivalent CFF check failed" result.ok;
      let wrong = subroutine ~result:99L () in
      let result =
        Emu.Cff.check emu ~regs:[ "RAX" ] ~continuation:[ (0x403000L, 1) ]
          ~original ~simplified:wrong ()
      in
      check "wrong result was accepted" (not result.ok);
      check "wrong result did not blame registers" (not result.registers);
      let with_call = subroutine ~call:true () in
      let result =
        Emu.Cff.check emu ~regs:[ "RAX" ] ~original:with_call ~simplified ()
      in
      check "deleted call was accepted" (not result.ok);
      check "deleted call was not inventoried" (not result.effects);
      check "deleted external boundary was accepted" (not result.boundaries);
      print_endline "CFF recovery and validation passed"
  | _ -> failwith "expected PROGRAM"
