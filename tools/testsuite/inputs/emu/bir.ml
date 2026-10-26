#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let show emu addr =
  match Emu.bir emu addr with
  | None -> printf "%Lx: not an instruction\n" addr
  | Some (size, blks) ->
      printf "%Lx: %d bytes\n" addr size;
      List.iter blks ~f:(fun b -> print_endline (Blk.to_string b))

let () =
  match Bap_script.args () with
  | [ echo; thumb; mprotect; aarch64 ] -> (
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      show emu (Emu.pc emu);
      (* in a hook, where the program runs, at the address of the code *)
      let n = ref 0 in
      Emu.on_code emu (fun emu addr ->
          incr n;
          if !n = 2 then (
            printf "hook ";
            show emu addr));
      ignore (Emu.run emu ~until:0x40076bL);
      show emu 0x40076bL;
      (* the patched code is lifted anew, mov $0xa, %edi becomes mov $0x2b *)
      show emu 0x400727L;
      Emu.write emu 0x400727L "\xbf\x2b";
      show emu 0x400727L;
      (* the Thumb code of ARM, by the lower bit of the address *)
      let arm = Emu.create (Bap_script.project thumb) in
      printf "thumb pc %Lx\n" (Emu.pc arm);
      show arm (Emu.pc arm);
      (* the IT instruction, it eq, lifted itself, leaves the decoder
         out of its block, so the instruction after the block, subs r3,
         #1, lifted next, has no condition, and the member of the block,
         lsreq r2, r4, #1, lifted before the IT instruction, has its
         condition *)
      show arm 0x2028bL;
      show arm 0x2028fL;
      show arm 0x2028dL;
      (* the halfword, that looks like an IT instruction, it eq, but is
         the second one of a 32-bit instruction, that was lifted, ldr.w
         r11, [r0, #0xf08], written over eor.w r2, r1, r4, lsr #1, is
         not one, so lsls r5, r4, #31 after it has no condition *)
      Emu.write arm 0x20284L "\xd0\xf8\x08\xbf";
      show arm 0x20285L;
      show arm 0x20289L;
      (* the code, that the program writes to its buffer at 0x405000, is
         lifted from its bytes, the zeros before, mov $42, %eax after *)
      let code = 0x405000L in
      let emu = Emu.create (Bap_script.project mprotect) in
      printf "unwritten ";
      show emu code;
      Emu.on_code emu ~first:code ~last:code (fun emu addr ->
          printf "written hook ";
          show emu addr);
      ignore (Emu.run emu ~until:code);
      printf "written ";
      show emu (Emu.pc emu);
      (* a synthetic AArch64 stub returns to the caller of Emu.call *)
      let emu = Emu.create (Bap_script.project aarch64) in
      let stub = Emu.pc emu in
      Emu.write emu stub (Emu.AArch64.bytes Emu.AArch64.ret);
      match Emu.call emu stub ~args:[ 42L ] with
      | Some 42L -> print_endline "synthetic AArch64 stub returned 42"
      | result ->
          failwithf "synthetic AArch64 stub returned %s"
            (Option.value_map result ~default:"nothing" ~f:Int64.to_string)
            ())
  | _ -> failwith "expected ECHO THUMB MPROTECT AARCH64"
