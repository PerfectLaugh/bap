#require "bap-primus-unicorn.emu"

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
  | [ echo; thumb; mprotect ] ->
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
      show emu (Emu.pc emu)
  | _ -> failwith "expected ECHO THUMB MPROTECT"
