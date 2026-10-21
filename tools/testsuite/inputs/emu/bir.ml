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
  | [ echo; thumb ] ->
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      show emu (Emu.pc emu);
      ignore (Emu.run emu ~until:0x40076bL);
      show emu 0x40076bL;
      (* the patched code is lifted anew, mov $0xa, %edi becomes mov $0x2b *)
      show emu 0x400727L;
      Emu.patch emu 0x400727L "\xbf\x2b";
      show emu 0x400727L;
      (* the Thumb code of ARM, by the lower bit of the address *)
      let arm = Emu.create (Bap_script.project thumb) in
      printf "thumb pc %Lx\n" (Emu.pc arm);
      show arm (Emu.pc arm)
  | _ -> failwith "expected ECHO THUMB"
