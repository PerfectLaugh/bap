#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The checkpoint keeps the bytes of the instructions, that the lifted
   engine ran, so the program, that continues from it, has them, see
   Emu.insn_at, also of main, whose code the script scrubbed before. The
   program writes to a file, as its first string is the path of the
   binary. *)

let () =
  match Bap_script.args () with
  | [ echo; dir ] ->
      let ckpt = Filename.concat dir "ran.ckpt" in
      let out = Filename.concat dir "ran.out" in
      let emu =
        Emu.create ~args:[ "hello" ]
          ~redirects:[ ("<stdout>", out) ]
          (Bap_script.project echo)
      in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      let main = addr "main" in
      ignore (Emu.run emu ~until:(addr "print_endline") : Emu.status);
      let ran = Emu.insns emu in
      let insn = Option.value_exn (Emu.insn_at emu main) in
      printf "ran main %b, %s\n"
        (List.mem ran main ~equal:Int64.equal)
        insn.name;
      Emu.write emu main (String.make (String.length insn.bytes) '\000');
      Emu.save emu ckpt;
      let again =
        Emu.create ~restore:ckpt
          ~redirects:[ ("<stdout>", out) ]
          (Bap_script.project echo)
      in
      printf "restored the instructions %b\n"
        (List.equal Int64.equal (Emu.insns again) ran);
      (match Emu.insn_at again main with
      | Some restored ->
          printf "main: %s, the bytes, that ran %b, in memory %b\n"
            restored.name
            (String.equal restored.bytes insn.bytes)
            (String.equal
               (Emu.read again main (String.length insn.bytes))
               restored.bytes);
          printf "lifted %b\n" (not (List.is_empty restored.bir))
      | None -> print_endline "main is not restored");
      printf "the bytes of main, that ran, from the checkpoint: %d of 16\n"
        (String.length (Emu.lifted_bytes again main 16));
      (match Emu.run again with
      | Exited (Some 0) -> print_endline "exited 0"
      | _ -> print_endline "didn't exit 0");
      printf "ran more %b\n" (List.length (Emu.insns again) > List.length ran)
  | _ -> failwith "expected ECHO DIR"
