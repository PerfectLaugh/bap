#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* What a hook may do, while the machine runs the program: it can't be
   asked for the memory, so Emu.read of a page, that is not in Unicorn
   yet, raises, and Emu.write raises, but Emu.save saves the checkpoint
   at the pause, that the hook asks for, before the instruction, that it
   sees, and Emu.defer runs any action there, after which the program
   continues, unless the hook stopped it too. *)

let () =
  match Bap_script.args () with
  | [ echo; dir ] -> (
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      ignore (Emu.run emu ~until:(addr "main") : Emu.status);
      let print_strings = addr "print_strings"
      and endline = addr "print_endline" in
      (* a page of the stack, far below the top, that the program never
         touched, so Unicorn doesn't have it *)
      let far = Int64.(Emu.reg emu "RSP" - 0x400000L) in
      let ckpt = Filename.concat dir "hook.ckpt" in
      let deferred = ref [] in
      Emu.on_code emu ~first:print_strings ~last:print_strings (fun emu pc ->
          (match Emu.read emu far 4096 with
          | exception Invalid_argument msg ->
              printf "read in the hook: %s\n" msg
          | _ -> print_endline "read a page, that is not in Unicorn");
          (match Emu.write emu far "x" with
          | exception Invalid_argument msg ->
              printf "write in the hook: %s\n" msg
          | () -> print_endline "wrote in the hook");
          Emu.save emu ckpt;
          Emu.defer emu (fun emu ->
              let page = Emu.read emu far 4096 in
              deferred :=
                sprintf "%d bytes, at %Lx of print_strings, paused %b"
                  (String.length page)
                  Int64.(Emu.pc emu - pc)
                  (Emu.status emu |> function Paused -> true | _ -> false)
                :: !deferred));
      (match Emu.run emu ~until:endline with
      | Paused ->
          printf "paused at print_endline %b, after the hook of print_strings\n"
            Int64.(Emu.pc emu = endline)
      | _ -> print_endline "didn't pause at print_endline");
      printf "deferred: %s\n" (String.concat ~sep:"; " !deferred);
      let info = Emu.Checkpoint.info ckpt in
      printf "the checkpoint is at print_strings %b\n"
        Int64.(info.pc = print_strings);
      (* the hook, that stops the program too, keeps it paused *)
      let seen = ref 0 in
      Emu.on_code emu ~first:endline ~last:endline (fun emu _ ->
          incr seen;
          Emu.defer emu (fun emu ->
              printf "deferred at print_endline %b, seen %d time(s)\n"
                Int64.(Emu.pc emu = endline)
                !seen);
          Emu.stop emu);
      (match Emu.run emu with
      | Paused ->
          printf "stopped at print_endline %b\n" Int64.(Emu.pc emu = endline)
      | _ -> print_endline "didn't stop");
      (* when the program is paused, the action runs at once *)
      Emu.defer emu (fun emu ->
          printf "at once, paused %b\n"
            (Emu.status emu |> function Paused -> true | _ -> false));
      (* the checkpoint continues the program from print_strings *)
      let again = Emu.create ~restore:ckpt (Bap_script.project echo) in
      printf "restored at print_strings %b\n"
        Int64.(Emu.pc again = print_strings);
      match Emu.run again ~until:endline with
      | Paused -> print_endline "the restored program reached print_endline"
      | _ -> print_endline "the restored program didn't reach print_endline")
  | _ -> failwith "expected ECHO DIR"
