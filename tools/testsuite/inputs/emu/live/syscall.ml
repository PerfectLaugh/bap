#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The program writes its CRC with the system call of Linux, svc #0 of
   AArch64, or syscall of x86-64, which no Lisp function serves, so it
   fails without the hook, and the hook of all system calls serves it,
   in the engine of the argument. *)

let run engine file ~hook =
  let emu = Emu.create ~engine (Bap_script.project file) in
  let checkpointed = ref false in
  if hook then
    Emu.on_syscall emu (fun emu number args ->
        match (number, args) with
        | (64L | 1L), [ fd; buf; len; _; _; _ ] ->
            printf "write %Ld: %S\n" fd
              (Emu.read emu buf (Int64.to_int_exn len));
            if not !checkpointed then begin
              checkpointed := true;
              Emu.save emu "syscall.ckpt"
            end;
            Return len
        | _ -> Default);
  Emu.run emu

let () =
  match Bap_script.args () with
  | [ file; engine ] -> (
      let engine =
        if String.equal engine "unicorn" then `Unicorn else `Lifted
      in
      (match run engine file ~hook:false with
      | Failed msg ->
          printf "fails without the hook, as it's unbound %b\n"
            (String.is_substring msg ~substring:"unbound function intrinsic:")
      | _ -> print_endline "doesn't fail without the hook");
      match run engine file ~hook:true with
      | Exited (Some 0) ->
          print_endline "exited 0";
          let context = Emu.Checkpoint.context "syscall.ckpt" in
          printf "syscall journal: %b\n"
            (List.exists context.events ~f:(fun (event : Emu.event) ->
                 String.equal event.kind "syscall"))
      | _ -> print_endline "didn't exit 0")
  | _ -> failwith "expected FILE ENGINE"
