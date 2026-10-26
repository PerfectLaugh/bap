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
  | [ echo; dir ] ->
      let models = Emu.Checkpoint.create () in
      let emu =
        Emu.create ~models ~args:[ "hello" ] (Bap_script.project echo)
      in
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
      let script_state = ref 41 in
      Emu.Checkpoint.register ~package:"test" ~required:true ~version:1 models
        "script-state"
        ~save:(fun () -> Some (Int.to_string !script_state))
        ~restore:(fun data -> script_state := Int.of_string data);
      Emu.on_code emu ~first:print_strings ~last:print_strings (fun emu pc ->
          (match Emu.read emu far 4096 with
          | exception Invalid_argument msg ->
              printf "read in the hook: %s\n" msg
          | _ -> print_endline "read a page, that is not in Unicorn");
          (match Emu.write emu far "x" with
          | exception Invalid_argument msg ->
              printf "write in the hook: %s\n" msg
          | () -> print_endline "wrote in the hook");
          let rejected name f =
            match f () with
            | exception Invalid_argument msg ->
                printf "%s names its context error %b\n" name
                  (String.is_prefix msg ~prefix:(sprintf "Bap_emu.%s:" name))
            | () -> printf "%s ran in the hook\n" name
          in
          rejected "thread" (fun () -> ignore (Emu.thread emu));
          rejected "threads" (fun () -> ignore (Emu.threads emu));
          rejected "thread_regs" (fun () -> ignore (Emu.thread_regs emu 1));
          rejected "backtrace" (fun () -> ignore (Emu.backtrace emu));
          Emu.save emu ckpt;
          Emu.defer emu (fun _ -> script_state := 42);
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
      printf "script model in manifest %b\n"
        (Option.exists (Emu.Checkpoint.models ckpt) ~f:(fun models ->
             List.exists models ~f:(fun (m : Emu.Checkpoint.model_state) ->
                 String.equal m.name "test:script-state"
                 && m.version = 1 && m.required)));
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
      script_state := 99;
      let unbound =
        Emu.create ~models:(Emu.Checkpoint.create ()) ~restore:ckpt
          (Bap_script.project echo)
      in
      printf "missing required hook binding %b\n"
        (match Emu.status unbound with
        | Failed msg ->
            String.is_substring msg
              ~substring:"test:script-state is not registered"
        | _ -> false);
      let again = Emu.create ~models ~restore:ckpt (Bap_script.project echo) in
      printf "restored at print_strings %b\n"
        Int64.(Emu.pc again = print_strings);
      (match Emu.run again ~until:endline with
      | Paused -> print_endline "the restored program reached print_endline"
      | _ -> print_endline "the restored program didn't reach print_endline");
      printf "restored script state: %d\n" !script_state;
      let live = Emu.create (Bap_script.project echo) in
      ignore (Emu.run live ~until:(addr "main") : Emu.status);
      let live_far = Int64.(Emu.reg live "RSP" - 0x400000L) in
      let code_seen = ref false and site_seen = ref false in
      Emu.scoped live (fun () ->
          Emu.on_code live ~deferred:true ~first:print_strings
            ~last:print_strings (fun emu pc ->
              let page = Emu.read emu live_far 4096 in
              let tid = Emu.thread emu in
              ignore (Emu.backtrace emu);
              code_seen :=
                String.length page = 4096
                && Int64.(pc = print_strings && Emu.pc emu = pc)
                && List.exists (Emu.threads emu)
                     ~f:(fun (thread : Emu.Checkpoint.thread) ->
                       thread.tid = tid)
                && (not (List.is_empty (Emu.thread_regs emu tid)))
                && match Emu.status emu with Paused -> true | _ -> false);
          Emu.on_sites live ~deferred:true [ print_strings ] (fun emu pc ->
              site_seen :=
                Int64.(pc = print_strings && Emu.pc emu = pc)
                && match Emu.status emu with Paused -> true | _ -> false);
          match Emu.run live ~until:endline with
          | Paused ->
              printf "deferred code continued to print_endline %b\n"
                Int64.(Emu.pc live = endline)
          | _ -> print_endline "deferred code didn't continue");
      printf "deferred code inspected memory and thread %b, sites %b\n"
        !code_seen !site_seen;
      let read_seen = ref false in
      Emu.scoped live (fun () ->
          Emu.on_read live ~deferred:true (fun emu _ size ->
              let page = Emu.read emu live_far 4096 in
              (read_seen :=
                 size > 0
                 && String.length page = 4096
                 && match Emu.status emu with Paused -> true | _ -> false);
              Emu.stop emu);
          match Emu.run live with
          | Paused -> print_endline "deferred read callback stopped"
          | _ -> print_endline "deferred read callback didn't stop");
      printf "deferred read captured args and read a new page %b\n" !read_seen;
      let write_seen = ref false in
      Emu.scoped live (fun () ->
          Emu.on_write live ~deferred:true (fun emu _ size _ ->
              (write_seen :=
                 size > 0
                 && match Emu.status emu with Paused -> true | _ -> false);
              Emu.stop emu);
          match Emu.run live with
          | Paused -> print_endline "deferred write callback stopped"
          | _ -> print_endline "deferred write callback didn't stop");
      printf "deferred write captured args %b\n" !write_seen;
      let error =
        Emu.scoped live (fun () ->
            Emu.on_code live ~deferred:true (fun _ _ ->
                failwith "deferred observer failure");
            match Emu.run live with
            | exception Failure msg -> msg
            | _ -> "deferred observer error didn't propagate")
      in
      printf "deferred error: %s\n" error
  | _ -> failwith "expected ECHO DIR"
