#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

let pause emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwithf "doesn't pause at %Lx" addr ()

let () =
  match Bap_script.args () with
  | [ file; dir ] ->
      let emu = Emu.create (Bap_script.project ~disassemble:true file) in
      pause emu 0x2013e0L;
      let checkpoint = Filename.concat dir "thread-controls.ckpt" in
      Emu.save emu checkpoint;
      let saved_journal = Emu.Checkpoint.journal checkpoint in
      let quantum = (Emu.Checkpoint.info checkpoint).quantum_remaining in
      printf "saved quantum %b, journal %b\n"
        Float.(quantum >= 0. && quantum <= 0.005)
        (not (List.is_empty saved_journal));
      let current = Emu.thread emu in
      let other =
        List.find_exn (Emu.threads emu)
          ~f:(fun (thread : Emu.Checkpoint.thread) -> thread.tid <> current)
      in
      if Option.is_some other.waiting then failwith "expected a ready thread";
      printf "frames: active %d, parked %d\n"
        (List.length (Emu.backtrace emu))
        (List.length (Emu.backtrace emu ~thread:other.tid));
      (match Emu.backtrace emu ~thread:999 with
      | exception Invalid_argument msg -> printf "missing backtrace: %s\n" msg
      | _ -> print_endline "traced a missing thread");
      Emu.set_thread_reg emu other.tid "R8" 0x42L;
      Emu.set_thread_pc emu other.tid 0x201513L;
      Emu.resume_thread emu other.tid;
      printf "resumed thread %d at %Lx with R8 = %Lx\n" (Emu.thread emu)
        (Emu.pc emu) (Emu.reg emu "R8");
      Emu.scoped emu (fun () ->
          Emu.on_code emu ~deferred:true ~first:0x201513L ~last:0x201513L
            (fun emu _ ->
              let current = Emu.thread emu in
              let other =
                List.find_exn (Emu.threads emu)
                  ~f:(fun (thread : Emu.Checkpoint.thread) ->
                    thread.tid <> current)
              in
              printf
                "deferred inspection: active %b, parked %b, backtraces %b\n"
                (not (List.is_empty (Emu.thread_regs emu current)))
                (not (List.is_empty (Emu.thread_regs emu other.tid)))
                (List.length (Emu.backtrace emu) = 2
                && List.length (Emu.backtrace emu ~thread:other.tid) = 2));
          pause emu 0x201537L);
      printf "continued thread %d with R8 = %Lx\n" (Emu.thread emu)
        (Emu.reg emu "R8");
      (match Emu.resume_thread emu 999 with
      | exception Invalid_argument msg -> printf "missing thread: %s\n" msg
      | () -> print_endline "resumed a missing thread");
      let waiting =
        List.find_exn (Emu.threads emu)
          ~f:(fun (thread : Emu.Checkpoint.thread) ->
            thread.tid <> Emu.thread emu && Option.is_some thread.waiting)
      in
      (match Emu.resume_thread emu waiting.tid with
      | exception Invalid_argument msg -> printf "waiting thread: %s\n" msg
      | () -> print_endline "resumed a waiting thread");
      ignore (Emu.run emu : Emu.status);
      List.iter (Emu.thread_journal emu) ~f:(fun (event : Emu.event) ->
          printf "%s %s\n" event.kind event.detail);
      let restored =
        Emu.create ~restore:checkpoint
          (Bap_script.project ~disassemble:true file)
      in
      printf "restored journal %b, quantum %b\n"
        (Poly.equal saved_journal (Emu.thread_journal restored))
        Float.((Emu.Checkpoint.info checkpoint).quantum_remaining <= 0.005)
  | _ -> failwith "expected THREADS DIR"
