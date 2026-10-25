#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The script calls worker of threads.c in main, while the threads
   wait, see Emu.call, which a hook pauses at its start, and saves the
   checkpoint, which is of the program, as it was at the call, with its
   registers and its threads, as the call is not of the program, and
   the program, that continues from it, counts as before. *)

let () =
  match Bap_script.args () with
  | [ file; dir ] -> (
      let ckpt = Filename.concat dir "call-save.ckpt" in
      let proj = Bap_script.project ~disassemble:true file in
      let emu = Emu.create proj in
      let worker =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "worker"
      in
      ignore (Emu.run emu ~until:0x2013e0L : Emu.status);
      let pc = Emu.pc emu and rsp = Emu.reg emu "RSP" in
      let threads = List.length (Emu.threads emu) in
      printf "paused at %Lx in the thread %d\n" pc (Emu.thread emu);
      (* past the push of worker, as the threads start there too *)
      Emu.on_code emu
        ~first:Int64.(worker + 3L)
        ~last:Int64.(worker + 3L)
        (fun emu _ -> Emu.stop emu);
      (match Emu.call emu worker ~args:[ 7L ] with
      | None -> printf "the call paused at %Lx\n" (Emu.pc emu)
      | Some _ -> print_endline "the call returned");
      Emu.save emu ckpt;
      let info = Emu.Checkpoint.info ckpt in
      printf "saved at the call %b, with the threads %b\n"
        Int64.(info.pc = pc)
        (List.length info.threads = threads);
      let again = Emu.create ~restore:ckpt proj in
      printf "restored at the call %b, with its stack %b\n"
        Int64.(Emu.pc again = pc)
        Int64.(Emu.reg again "RSP" = rsp);
      match Emu.run again with
      | Exited (Some 0) -> print_endline "exited 0"
      | _ -> print_endline "didn't exit 0")
  | _ -> failwith "expected FILE DIR"
