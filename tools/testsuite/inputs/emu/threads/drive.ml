#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The script calls worker of threads.c, see Emu.drive: after main let
   the threads go, worker waits on the lock, that a thread, which
   doesn't run in the call, holds, so each wait pauses, which the
   service serves, until the budget runs out, and before main let them
   go, worker spins, until the timeout runs out. The registers of a
   thread, that doesn't run, are its own, see Emu.thread_regs. *)

let reg emu tid name =
  List.Assoc.find_exn (Emu.thread_regs emu tid) ~equal:String.equal name

let () =
  match Bap_script.args () with
  | [ file ] -> (
      let proj = Bap_script.project ~disassemble:true file in
      let start until =
        let emu = Emu.create proj in
        ignore (Emu.run emu ~until : Emu.status);
        let worker =
          List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "worker"
        in
        (emu, worker)
      in
      (* a thread is about to wait on the lock *)
      let emu, worker = start 0x201550L in
      let tid = Emu.thread emu in
      let served = ref [] in
      (match
         Emu.drive emu worker ~args:[ 3L ] ~budget:3 ~service:(fun _ pc ->
             served := pc :: !served)
       with
      | Parked { pc; thread } ->
          printf "parked after the wait %b, in the thread %b, served %d\n"
            Int64.(pc = 0x20156cL)
            (thread = tid) (List.length !served)
      | Returned _ -> print_endline "returned"
      | Ended _ -> print_endline "ended");
      (* the threads spin, until main lets them go *)
      let emu, worker = start 0x2013e0L in
      (match Emu.drive emu worker ~args:[ 3L ] ~timeout:0.5 with
      | Parked { pc; _ } ->
          printf "parked in the spin %b\n"
            (List.mem [ 0x201520L; 0x201527L ] pc ~equal:Int64.equal)
      | Returned _ -> print_endline "returned"
      | Ended _ -> print_endline "ended");
      let main = Emu.thread emu in
      printf "the registers of the call %b\n"
        Int64.(
          reg emu main "RDI" = 3L && reg emu main "RSP" = Emu.reg emu "RSP");
      let others =
        List.filter (Emu.threads emu) ~f:(fun th -> th.tid <> main)
      in
      printf "the threads have their own stacks %b\n"
        (List.for_all others ~f:(fun th ->
             Int64.(reg emu th.tid "RSP" <> Emu.reg emu "RSP")));
      match Emu.thread_regs emu 99 with
      | exception Invalid_argument msg -> print_endline msg
      | _ -> print_endline "the thread 99 has registers")
  | _ -> failwith "expected FILE"
