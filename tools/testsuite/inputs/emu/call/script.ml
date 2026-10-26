#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* Calls worker of spawn.c with 1 and 2 at the entry of main, see
   Emu.call, which then finds their results in out, prints them, 11 and
   21, and exits, with api=DIR, the api of the target, e.g., of
   PowerPC. The registers are as before the calls, and a call, that a
   hook pauses, continues with run, after which the program pauses where
   it was, with the result. *)

let () =
  let args = Bap_script.args () in
  let api = List.filter_map args ~f:(String.chop_prefix ~prefix:"api=") in
  let emu = Emu.create (Bap_script.project ~api (List.hd_exn args)) in
  let last_pc = ref 0L and syscall = ref None and continued = ref false in
  Emu.on_code emu (fun _ pc ->
      (match !syscall with
      | Some site when not (Int64.equal site pc) ->
          continued := true;
          syscall := None
      | _ -> ());
      last_pc := pc);
  Emu.on_syscall emu (fun _ _ _ ->
      syscall := Some !last_pc;
      Default);
  let addr name =
    List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
  in
  (match Emu.run emu ~until:(addr "main") with
  | Paused -> ()
  | _ -> failwith "doesn't pause at main");
  let pc = Emu.pc emu in
  let registers =
    List.map (Emu.registers emu) ~f:(fun r -> (r, Emu.reg_word emu r))
  in
  let call n =
    match Emu.call emu (addr "worker") ~args:[ n ] with
    | Some x -> printf "worker(%Ld) = %Ld\n%!" n x
    | None -> printf "worker(%Ld) paused\n%!" n
  in
  call 1L;
  call 2L;
  printf "pc back %b, registers back %b\n%!"
    Int64.(Emu.pc emu = pc)
    (List.for_all registers ~f:(fun (r, x) ->
         Bap.Std.Word.equal (Emu.reg_word emu r) x));
  printf "returned %s\n%!"
    (Option.value_map (Emu.returned emu) ~default:"none" ~f:Int64.to_string);
  let stopped = ref false in
  Emu.on_code emu ~first:(addr "worker") ~last:(addr "worker") (fun emu _ ->
      if not !stopped then begin
        stopped := true;
        Emu.stop emu
      end);
  (match Emu.call emu (addr "worker") ~args:[ 1L ] with
  | None ->
      printf "paused in worker %b\n%!"
        Int64.(Emu.pc emu land -2L = addr "worker")
  | Some _ -> print_endline "not paused");
  (match Emu.run emu with
  | Paused ->
      printf "paused back at main %b, returned %s\n%!"
        Int64.(Emu.pc emu = pc)
        (Option.value_map (Emu.returned emu) ~default:"none" ~f:Int64.to_string)
  | _ -> print_endline "didn't pause");
  (match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | Exited _ -> print_endline "exited otherwise"
  | Failed msg -> print_endline ("failed: " ^ msg)
  | _ -> print_endline "not exited");
  if not !continued then failwith "no syscall continued to the next instruction";
  print_endline "syscall continued"
