#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu

let pause emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwithf "doesn't pause at %Lx" addr ()

let other_thread emu =
  let current = Emu.thread emu in
  List.find_exn (Emu.threads emu) ~f:(fun (thread : Emu.Checkpoint.thread) ->
      thread.tid <> current && Option.is_none thread.waiting)

let narrow_view emu tid =
  let regs = Emu.thread_regs emu tid in
  (not (List.Assoc.mem regs ~equal:String.equal "V0"))
  &&
  match List.Assoc.find regs ~equal:String.equal "R0" with
  | Some value -> Int64.(value = minus_one)
  | None -> false

let check_views emu active parked label =
  printf "%s: active %b, parked %b, full %b\n" label (narrow_view emu active)
    (narrow_view emu parked)
    (Word.bitwidth (Emu.reg_word emu "V0") = 128)

let engine_of_string = function "unicorn" -> `Unicorn | _ -> `Lifted

let test_checkpoint proj dir engine =
  let engine_name =
    if Poly.equal engine `Unicorn then "unicorn" else "lifted"
  in
  let emu = Emu.create ~engine proj in
  pause emu 0x2103f4L;
  let main = Emu.thread emu in
  let other = other_thread emu in
  printf "initial backtraces %b\n"
    (List.length (Emu.backtrace emu) = 2
    && List.length (Emu.backtrace emu ~thread:other.tid) = 2);
  let wide = Word.ones 128 in
  Emu.set_reg_word emu "V0" wide;
  if not (Word.equal wide (Emu.reg_word emu "V0")) then
    failwith "the active full-width register wasn't preserved";
  Emu.set_reg emu "R0" Int64.minus_one;
  Emu.resume_thread emu other.tid;
  if Emu.thread emu <> other.tid then failwith "didn't select the other thread";
  Emu.set_reg_word emu "V0" wide;
  if not (Word.equal wide (Emu.reg_word emu "V0")) then
    failwith "the other full-width register wasn't preserved";
  Emu.set_reg emu "R0" Int64.minus_one;
  if not (narrow_view emu other.tid) then
    failwith "the active wide register wasn't omitted";
  Emu.resume_thread emu main;
  check_views emu main other.tid "before save";
  let checkpoint =
    Filename.concat dir ("thread-regs-" ^ engine_name ^ ".ckpt")
  in
  Emu.save emu checkpoint;
  let restored = Emu.create ~engine ~restore:checkpoint proj in
  check_views restored main other.tid "after restore";
  let active_frames = List.length (Emu.backtrace restored) in
  printf "restored backtraces %b\n"
    (active_frames > 0
    && active_frames = List.length (Emu.backtrace restored ~thread:other.tid));
  match Emu.run restored with
  | Exited (Some 0) -> print_endline "restored outcome true"
  | _ -> print_endline "restored outcome false"

let test_timeout proj engine =
  let emu = Emu.create ~engine proj in
  pause emu 0x2103f4L;
  Emu.set_reg_word emu "V0" (Word.ones 128);
  let worker =
    List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "worker"
  in
  match Emu.drive emu worker ~args:[ 3L ] ~timeout:0.5 with
  | Parked { pc; _ } ->
      let other = other_thread emu in
      let active = Emu.thread_regs emu (Emu.thread emu) in
      let parked = Emu.thread_regs emu other.tid in
      let frames = List.length (Emu.backtrace emu) in
      printf "timeout outcome %b, backtraces %b, views %b\n"
        (List.mem [ worker; 0x210564L; 0x210568L ] pc ~equal:Int64.equal)
        (frames > 0
        && frames = List.length (Emu.backtrace emu ~thread:other.tid))
        ((not (List.Assoc.mem active ~equal:String.equal "V0"))
        && not (List.is_empty parked))
  | Returned _ -> print_endline "timeout returned unexpectedly"
  | Ended _ -> print_endline "timeout ended unexpectedly"

let () =
  match Bap_script.args () with
  | [ file; dir; engine ] ->
      let proj = Bap_script.project ~disassemble:true file in
      let engine = engine_of_string engine in
      test_checkpoint proj dir engine;
      test_timeout proj engine
  | _ -> failwith "expected FILE DIR ENGINE"
