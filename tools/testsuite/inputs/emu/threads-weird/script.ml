#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* The script of threads-weird.c, which taints the secret, that main
   passes to the mixer, a thread, in a register, through clone, and the
   mixer mixes into the memory, after it waited on a futex, and saves
   the checkpoints: while the mixer waits, in main, and while the threads
   take turns, in one of them, also in the program, that continues from
   a checkpoint, so that the checkpoint of the checkpoint keeps the
   taint and the threads too, and after main exited.

   save: runs, and saves the checkpoints, mixer.ckpt, pingpong.ckpt, and
   orphan.ckpt, after main exited
   restore FILE [SAVE]: continues from the checkpoint, and saves the one
   of pingpong, if the SAVE is given *)

let addr emu name =
  match List.assoc_opt name (Emu.symbols emu) with
  | Some addr -> addr
  | None -> failwith ("no " ^ name)

(* the argument [n] of the mark, that the program paused at *)
let arg emu n =
  let regs =
    if List.mem "RDI" (Emu.registers emu) then [| "RDI"; "RSI"; "RDX" |]
    else [| "R0"; "R1"; "R2" |]
  in
  Emu.reg emu regs.(n)

let pause emu name =
  match Emu.run emu ~until:(addr emu name) with
  | Paused -> Printf.printf "%s in the thread %d\n%!" name (Emu.thread emu)
  | _ -> failwith ("doesn't pause at " ^ name)

let taint emu (name, addr) =
  let kinds = Emu.Taint.kinds emu (Mem (addr, 8)) in
  Printf.printf "%s: %s\n%!" name
    (if kinds = [] then "-" else String.concat "," kinds)

let joined emu =
  pause emu "taint_joined";
  let data = [ "inherited"; "mixed"; "clean" ] in
  let data = List.mapi (fun i name -> (name, arg emu i)) data in
  List.iter (taint emu) data;
  data

(* the addresses of the data, for the restored programs *)
let store data =
  Out_channel.with_open_text "data" (fun out ->
      List.iter (fun (name, addr) -> Printf.fprintf out "%s %Ld\n" name addr) data)

let load () =
  In_channel.with_open_text "data" In_channel.input_lines
  |> List.map (fun line -> Scanf.sscanf line "%s %Ld" (fun n a -> (n, a)))

let finish emu data =
  (match Emu.run emu with
  | Exited code ->
      Printf.printf "exited %s\n%!"
        (match code with Some c -> string_of_int c | None -> "-")
  | _ -> print_endline "not exited");
  List.iter (taint emu) data

let create ?restore file =
  Emu.create ~components:Emu.Taint.components ?restore
    (Bap_script.project ~disassemble:true file)

let () =
  match Bap_script.args () with
  | [ file ] ->
      let emu = create file in
      pause emu "taint_started";
      Emu.Taint.introduce emu ~kind:"secret" (Mem (arg emu 0, 16));
      pause emu "mixer_waits";
      Emu.save emu "mixer.ckpt";
      print_endline "saved mixer.ckpt";
      let data = joined emu in
      store data;
      pause emu "pinged";
      Emu.save emu "pingpong.ckpt";
      print_endline "saved pingpong.ckpt";
      pause emu "orphaned";
      Emu.save emu "orphan.ckpt";
      print_endline "saved orphan.ckpt";
      finish emu data
  | [ file; "restore"; ckpt ] | [ file; "restore"; ckpt; _ ] as args ->
      let emu = create ~restore:ckpt file in
      Printf.printf "restored %s in the thread %d\n%!" ckpt (Emu.thread emu);
      let data = if ckpt = "mixer.ckpt" then joined emu else load () in
      if List.length args = 4 then begin
        pause emu "pinged";
        Emu.save emu (List.nth args 3);
        Printf.printf "saved %s\n%!" (List.nth args 3)
      end;
      finish emu data
  | _ -> failwith "usage: script.ml FILE [restore CKPT [SAVE]]"
