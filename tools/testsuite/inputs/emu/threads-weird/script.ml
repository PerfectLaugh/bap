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
   of pingpong, if the SAVE is given

   and api=DIR, the api of the target, e.g., of PowerPC *)

let addr emu name =
  match List.assoc_opt name (Emu.symbols emu) with
  | Some addr -> addr
  | None -> failwith ("no " ^ name)

(* the target, by the name of the file, e.g., aarch64-linux-gnu-... *)
let target = ref ""

let starts prefix = String.starts_with ~prefix !target

(* the argument [n] of the mark, that the program paused at, at its
   entry, which is on the stack of x86 *)
let arg emu n =
  let reg prefix first = Emu.reg emu (Printf.sprintf "%s%d" prefix (first + n)) in
  if starts "x86_64" then Emu.reg emu [| "RDI"; "RSI"; "RDX" |].(n)
  else if starts "i686" then
    let data = Emu.read emu Int64.(add (Emu.reg emu "ESP") (of_int (4 + (4 * n)))) 4 in
    String.fold_right
      (fun c acc -> Int64.(logor (shift_left acc 8) (of_int (Char.code c))))
      data 0L
  else if starts "mips" then reg "R" 4
  else if starts "powerpc" then reg "R" 3
  else if starts "riscv" then reg "X" 10
  else reg "R" 0

let pause emu name =
  match Emu.run emu ~until:(addr emu name) with
  | Paused -> Printf.printf "%s in the thread %d\n%!" name (Emu.thread emu)
  | Failed msg -> failwith ("doesn't pause at " ^ name ^ ": " ^ msg)
  | Exited code ->
      failwith
        (Printf.sprintf "doesn't pause at %s: exited %s" name
           (match code with Some c -> string_of_int c | None -> "-"))
  | _ -> failwith ("doesn't pause at " ^ name)

let taint emu (name, addr) =
  let kinds = Emu.Taint.kinds emu (Mem (addr, 1)) in
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

(* the api of PowerPC, as api=DIR *)
let api =
  List.filter_map
    (fun arg ->
      if String.starts_with ~prefix:"api=" arg then
        Some (String.sub arg 4 (String.length arg - 4))
      else None)
    (Bap_script.args ())

let create ?restore file =
  target := Filename.basename file;
  Emu.create ~components:Emu.Taint.components ?restore
    (Bap_script.project ~api ~disassemble:true file)

let () =
  match
    List.filter
      (fun arg -> not (String.starts_with ~prefix:"api=" arg))
      (Bap_script.args ())
  with
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
