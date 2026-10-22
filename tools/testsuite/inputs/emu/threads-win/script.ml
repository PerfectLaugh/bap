#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* The script of threads-win.c, which taints the turns of the events,
   whose page has the critical sections, the handles of the events, and
   the address of WaitOnAddress, which is not in Unicorn then, as it is
   tainted, and the seed, which the thread mixes, and saves the
   checkpoint, while the thread waits on an event, in
   WaitForSingleObject, which it calls again, when it is woken, also in
   the program, that continues from the checkpoint. The turns, that the
   program overwrites, are not tainted then.

   save: runs, and saves the checkpoint, events.ckpt
   restore: continues from the checkpoint *)

let wide = ref true

(* the argument [n] of the mark, at its entry *)
let arg emu n =
  if !wide then Emu.reg emu [| "RCX"; "RDX"; "R8" |].(n)
  else
    let sp = Emu.reg emu "ESP" in
    let data = Emu.read emu Int64.(add sp (of_int (4 + (4 * n)))) 4 in
    String.fold_right
      (fun c acc -> Int64.(logor (shift_left acc 8) (of_int (Char.code c))))
      data 0L

let taint emu (name, addr) =
  let kinds = Emu.Taint.kinds emu (Mem (addr, 1)) in
  Printf.printf "%s: %s\n%!" name
    (if kinds = [] then "-" else String.concat "," kinds)

let finish emu =
  match Emu.run emu with
  | Exited code ->
      Printf.printf "exited %s\n%!"
        (match code with Some c -> string_of_int c | None -> "-")
  | Failed msg -> Printf.printf "failed %s\n%!" msg
  | _ -> print_endline "not exited"

let create ?restore file =
  wide := String.starts_with ~prefix:"x86_64" (Filename.basename file);
  Emu.create ~components:Emu.Taint.components ?restore
    (Bap_script.project ~disassemble:true file)

let () =
  match Bap_script.args () with
  | [ file ] ->
      let emu = create file in
      let mark = List.assoc "win_waits" (Emu.symbols emu) in
      (match Emu.run emu ~until:mark with
      | Paused -> Printf.printf "paused in the thread %d\n%!" (Emu.thread emu)
      | _ -> failwith "doesn't pause at win_waits");
      let data = List.mapi (fun i name -> (name, arg emu i)) [ "turns"; "seed"; "mixed" ] in
      Emu.Taint.introduce emu ~kind:"secret" (Mem (arg emu 0, 4));
      Emu.Taint.introduce emu ~kind:"secret" (Mem (arg emu 1, 4));
      Emu.save emu "events.ckpt";
      Out_channel.with_open_text "data" (fun out ->
          List.iter (fun (n, a) -> Printf.fprintf out "%s %Ld\n" n a) data);
      print_endline "saved events.ckpt";
      finish emu;
      List.iter (taint emu) data
  | [ file; "restore" ] ->
      let emu = create ~restore:"events.ckpt" file in
      Printf.printf "restored in the thread %d\n%!" (Emu.thread emu);
      let data =
        In_channel.with_open_text "data" In_channel.input_lines
        |> List.map (fun line -> Scanf.sscanf line "%s %Ld" (fun n a -> (n, a)))
      in
      finish emu;
      List.iter (taint emu) data
  | _ -> failwith "usage: script.ml FILE [restore]"
