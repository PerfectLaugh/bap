#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* The thread 2 of threads.c has its argument in R8, at 201513, which
   it reads, after it waits for main, at 201537, while the threads
   switch. The script taints R8 of the thread 2, saves the checkpoint,
   while main runs, and the thread 2 doesn't, and checks, that R8 keeps
   its taint in the thread 2 only, also in the restored program, see
   restore.ml. *)

let pause emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwith (Printf.sprintf "doesn't pause at %Lx" addr)

let check emu =
  for _ = 1 to 4 do
    pause emu 0x201537L;
    Printf.printf "R8 of the thread %d: %s\n%!" (Emu.thread emu)
      (match Emu.Taint.kinds emu (Reg "R8") with
      | [] -> "-"
      | kinds -> String.concat "," kinds)
  done

let finish emu =
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | _ -> print_endline "not exited"

let () =
  let file = List.hd (Bap_script.args ()) in
  if List.length (Bap_script.args ()) = 1 then begin
    let emu =
      Emu.create ~components:Emu.Taint.components
        (Bap_script.project ~disassemble:true file)
    in
    pause emu 0x201513L;
    Printf.printf "tainted in the thread %d\n%!" (Emu.thread emu);
    Emu.Taint.introduce emu ~kind:"input" (Reg "R8");
    pause emu 0x2013e0L;
    Emu.save emu "threads.ckpt";
    Printf.printf "saved in the thread %d\n%!" (Emu.thread emu);
    check emu;
    finish emu
  end
  else
    let emu =
      Emu.create ~components:Emu.Taint.components ~restore:"threads.ckpt"
        (Bap_script.project ~disassemble:true file)
    in
    Printf.printf "restored in the thread %d\n%!" (Emu.thread emu);
    check emu;
    finish emu
