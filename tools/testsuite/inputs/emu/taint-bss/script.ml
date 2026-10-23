#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* bap script script.ml ENGINE PROGRAM: taints buf of taint-bss.c, at
   main, 4004b6, and prints the taint of the results at the call of
   printf, 40054b: the CRC of buf in RDX, and the number of its odd
   bytes in RCX, are tainted, and the other CRC in RSI isn't *)
let pause emu addr =
  match Emu.run emu ~until:addr with
  | Paused -> ()
  | _ -> failwith (Printf.sprintf "doesn't pause at %Lx" addr)

let () =
  match Bap_script.args () with
  | [ engine; file ] -> (
      let engine = if engine = "lifted" then `Lifted else `Unicorn in
      let emu =
        Emu.create ~engine ~components:Emu.Taint.components
          (Bap_script.project ~disassemble:true file)
      in
      pause emu 0x4004b6L;
      Emu.Taint.introduce emu ~kind:"input" (Mem (0x403040L, 256));
      pause emu 0x40054bL;
      List.iter
        (fun reg ->
          Printf.printf "%s: %s\n%!" reg
            (match Emu.Taint.kinds emu (Reg reg) with
            | [] -> "-"
            | kinds -> String.concat "," kinds))
        [ "RDX"; "RCX"; "RSI" ];
      match Emu.run emu with
      | Exited (Some 0) -> print_endline "exited"
      | _ -> print_endline "not exited")
  | _ -> failwith "usage: script.ml ENGINE PROGRAM"
