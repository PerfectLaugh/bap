#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The shell runs the commands of the debugger on the paused program,
   from a file here, whose lines it shows, and returns at q, after which
   the script goes on, with the breakpoints, that it set; from a hook, it
   opens at the pause, that the hook asks for. The program writes to a
   file, as its first string is the path of the binary. *)

let () =
  match Bap_script.args () with
  | [ echo; dir ] -> (
      Stdlib.Sys.chdir dir;
      let emu =
        Emu.create ~args:[ "hello" ]
          ~redirects:[ ("<stdout>", "shell.out") ]
          (Bap_script.project echo)
      in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      ignore (Emu.run emu ~until:(addr "main") : Emu.status);
      Emu.set_snapshot_limit emu (Some 1);
      let commands name lines =
        Out_channel.write_lines name lines;
        In_channel.create name
      in
      let input =
        commands "shell.cmd"
          [
            "pc";
            "b print_endline";
            "b 0x400727";
            "breaks";
            "c";
            "x RSP 8";
            "s 2";
            "reg RDI";
            "set RSI RDI";
            "reg RSI";
            "snap";
            "snap";
            "c print_strings";
            "c";
            "x RDI 16";
            "restore";
            "reg RDI";
            "d 0x400727";
            "d print_endline";
            "breaks";
            "write RDI 0x4e 0x4f 0x57";
            "x RDI 3";
            "origin RDI";
            "origin main";
            "insn main";
            "lifted main";
            "bir main";
            "sym print";
            "regions";
            "call print_endline RDI";
            "save shell.ckpt";
            "nonsense";
            "x nowhere";
            "x 0x12";
            "q";
            "pc";
          ]
      in
      (match Emu.shell ~input emu with
      | Paused -> printf "left the shell, paused at %Lx\n" (Emu.pc emu)
      | _ -> print_endline "left the shell, not paused");
      printf "the checkpoint is at the pause %b\n"
        Int64.((Emu.Checkpoint.info "shell.ckpt").pc = Emu.pc emu);
      (* from a hook, at the pause before the hooked instruction, after
         which the program goes on; main calls print_strings once, which
         already runs, so the hook is at the return from it *)
      let input = commands "hook.cmd" [ "pc"; "reg RDI"; "q" ] in
      let return = 0x40094dL in
      Emu.on_code emu ~first:return ~last:return (fun emu _ ->
          match Emu.shell ~input ~prompt:"(hook) " emu with
          | Running -> print_endline "the shell opens at the pause"
          | _ -> print_endline "the shell didn't wait for the pause");
      Emu.restore emu (Emu.snapshot emu);
      match Emu.run emu with
      | Exited (Some 0) -> print_endline "exited 0"
      | _ -> print_endline "didn't exit 0")
  | _ -> failwith "expected ECHO DIR"
