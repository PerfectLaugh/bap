#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let status = function
  | Emu.Exited c ->
      Printf.sprintf "exited %s"
        (match c with Some c -> string_of_int c | None -> "?")
  | Paused -> "paused"
  | Running -> "running"
  | Failed m -> "failed " ^ m

let () =
  match Bap_script.args () with
  | file :: api ->
      let emu =
        Emu.create
          ~args:[ "hello"; "cruel"; "world" ]
          (Bap_script.project ~api file)
      in
      let entry = Emu.pc emu in
      Printf.printf "registers: %b\n%!" (List.length (Emu.registers emu) > 16);
      let stepped = status (Emu.step emu) in
      Printf.printf "step: %s, moved %b\n%!" stepped (Emu.pc emu <> entry);
      (try ignore (Emu.arg emu 0)
       with Invalid_argument _ ->
         print_endline "no argument outside of a call");
      let chars = Buffer.create 64 and first = ref true in
      Emu.on_call emu "putchar" (fun emu ->
          let c =
            Char.chr (Int64.to_int (Int64.logand (Emu.arg emu 0) 0xffL))
          in
          (try Emu.write emu 0L "x"
           with Invalid_argument _ ->
             if !first then print_endline "no write in the hook");
          if !first then begin
            first := false;
            Emu.stop emu
          end;
          (* the program prints the vowels of the arguments, as Q *)
          if c = 'e' then Return 101L
          else begin
            Buffer.add_char chars c;
            Default
          end);
      Printf.printf "first putchar: %s\n%!" (status (Emu.run emu));
      let snapshot = Emu.snapshot emu in
      let s1 = status (Emu.run emu) in
      let out1 = Buffer.contents chars in
      Buffer.clear chars;
      Emu.restore emu snapshot;
      Printf.printf "restored: %s\n%!" (status (Emu.status emu));
      let s2 = status (Emu.run emu) in
      let replays =
        String.equal
          (String.sub out1 1 (String.length out1 - 1))
          (Buffer.contents chars)
      in
      Printf.printf "%s, %s, replays %b, exit code %s\n" s1 s2 replays
        (match Emu.exit_code emu with Some c -> string_of_int c | None -> "?");
      Printf.printf "printed %S\n" out1
  | _ -> failwith "expected FILE [API]"
