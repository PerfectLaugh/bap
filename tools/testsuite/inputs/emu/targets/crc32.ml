#require "bap-primus-unicorn.emu"

module Emu = Bap_emu
module Sym = Emu.Symbolic
module Taint = Emu.Taint

let status = function
  | Emu.Exited c ->
      Printf.sprintf "exited %s"
        (match c with Some c -> string_of_int c | None -> "?")
  | Paused -> "paused"
  | Running -> "running"
  | Failed m -> "failed " ^ m

(* the program pauses, when it calls crc32 first, after it read both
   lines with fgets, whose first argument is the buffer *)
let () =
  match Bap_script.args () with
  | file :: input :: api ->
      let emu =
        Emu.create
          ~components:(Sym.components @ Taint.components)
          ~redirects:[ ("<stdin>", input) ]
          (Bap_script.project ~api file)
      in
      let buffers = ref [] and crcs = ref 0 in
      Emu.on_call emu "fgets" (fun emu ->
          buffers := Emu.arg emu 0 :: !buffers;
          Default);
      Emu.on_call emu "crc32" (fun emu ->
          incr crcs;
          if !crcs = 1 then Emu.stop emu;
          Default);
      let s = status (Emu.run emu) in
      Printf.printf "at crc32: %s after %d reads\n%!" s (List.length !buffers);
      let buf1 = List.nth !buffers 1 and buf2 = List.nth !buffers 0 in
      Printf.printf "buf1 %S, buf2 %S\n%!" (Emu.read emu buf1 4)
        (Emu.read emu buf2 4);
      Sym.symbolize emu (Mem (buf1, 4));
      Taint.introduce emu ~kind:"input" (Mem (buf1, 4));
      Printf.printf "symbolic: %s\n%!"
        (String.concat ""
           (List.map
              (function Some _ -> "S" | None -> "-")
              (Sym.formula emu (Mem (buf1, 5)))));
      Printf.printf "tainted: %b %b\n%!"
        (Taint.is_tainted emu ~kind:"input" (Mem (buf1, 4)))
        (Taint.is_tainted emu ~kind:"input" (Mem (buf2, 4)));
      let branches = ref [] and jumps = ref 0 in
      Sym.on_branch emu (fun _ b -> branches := b :: !branches);
      Taint.on_jump emu (fun _ ~kinds _ ->
          if List.mem "input" kinds then incr jumps);
      let s = status (Emu.run emu) in
      let crcs = !crcs in
      Printf.printf "%s, crc32 called %d times\n" s crcs;
      Printf.printf "symbolic branches: %b, tainted jumps: %b\n"
        (List.length !branches > 4)
        (!jumps > 4);
      (match Sym.flip ~timeout:30_000 (List.hd !branches) with
      | None -> print_endline "no collision"
      | Some m ->
          Printf.printf "collision %S\n"
            (String.concat ""
               (List.map
                  (fun (_, v) -> String.make 1 (Char.chr (Int64.to_int v)))
                  m)));
      Taint.sanitize emu ~kind:"input" (Mem (buf1, 4));
      Printf.printf "sanitized: %b\n"
        (Taint.is_tainted emu ~kind:"input" (Mem (buf1, 4)))
  | _ -> failwith "expected FILE INPUT [API]"
