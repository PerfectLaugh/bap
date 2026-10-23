#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* bap script script.ml PROGRAM: taints the 9 bytes of src of
   taint-natives.c, at 403160, at ready, and prints the taint of the 18
   bytes of the copies, at mark: of memcpy, at 403120, of memset, at
   4030e0, of strcpy, at 4030a0, and of memmove, at 403060 *)
let sym emu name = List.assoc name (Emu.symbols emu)

let kinds emu place =
  match Emu.Taint.kinds emu place with [] -> "-" | ks -> String.concat "," ks

let pause emu name =
  match Emu.run emu ~until:(sym emu name) with
  | Paused -> ()
  | _ -> failwith ("doesn't pause at " ^ name)

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create ~components:Emu.Taint.components
      (Bap_script.project ~disassemble:true file)
  in
  pause emu "ready";
  Emu.Taint.introduce emu ~kind:"input" (Mem (0x403160L, 9));
  pause emu "mark";
  List.iter
    (fun (name, dst) ->
      Printf.printf "%s:" name;
      for i = 0 to 17 do
        Printf.printf " %s" (kinds emu (Mem (Int64.(add dst (of_int i)), 1)))
      done;
      print_newline ())
    [
      ("memcpy", 0x403120L);
      ("memset", 0x4030e0L);
      ("strcpy", 0x4030a0L);
      ("memmove", 0x403060L);
    ];
  match Emu.run emu with
  | Exited (Some 0) -> print_endline "exited"
  | _ -> print_endline "not exited"
