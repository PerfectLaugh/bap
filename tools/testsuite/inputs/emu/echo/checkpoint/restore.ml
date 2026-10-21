#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create ~restore:"echo.ckpt" (Bap_script.project file)
  in
  Printf.printf "restored at %Lx, RDI = %Ld\n%!" (Emu.pc emu)
    (Emu.reg emu "RDI");
  Printf.printf "say at %Lx\n%!" (List.assoc "say" (Emu.symbols emu));
  let calls = ref 0 in
  Emu.on_call emu "say" (fun _ ->
      incr calls;
      Default);
  match Emu.run emu with
  | Exited c ->
      Printf.printf "exited %s, say was called %d times\n"
        (match c with Some c -> string_of_int c | None -> "?")
        !calls
  | Failed m -> print_endline ("failed " ^ m)
  | _ -> print_endline "not exited"
