#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

let show emu = function
  | Emu.Paused -> Printf.printf "paused at %Lx\n%!" (Emu.pc emu)
  | Exited c ->
      Printf.printf "exited %s\n%!"
        (match c with Some c -> string_of_int c | None -> "?")
  | Failed m -> Printf.printf "failed %s\n%!" m

let () =
  let file = List.hd (Bap_script.args ()) in
  let emu =
    Emu.create ~args:[ "hello"; "cruel" ] (Bap_script.project file)
  in
  (* three steps from the entry *)
  for _ = 1 to 3 do
    show emu (Emu.step emu)
  done;
  (* the first instruction of print_strings stops the program, which
     continues from there, as the hook doesn't see it again *)
  Emu.on_code emu ~first:0x400733L ~last:0x400733L (fun emu _ -> Emu.stop emu);
  show emu (Emu.run emu);
  (* print_endline, a function of the program, prints nothing for the
     arguments, but the strings of the program *)
  let calls = ref 0 in
  Emu.on_call emu "print_endline" (fun _ ->
      incr calls;
      if !calls <= 3 then Return 0L else Default);
  show emu (Emu.run emu);
  Printf.printf "print_endline was called %d times\n" !calls
