#require "bap-primus-unicorn.emu"

module Emu = Bap_emu

(* bap script script.ml POLICY PROGRAM: taints in of taint-ops.c, at
   403080, at main, and prints the taint of the bytes of out, and of the arguments
   of mark, by the policy of the computations, [computation], or of the
   moves, [exact], which BAP_LIFTED_TAINT=false leaves to the
   interpreter *)
let addr emu name =
  match List.assoc_opt name (Emu.symbols emu) with
  | Some addr -> addr
  | None -> failwith ("no " ^ name)

let pause emu name =
  match Emu.run emu ~until:(addr emu name) with
  | Paused -> ()
  | _ -> failwith ("doesn't pause at " ^ name)

let kinds emu place =
  match Emu.Taint.kinds emu place with [] -> "-" | ks -> String.concat "," ks

let () =
  match Bap_script.args () with
  | [ policy; file ] -> (
      let components =
        match policy with
        | "exact" ->
            [
              "bap:propagate-taint-exact";
              "bap:select-propagate-taint-exact-policy";
            ]
        | _ -> Emu.Taint.components
      in
      let emu =
        Emu.create ~components (Bap_script.project ~disassemble:true file)
      in
      pause emu "main";
      Emu.Taint.introduce emu ~kind:"input" (Mem (0x403080L, 16));
      pause emu "mark";
      let out = 0x403040L in
      print_string "out:";
      for i = 0 to 27 do
        Printf.printf " %d=%s" i
          (kinds emu (Mem (Int64.(add out (of_int i)), 1)))
      done;
      print_newline ();
      List.iter
        (fun r -> Printf.printf "%s: %s\n" r (kinds emu (Reg r)))
        [ "RDI"; "RSI"; "RDX"; "RCX" ];
      match Emu.run emu with
      | Exited (Some 0) -> print_endline "exited"
      | _ -> print_endline "not exited")
  | _ -> failwith "usage: script.ml POLICY PROGRAM"
