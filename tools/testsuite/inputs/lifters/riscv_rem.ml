#require "bap-primus-native.emu"

(* REM of RISC-V is the truncating remainder, whose sign follows the dividend,
   which BIL, whose SMOD is the modulus, has not. See the M extension of the
   unprivileged specification: x rem 0 = x, and min rem -1 = 0. *)

module Emu = Bap_emu

let min_int64 = Int64.min_int

let table =
  [
    (-5L, 3L, -2L);
    (5L, -3L, 2L);
    (-5L, -3L, -2L);
    (5L, 3L, 2L);
    (-6L, 3L, 0L);
    (7L, 0L, 7L);
    (-7L, 0L, -7L);
    (min_int64, -1L, 0L);
    (-1L, min_int64, -1L);
  ]

let run name engine interpret file =
  let emu = Emu.create ~engine (Bap_script.project ~disassemble:true file) in
  let pc = Emu.pc emu in
  (* rem a0, a1, a2 *)
  Emu.write emu pc "\x33\xe5\xc5\x02";
  List.iter
    (fun (x, y, expected) ->
      Emu.set_reg emu "X11" x;
      Emu.set_reg emu "X12" y;
      Emu.set_pc emu pc;
      (match if interpret then Emu.interpret emu else Emu.step emu with
      | Emu.Paused -> ()
      | Emu.Running -> failwith (name ^ " is running")
      | Emu.Exited _ -> failwith (name ^ " exited")
      | Emu.Failed message -> failwith (name ^ ": " ^ message));
      let result = Emu.reg emu "X10" in
      if result <> expected then
        failwith
          (Printf.sprintf "%s: %Ld rem %Ld = %Ld, not %Ld" name x y result
             expected))
    table;
  Printf.printf "%s: rem passed\n" name

let () =
  match Bap_script.args () with
  | [ file ] ->
      run "primus" `Unicorn true file;
      run "lifted" `Lifted false file
  | _ -> failwith "usage: riscv_rem.ml PROGRAM"
