#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The static slices of print_strings of echo, at main, see
   Emu.Static.slice, from the instructions at the addresses of the cases,
   DIRECTION:ADDR:REGISTER, backward, b, or forward, f, of the register,
   or of what the instruction reads or writes, without the register,
   with and without the addresses: through the slots of the frame, which
   the code, compiled without optimizations, keeps the pointer in, and
   the loop, and its alias, e.g., X0 of R0 on AArch64, and up to the loads
   through the pointer, which aren't followed. *)

let loc = function Emu.Reg r -> r | Mem (a, n) -> sprintf "mem[%Lx:%d]" a n

let show name (s : Emu.Static.slice) =
  printf "%s: sites %s | live %s | calls %s | complete %b\n" name
    (String.concat ~sep:" " (List.map s.sites ~f:(sprintf "%Lx")))
    (String.concat ~sep:"," (List.map s.live ~f:loc))
    (String.concat ~sep:" " (List.map s.calls ~f:(sprintf "%Lx")))
    s.complete

let () =
  match Bap_script.args () with
  | file :: cases ->
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
      ignore
        (Emu.run emu
           ~until:
             (List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main")
          : Emu.status);
      let proj = Emu.project emu in
      List.iter cases ~f:(fun case ->
          match String.split case ~on:':' with
          | [ dir; addr; reg ] ->
              let addr = Int64.of_string ("0x" ^ addr) in
              let forward = String.is_prefix dir ~prefix:"f" in
              (* the digit after the direction is the depth of the calls *)
              let depth =
                if String.length dir > 1 then
                  Int.of_string (String.drop_prefix dir 1)
                else 0
              in
              let locs = if String.is_empty reg then [] else [ Emu.Reg reg ] in
              let dir =
                (if forward then "forward" else "backward")
                ^ if depth > 0 then sprintf " %d deep" depth else ""
              in
              show
                (sprintf "%s %s from %Lx" dir reg addr)
                (Emu.Static.slice ~forward ~depth proj addr locs);
              show
                (sprintf "%s %s from %Lx with addresses" dir reg addr)
                (Emu.Static.slice ~forward ~depth ~addresses:true proj addr locs)
          | _ -> failwithf "the case %s isn't DIRECTION:ADDR:REGISTER" case ())
  | _ -> failwith "expected FILE CASE..."
