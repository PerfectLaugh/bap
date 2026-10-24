#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu
module Xrefs = Emu.Xrefs

(* The cross references of echo, at main, see Emu.Xrefs: the callers of
   its functions, the callees of main, the references to the slot of
   .bss, that __do_global_dtors_aux loads and stores, through the
   address, that adrp and add build on AArch64, and the jumps of the PLT
   stubs through their slots of GOT, to the trampolines of the external
   functions, which the slots hold in the emulator. *)

let kind = function
  | Xrefs.Call -> "call"
  | Jump -> "jump"
  | Load -> "load"
  | Store -> "store"
  | Address -> "addr"

let () =
  match Bap_script.args () with
  | [ file; slot ] ->
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project file) in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      ignore (Emu.run emu ~until:(addr "main") : Emu.status);
      let xrefs = Xrefs.create (Emu.project emu) in
      let name a =
        Option.value (Xrefs.name xrefs a) ~default:(sprintf "%Lx" a)
      in
      let names addrs = String.concat ~sep:" " (List.map addrs ~f:name) in
      List.iter [ "print_endline"; "print_strings"; "main" ] ~f:(fun f ->
          printf "%s: callers %s\n" f (names (Xrefs.callers xrefs (addr f))));
      printf "main calls %s\n" (names (Xrefs.callees xrefs (addr "main")));
      let show x =
        printf "  %Lx %s %Lx%s in %s\n" x.Xrefs.site (kind x.kind) x.target
          (Option.value_map x.slot ~default:"" ~f:(sprintf " via %Lx"))
          (Option.value_map
             (Xrefs.function_of xrefs x.site)
             ~default:"?" ~f:name)
      in
      printf "to %s:\n" slot;
      List.iter (Xrefs.find xrefs (Int64.of_string slot)) ~f:show;
      (* the stub of the PLT is a function of the project, not of the
         bare program, whose external functions have no addresses *)
      let strlen =
        List.find_exn (Xrefs.functions xrefs) ~f:(fun f ->
            Option.equal String.equal (Xrefs.name xrefs f) (Some "strlen"))
      in
      printf "strlen:\n";
      List.iter (Xrefs.of_function xrefs strlen) ~f:show;
      printf "to main:\n";
      List.iter (Xrefs.find xrefs (addr "main")) ~f:show
  | _ -> failwith "expected FILE SLOT"
