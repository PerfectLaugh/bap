#require "bap-primus-native.emu"

open Core
open Bap.Std
module Emu = Bap_emu
module Xrefs = Emu.Xrefs

(* The project of the memory of echo, and its cross references, are
   saved, and loaded, with the digest of the code, so that the next
   script skips the disassembly, see Emu.save_project and Xrefs.save,
   and the analyses work on the loaded project. The calls of the trace
   join the references, see Xrefs.add_calls, once each. *)

let () =
  match Bap_script.args () with
  | [ echo; dir ] ->
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      ignore (Emu.run emu ~until:(addr "main") : Emu.status);
      (* the calls of main before print_strings, in the trace *)
      let trace = Emu.Trace.start ~blocks:true emu in
      let digest = Emu.code_digest emu in
      let proj = Emu.project emu in
      printf "the project is of the code %b\n"
        (Option.equal String.equal (Emu.project_digest proj) (Some digest));
      let file = Filename.concat dir "echo.proj" in
      Emu.save_project proj file;
      let loaded = Emu.load_project file in
      printf "loaded: of the code %b, %d of %d subs, %d of %d regions\n"
        (Option.equal String.equal (Emu.project_digest loaded) (Some digest))
        (Term.length sub_t (Project.program loaded))
        (Term.length sub_t (Project.program proj))
        (Sequence.length (Memmap.to_sequence (Project.memory loaded)))
        (Sequence.length (Memmap.to_sequence (Project.memory proj)));
      printf "loaded: %d of %d instructions, symbols %b, disassembled %b\n"
        (Sequence.length (Disasm.insns (Project.disasm loaded)))
        (Sequence.length (Disasm.insns (Project.disasm proj)))
        (Option.is_some
           (Symtab.find_by_name (Project.symbols loaded) "print_strings"))
        (Project.disassembled loaded);
      (match Emu.load_project echo with
      | exception Failure _ -> print_endline "the program isn't a saved project"
      | _ -> print_endline "loaded the program as a project");
      (* the cache of the project loads it, if the code is the same *)
      let cached = Filename.concat dir "echo.cache" in
      let t0 = Caml_unix.gettimeofday () in
      ignore (Emu.project emu ~cache:cached : Project.t);
      let built = Caml_unix.gettimeofday () -. t0 in
      let t0 = Caml_unix.gettimeofday () in
      let again = Emu.project emu ~cache:cached in
      let loaded_again = Caml_unix.gettimeofday () -. t0 in
      printf "the cache is of the code %b, and loads faster %b\n"
        (Option.equal String.equal (Emu.project_digest again) (Some digest))
        Float.(loaded_again < built);
      let main = addr "main" in
      let only_main (r : Emu.region) =
        Int64.(r.executable && r.lower <= main && main <= r.upper)
      in
      let scoped_digest = Emu.code_digest ~regions:only_main emu in
      let scoped = Emu.project ~regions:only_main ~cache:cached emu in
      let scoped_file = Filename.concat dir "scoped.proj" in
      Emu.save_project scoped scoped_file;
      let loaded_scoped = Emu.load_project scoped_file in
      printf "scoped cache: of its code %b, %d of %d subs, %d of %d regions\n"
        (Option.equal String.equal
           (Emu.project_digest loaded_scoped)
           (Some scoped_digest))
        (Term.length sub_t (Project.program scoped))
        (Term.length sub_t (Project.program proj))
        (Sequence.length (Memmap.to_sequence (Project.memory loaded_scoped)))
        (Sequence.length (Memmap.to_sequence (Project.memory proj)));
      let full = Emu.project ~cache:cached emu in
      printf "the scoped cache didn't change the full project %b\n"
        (Option.equal String.equal (Emu.project_digest full) (Some digest));
      let xrefs = Xrefs.create loaded in
      let xfile = Filename.concat dir "echo.xrefs" in
      Xrefs.save xrefs xfile;
      let xrefs = Xrefs.load loaded xfile in
      printf "xrefs %d, print_endline is called by %s\n"
        (List.length (Xrefs.all xrefs))
        (String.concat ~sep:","
           (List.map
              (Xrefs.callers xrefs (addr "print_endline"))
              ~f:(fun f -> Option.value (Xrefs.name xrefs f) ~default:"?")));
      let focused = Xrefs.create_focused loaded (addr "print_endline") in
      printf "focused: %d functions, print_endline is called by %s\n"
        (List.length (Xrefs.functions focused))
        (String.concat ~sep:","
           (List.map
              (Xrefs.callers focused (addr "print_endline"))
              ~f:(fun f -> Option.value (Xrefs.name focused f) ~default:"?")));
      (match Xrefs.load scoped xfile with
      | exception Failure _ -> print_endline "stale xrefs are rejected"
      | _ -> print_endline "stale xrefs are accepted");
      let s =
        Emu.Static.slice loaded 0x400764L [ Emu.Reg "RAX" ] ~addresses:true
      in
      printf "the slice of the loaded project %s\n"
        (String.concat ~sep:" " (List.map s.sites ~f:(sprintf "%Lx")));
      (* the patch of the program changes the digest *)
      Emu.write emu 0x400727L "\xbf\x2b";
      printf "the patched code is of the project %b\n"
        (String.equal (Emu.code_digest emu) digest);
      ignore (Emu.run emu ~until:(addr "print_strings") : Emu.status);
      let calls = Emu.Trace.calls trace in
      (* the stub of strlen is a function of the project, not of the bare
         program, whose external functions have no addresses *)
      let strlen =
        List.find_exn (Xrefs.functions xrefs) ~f:(fun f ->
            Option.equal String.equal (Xrefs.name xrefs f) (Some "strlen"))
      in
      let before = List.length (Xrefs.find xrefs strlen) in
      Xrefs.add_calls xrefs calls;
      Xrefs.add_calls xrefs calls;
      printf "strlen: %d references, %d with the %d calls of the trace\n" before
        (List.length (Xrefs.find xrefs strlen))
        (List.length calls);
      Xrefs.add_calls xrefs [ (0x400753L, [ (strlen, 1) ]) ];
      printf "with a call of a dispatcher: %d, from %s\n"
        (List.length (Xrefs.find xrefs strlen))
        (String.concat ~sep:","
           (List.map (Xrefs.callers xrefs strlen) ~f:(fun f ->
                Option.value (Xrefs.name xrefs f) ~default:"?")));
      Xrefs.save xrefs xfile;
      let restored = Xrefs.load loaded xfile in
      printf "restored dynamic calls: %d, from %s\n"
        (List.length (Xrefs.find restored strlen))
        (String.concat ~sep:","
           (List.map (Xrefs.callers restored strlen) ~f:(fun f ->
                Option.value (Xrefs.name restored f) ~default:"?")))
  | _ -> failwith "expected ECHO DIR"
