#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The script observes, what the program does outside of the hooks of
   the engine, see Emu.on_write ~primus, the read stub of files.c, that
   stores the tail of the file, scopes its hooks, see Emu.scoped, hooks
   the sites of the functions with one hook, see Emu.on_sites, which sees,
   what their hooks of the code see, and tells, why a call in a hook
   can't run, and where the program, that ran into an instruction,
   whose intrinsic is unbound, failed, of UDF of AArch64. *)

let () =
  match Bap_script.args () with
  | [ files; arm; input; dir; engine ] -> (
      let engine =
        if String.equal engine "unicorn" then `Unicorn else `Lifted
      in
      let proj = Bap_script.project files in
      let create () =
        Emu.create ~engine
          ~redirects:
            [ ("/data/input", input); ("<stdout>", Filename.concat dir "out") ]
          proj
      in
      (* the read stub stores the bytes, that the engine doesn't see *)
      let emu = create () in
      let buf = ref None in
      Emu.on_call emu "read" (fun emu ->
          buf := Some (Emu.arg emu 1);
          Default);
      let tail addr =
        match !buf with
        | Some b -> Int64.(addr >= b && addr < b + 4L)
        | None -> false
      in
      let engine_stores = ref 0 and stores = Buffer.create 16 in
      Emu.on_write emu (fun _ addr _ _ -> if tail addr then incr engine_stores);
      Emu.on_write emu ~primus:true (fun _ addr size value ->
          if tail addr then bprintf stores " %d:%02Lx" size value);
      ignore (Emu.run emu : Emu.status);
      printf "the engine stored %d bytes of the tail, all stores:%s\n"
        !engine_stores (Buffer.contents stores);
      (* the hooks of the scope are gone after it *)
      let emu = create () in
      let main =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "main"
      in
      let seen = ref 0 and lseeks = ref 0 in
      Emu.scoped emu (fun () ->
          Emu.on_code emu (fun _ _ -> incr seen);
          Emu.on_call emu "lseek" (fun _ ->
              incr lseeks;
              Default);
          ignore (Emu.run emu ~until:main : Emu.status));
      let before = !seen in
      ignore (Emu.run emu : Emu.status);
      printf "the scope saw %b, after it %d instructions and %d calls\n"
        (before > 0) (!seen - before) !lseeks;
      (* one hook of the sites sees, what a hook of each site sees *)
      let sites = List.map (Emu.symbols (create ())) ~f:snd in
      let hits f =
        let emu = create () in
        let n = ref 0 in
        f emu (fun _ _ -> incr n);
        ignore (Emu.run emu : Emu.status);
        !n
      in
      let each =
        hits (fun emu f ->
            List.iter sites ~f:(fun s -> Emu.on_code emu ~first:s ~last:s f))
      in
      let one = hits (fun emu f -> Emu.on_sites emu sites f) in
      printf "the sites are seen %b, as by their hooks %b\n" (one > 0)
        (one = each);
      (* the call in a hook *)
      let emu = create () in
      Emu.on_code emu ~first:main ~last:main (fun emu _ ->
          (match Emu.call emu main with
          | exception Invalid_argument msg -> print_endline msg
          | _ -> print_endline "called in the hook");
          Emu.stop emu);
      ignore (Emu.run emu : Emu.status);
      (* the unbound intrinsic of UDF, at the address of the entry *)
      let emu = Emu.create ~engine (Bap_script.project arm) in
      Emu.write emu (Emu.pc emu) "\x00\x00\x00\x00";
      (match Emu.run emu with
      | Failed msg -> printf "failed: %s\n" msg
      | _ -> print_endline "didn't fail");
      match Emu.call emu 0x1000L with
      | exception Invalid_argument msg -> print_endline msg
      | _ -> print_endline "called after the failure")
  | _ -> failwith "expected FILES ARM INPUT DIR ENGINE"
