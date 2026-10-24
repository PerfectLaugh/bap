#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The context of the calls, and the memory, that they change: worker of
   spawn.c is called with a register, that the ABI doesn't pass, R12,
   which a hook sees at its entry, and the bytes, that it stored, out[1],
   are the ones, that differ from the snapshot, and from the checkpoint,
   which were stored, as the stack is generated, the code mapped, and
   the rest unmapped, see Emu.diff and Emu.provenance. In threads.c,
   worker is called in the context of another thread, whose callee-saved
   register R12 the hook sees, as each thread has its own. *)

let provenance emu addr =
  match Emu.provenance emu addr with
  | Stored -> "stored"
  | Generated -> "generated"
  | Mapped -> "mapped"
  | Unmapped -> "unmapped"

let ranges rs =
  String.concat ~sep:" " (List.map rs ~f:(fun (a, n) -> sprintf "%Lx+%d" a n))

let () =
  match Bap_script.args () with
  | [ spawn; threads; dir ] -> (
      let emu = Emu.create (Bap_script.project spawn) in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      ignore (Emu.run emu ~until:(addr "main") : Emu.status);
      let worker = addr "worker" in
      let snap = Emu.snapshot emu in
      let ckpt = Filename.concat dir "main.ckpt" in
      Emu.save emu ckpt;
      Emu.on_code emu ~first:worker ~last:worker (fun emu _ ->
          printf "worker sees R12 = %Lx\n%!" (Emu.reg emu "R12"));
      let r = Emu.call emu worker ~args:[ 1L ] ~regs:[ ("R12", 0x1234L) ] in
      printf "worker(1) = %s, R12 back %b\n%!"
        (Option.value_map r ~default:"none" ~f:Int64.to_string)
        Int64.(Emu.reg emu "R12" <> 0x1234L);
      (match Emu.call emu worker ~args:[ 1L ] ~regs:[ ("NOPE", 1L) ] with
      | exception Failure msg -> printf "%s\n" msg
      | _ -> print_endline "accepted an unknown register");
      let changed = Emu.diff emu snap in
      printf "diff %s\n" (ranges changed);
      printf "since the checkpoint %s\n" (ranges (Emu.changed_since emu ckpt));
      List.iter changed ~f:(fun (a, _) ->
          printf "%Lx %s\n" a (provenance emu a));
      let name = function
        | Emu.Stored -> "stored"
        | Generated -> "generated"
        | Mapped -> "mapped"
        | Unmapped -> "unmapped"
      in
      printf "changes %s\n"
        (String.concat ~sep:" "
           (List.map (Emu.changes emu snap) ~f:(fun c ->
                sprintf "%Lx+%d:%s>%s" c.addr c.size (name c.before)
                  (name c.after))));
      (* the arguments at the entry of worker, and the service of the
         calls, that a hook pauses *)
      let capture = Emu.Trace.capture emu [ worker ] ~regs:[ "RDI"; "RSI" ] in
      let stops = ref 0 in
      Emu.on_code emu ~first:worker ~last:worker (fun emu _ -> Emu.stop emu);
      let served = ref [] in
      let r =
        Emu.call emu worker ~args:[ 2L ] ~service:(fun emu pc ->
            incr stops;
            served := Int64.(pc land -2L = worker) :: !served)
      in
      printf "served %d pause(s) in worker %b, worker(2) = %s\n" !stops
        (List.for_all !served ~f:Fn.id)
        (Option.value_map r ~default:"none" ~f:Int64.to_string);
      printf "captured %Ld: %s\n"
        (Emu.Trace.captures capture)
        (String.concat ~sep:" "
           (List.map (Emu.Trace.captured capture) ~f:(fun (site, regs) ->
                sprintf "%s(%s)"
                  (if Int64.(site = worker) then "worker" else "?")
                  (String.concat ~sep:"," (List.map regs ~f:Int64.to_string)))));
      (* a region, that is allocated over the bytes, that were stored,
         replaces them, in Primus, and in Unicorn *)
      let out1 = List.hd_exn changed |> fst in
      printf "out[1] before the allocation %S\n" (Emu.read emu out1 1);
      Emu.primus emu
        (module functor
                  (Machine : Bap_primus.Std.Primus.Machine.S)
                  ->
                  struct
                    module Memory = Bap_primus.Std.Primus.Memory.Make (Machine)

                    let init () =
                      let a = Bap.Std.Word.of_int64 out1 in
                      Memory.add_region ~lower:a
                        ~upper:(Bap.Std.Word.nsucc a 15)
                        ~generator:(Bap_primus.Std.Primus.Generator.static 0)
                        ()
                  end);
      printf "out[1] after the allocation %S, %s\n" (Emu.read emu out1 1)
        (provenance emu out1);
      let sp = Emu.reg emu "RSP" in
      printf "the stack %s, the code %s, nowhere %s\n"
        (provenance emu Int64.(sp - 0x2000L))
        (provenance emu (addr "main"))
        (provenance emu 0x12L);
      ignore (Emu.read emu Int64.(sp - 0x2000L) 1 : string);
      printf "the stack, that was read, %s\n"
        (provenance emu Int64.(sp - 0x2000L));
      let emu = Emu.create (Bap_script.project threads) in
      ignore (Emu.run emu ~until:0x201537L : Emu.status);
      printf "paused in the thread %d, with %s\n" (Emu.thread emu)
        (String.concat ~sep:","
           (List.map (Emu.threads emu) ~f:(fun t -> Int.to_string t.tid)));
      let worker =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal "worker"
      in
      Emu.on_code emu ~first:worker ~last:worker (fun emu _ ->
          printf "worker sees R12 = %Lx\n%!" (Emu.reg emu "R12"));
      let r12 = Emu.reg emu "R12" in
      ignore (Emu.call emu worker ~args:[ 0L ] : int64 option);
      ignore (Emu.call emu worker ~args:[ 0L ] ~thread:1 : int64 option);
      ignore (Emu.call emu worker ~args:[ 0L ] ~thread:3 : int64 option);
      printf "R12 back %b\n" Int64.(Emu.reg emu "R12" = r12);
      match Emu.call emu worker ~args:[ 0L ] ~thread:9 with
      | exception Failure msg -> printf "%s\n" msg
      | _ -> print_endline "accepted an unknown thread")
  | _ -> failwith "expected SPAWN THREADS DIR"
