#require "bap-primus-native.emu"

open Core
open Bap.Std
open Bap_primus.Std
module Emu = Bap_emu

let show emu addr =
  match Emu.bir emu addr with
  | None -> printf "%Lx: not an instruction\n" addr
  | Some (size, blks) ->
      printf "%Lx: %d bytes\n" addr size;
      List.iter blks ~f:(fun b -> print_endline (Blk.to_string b))

let () =
  match Bap_script.args () with
  | [ echo; thumb; mprotect; aarch64 ] -> (
      let emu = Emu.create ~args:[ "hello" ] (Bap_script.project echo) in
      show emu (Emu.pc emu);
      (* in a hook, where the program runs, at the address of the code *)
      let n = ref 0 in
      Emu.on_code emu (fun emu addr ->
          incr n;
          if !n = 2 then (
            printf "hook ";
            show emu addr));
      ignore (Emu.run emu ~until:0x40076bL);
      show emu 0x40076bL;
      (* the patched code is lifted anew, mov $0xa, %edi becomes mov $0x2b *)
      show emu 0x400727L;
      Emu.write emu 0x400727L "\xbf\x2b";
      show emu 0x400727L;
      (* the Thumb code of ARM, by the lower bit of the address *)
      let arm = Emu.create (Bap_script.project thumb) in
      printf "thumb pc %Lx\n" (Emu.pc arm);
      show arm (Emu.pc arm);
      (* the IT instruction, it eq, lifted itself, leaves the decoder
         out of its block, so the instruction after the block, subs r3,
         #1, lifted next, has no condition, and the member of the block,
         lsreq r2, r4, #1, lifted before the IT instruction, has its
         condition *)
      show arm 0x2028bL;
      show arm 0x2028fL;
      show arm 0x2028dL;
      (* the halfword, that looks like an IT instruction, it eq, but is
         the second one of a 32-bit instruction, that was lifted, ldr.w
         r11, [r0, #0xf08], written over eor.w r2, r1, r4, lsr #1, is
         not one, so lsls r5, r4, #31 after it has no condition *)
      Emu.write arm 0x20284L "\xd0\xf8\x08\xbf";
      show arm 0x20285L;
      show arm 0x20289L;
      (* the code, that the program writes to its buffer at 0x405000, is
         lifted from its bytes, the zeros before, mov $42, %eax after *)
      let code = 0x405000L in
      let emu = Emu.create (Bap_script.project mprotect) in
      printf "unwritten ";
      show emu code;
      Emu.on_code emu ~first:code ~last:code (fun emu addr ->
          printf "written hook ";
          show emu addr);
      ignore (Emu.run emu ~until:code);
      printf "written ";
      show emu (Emu.pc emu);
      (* a synthetic AArch64 stub returns to the caller of Emu.call *)
      let emu = Emu.create (Bap_script.project aarch64) in
      let stub = Emu.pc emu in
      Emu.write emu stub (Emu.AArch64.bytes Emu.AArch64.ret);
      (match Emu.call emu stub ~args:[ 42L ] with
      | Some 42L -> print_endline "synthetic AArch64 stub returned 42"
      | result ->
          failwithf "synthetic AArch64 stub returned %s"
            (Option.value_map result ~default:"nothing" ~f:Int64.to_string)
            ());
      (* a backward B at the edge of its signed range crosses allocated
         high pages and returns with the argument unchanged *)
      let branch = 0x50001000L and target = 0x48001000L in
      Emu.primus emu
        (module functor
                  (Machine : Primus.Machine.S)
                  ->
                  struct
                    open Machine.Syntax
                    module Memory = Primus.Memory.Make (Machine)

                    let init () =
                      let addr = Word.of_int64 ~width:64 in
                      let allocate pc =
                        Memory.allocate (addr pc) 0x1000 >>= fun () ->
                        Memory.protect ~lower:(addr pc)
                          ~upper:(addr Int64.(pc + 0xfffL))
                          {
                            readable = true;
                            writable = true;
                            executable = true;
                          }
                      in
                      allocate branch >>= fun () -> allocate target
                  end);
      Emu.write emu branch (Emu.AArch64.bytes (Emu.AArch64.b ~pc:branch target));
      Emu.write emu target (Emu.AArch64.bytes Emu.AArch64.ret);
      let pcs = ref [] in
      Emu.on_code emu (fun _ pc -> pcs := pc :: !pcs);
      (match Emu.call emu branch ~args:[ 42L ] with
      | Some 42L -> ()
      | result ->
          failwithf "high backward B returned %s"
            (Option.value_map result ~default:"nothing" ~f:Int64.to_string)
            ());
      let pcs = List.rev !pcs in
      if not (List.equal Int64.equal pcs [ branch; target ]) then
        failwithf "high backward B PCs: %s"
          (String.concat ~sep:"," (List.map pcs ~f:(sprintf "%Lx")))
          ();
      print_endline "high backward B returned 42 via 50001000,48001000";
      (* an inner call restores the active outer stack, whose call resumes *)
      Emu.write emu stub (Emu.AArch64.bytes Emu.AArch64.ret);
      let paused = ref false in
      Emu.on_code emu ~first:target ~last:target (fun emu _ ->
          if not !paused then (
            paused := true;
            Emu.stop emu));
      (match Emu.call emu branch ~args:[ 41L ] with
      | None when Int64.(Emu.pc emu = target) -> ()
      | _ -> failwith "outer call did not pause at its branch target");
      let outer = (Emu.execution_stats emu).stack in
      (match Emu.call emu stub ~args:[ 42L ] with
      | Some 42L -> ()
      | _ -> failwith "inner call did not return 42");
      if not (Poly.equal outer (Emu.execution_stats emu).stack) then
        failwith "inner call replaced the active outer stack stats";
      (match Emu.run emu with
      | Paused when Option.equal Int64.equal (Emu.returned emu) (Some 41L) ->
          print_endline "nested emulated calls restored outer stack and result"
      | _ -> failwith "outer call did not resume and return 41");
      if not (Poly.equal outer (Emu.execution_stats emu).stack) then
        failwith "outer call did not become the most recent stack stats";
      (* the reserved entry room itself exceeds a tiny call stack, and the
         failed call leaves the emulator usable and its stack stats behind *)
      let emu = Emu.create (Bap_script.project aarch64) in
      let stub = Emu.pc emu in
      Emu.write emu stub (Emu.AArch64.bytes Emu.AArch64.ret);
      (match Emu.call emu stub ~stack:16 with
      | _ -> failwith "the 16-byte emulated call stack unexpectedly worked"
      | exception Failure msg ->
          if
            not
              (String.is_substring msg
                 ~substring:"emulated call stack exhausted")
          then failwithf "unexpected tiny-stack error: %s" msg ();
          if not (String.is_substring msg ~substring:(sprintf "0x%Lx" stub))
          then failwithf "tiny-stack error has no current PC: %s" msg ();
          print_endline "tiny emulated call stack reported exhaustion");
      let stats = (Emu.execution_stats emu).stack in
      (match stats with
      | Some { lowest_sp; lower; upper; _ }
        when Int64.(lowest_sp = lower - 48L && upper - lower = 16L) ->
          ()
      | _ -> failwith "tiny-stack stats were not retained");
      Emu.set_reg emu "X0" 42L;
      (match Emu.drive emu stub ~stack:4096 with
      | Returned 42L -> ()
      | _ -> failwith "valid call after stack exhaustion did not return 42");
      match (Emu.execution_stats emu).stack with
      | Some { lower; upper; lowest_sp; max_usage }
        when Int64.(
               upper - lower = 4096L
               && lowest_sp = upper - 64L
               && max_usage = 64L) ->
          print_endline
            "valid emulated call stack stats: bounds=4096,max_usage=64"
      | stats ->
          failwithf "valid emulated call stack stats are wrong: %s"
            (Option.value_map stats ~default:"none" ~f:(fun s ->
                 sprintf "[%Lx,%Lx) lowest=%Lx usage=%Ld" s.lower s.upper
                   s.lowest_sp s.max_usage))
            ())
  | _ -> failwith "expected ECHO THUMB MPROTECT AARCH64"
