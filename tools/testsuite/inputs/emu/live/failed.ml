#require "bap-primus-native.emu"

open Core
module Emu = Bap_emu

(* The program, that failed, is saved at the instruction, that faulted,
   and continues from there, after the script fixed the pointer, in the
   engine of the argument. The program writes to a file, as its first
   string is the path of the binary. *)

let le x =
  String.init 8 ~f:(fun i ->
      Char.of_int_exn
        Int64.(to_int_exn (shift_right_logical x Int.(8 * i) land 0xFFL)))

let () =
  match Bap_script.args () with
  | [ echo; dir; engine ] -> (
      let engine =
        if String.equal engine "unicorn" then `Unicorn else `Lifted
      in
      let ckpt = Filename.concat dir "failed.ckpt" in
      let redirects = [ ("<stdout>", Filename.concat dir "failed.out") ] in
      let allocator = ref 0x1000L in
      Emu.Checkpoint.register_ref ~package:"test" ~required:true "allocator"
        (module Int64)
        allocator;
      let emu =
        Emu.create ~engine ~redirects ~args:[ "hello" ]
          (Bap_script.project echo)
      in
      let addr name =
        List.Assoc.find_exn (Emu.symbols emu) ~equal:String.equal name
      in
      Emu.on_call emu "strlen" (fun _ -> Default);
      Emu.on_syscall emu (fun _ _ _ -> Default);
      ignore (Emu.run emu ~until:(addr "print_endline") : Emu.status);
      (* the string, that print_endline prints, is at 0x10 *)
      let good = Emu.reg emu "RDI" in
      Emu.set_reg emu "RDI" 0x10L;
      allocator := 0x2000L;
      Emu.record_event emu "allocator" (sprintf "cursor=%Lx" !allocator);
      (match Emu.run emu with
      | Failed msg -> (
          printf "failed: %s\n" msg;
          match Emu.failure emu with
          | Some fault ->
              printf "fault: thread=%d pc=%Lx addr=%Lx operation=%s\n"
                fault.thread fault.pc fault.addr
                (match fault.operation with
                | Emu.Read -> "read"
                | Emu.Write -> "write"
                | Emu.Fetch -> "fetch")
          | None -> print_endline "no structured fault")
      | _ -> print_endline "didn't fail");
      Emu.save emu ckpt;
      printf "saved at %Lx\n" (Emu.Checkpoint.info ckpt).pc;
      let context = Emu.Checkpoint.context ckpt in
      let has kind =
        List.exists context.events ~f:(fun (event : Emu.event) ->
            String.equal event.kind kind)
      in
      printf
        "context: thread=%d frames=%b model=%b fault=%Lx allocator=%b \
         import=%b syscall=%b\n"
        context.thread.tid
        (not (List.is_empty context.frames))
        (Option.exists context.models ~f:(fun models ->
             List.exists models ~f:(fun (model : Emu.Checkpoint.model_state) ->
                 String.equal model.name "test:allocator" && model.required)))
        (Option.value_exn context.failure).addr (has "allocator") (has "import")
        (has "syscall");
      let again =
        Emu.create ~engine ~redirects ~restore:ckpt (Bap_script.project echo)
      in
      printf "continues at %Lx, with RAX = %Lx\n" (Emu.pc again)
        (Emu.reg again "RAX");
      (* the pointer is in the frame and in RAX *)
      Emu.write again Int64.(Emu.reg again "RBP" - 8L) (le good);
      Emu.set_reg again "RAX" good;
      (match Emu.run again with
      | Exited (Some 0) -> print_endline "exited 0"
      | _ -> print_endline "didn't exit 0");
      (* the program, that exited, has no checkpoint *)
      match Emu.save again ckpt with
      | exception Invalid_argument msg -> print_endline msg
      | () -> print_endline "saved the program, that exited")
  | _ -> failwith "expected ECHO DIR ENGINE"
