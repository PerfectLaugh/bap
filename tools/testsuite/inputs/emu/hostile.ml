#require "bap-primus-unicorn.emu"

(* The code of the program, that is hostile to the JIT of the lifted
   engine, see bap_lifted_jit.ml, runs in Unicorn and in the lifted
   engine, whose results must be the same:

     bap script hostile.ml x86_64-linux-gnu-echo

   - rep: the string instruction, which loops, runs in a hot loop;
   - patch: the hot loop, whose code is patched, again and again, more
     times, than the JIT compiles a block at an address;
   - wrap: the store of a hot loop, whose address wraps around the end of
     the address space, faults in the middle of its block. *)

module Emu = Bap_emu

let file = List.hd (Bap_script.args ())

let status = function
  | Emu.Paused -> "paused"
  | Running -> "running"
  | Exited _ -> "exited"
  | Failed _ -> "failed"

let run name engine =
  let emu = Emu.create ~engine (Bap_script.project ~disassemble:true file) in
  (* the scenarios start at their own addresses, as the JIT counts the
     blocks, that it compiled, by the address *)
  let start = Emu.pc emu in
  let entry = ref start in
  let at offset = Int64.add !entry (Int64.of_int offset) in
  let scenario offset = entry := Int64.add start (Int64.of_int offset) in
  let buf =
    Int64.logand (Int64.sub (Emu.reg emu "RSP") 0x20000L) (Int64.lognot 0xFFFL)
  in
  let print fmt = Printf.printf ("%s: " ^^ fmt ^^ "\n%!") name in
  (* mov rcx, rdx; mov rdi, rsi; rep stosb; dec rbx; jnz -13; nop *)
  scenario 0;
  Emu.write emu !entry
    "\x48\x89\xd1\x48\x89\xf7\xf3\xaa\x48\xff\xcb\x75\xf3\x90";
  Emu.set_reg emu "RAX" 0x5AL;
  Emu.set_reg emu "RBX" 100L;
  Emu.set_reg emu "RDX" 16L;
  Emu.set_reg emu "RSI" buf;
  Emu.set_pc emu !entry;
  let rep = Emu.run ~until:(at 13) emu in
  print "rep %s, rdi +%Ld, %S" (status rep)
    (Int64.sub (Emu.reg emu "RDI") buf)
    (Emu.read emu buf 17);
  (* mov eax, I; add ebx, eax; dec ecx; jnz -11; nop *)
  scenario 0x40;
  Emu.write emu !entry "\xb8\x00\x00\x00\x00\x01\xc3\xff\xc9\x75\xf5\x90";
  Emu.set_reg emu "RBX" 0L;
  let statuses =
    List.init 20 (fun i ->
        Emu.write emu (at 1) (String.make 1 (Char.chr i));
        Emu.set_reg emu "RCX" 50L;
        Emu.set_pc emu !entry;
        status (Emu.run ~until:(at 11) emu))
    |> List.sort_uniq compare
  in
  print "patch %s, ebx %Ld" (String.concat "," statuses) (Emu.reg emu "RBX");
  (* the fault ends the program, so it is the last *)
  (* dec rcx; mov [rbx], ax; jnz -8; nop *)
  scenario 0x80;
  Emu.write emu !entry "\x48\xff\xc9\x66\x89\x03\x75\xf8\x90";
  Emu.set_reg emu "RBX" buf;
  Emu.set_reg emu "RCX" 1000L;
  Emu.set_pc emu !entry;
  let hot = Emu.run ~until:(at 8) emu in
  Emu.set_reg emu "RBX" (-1L);
  Emu.set_reg emu "RCX" 5L;
  Emu.set_pc emu !entry;
  let wrapped =
    match Emu.run ~until:(at 8) emu with
    | Failed msg -> msg
    | s -> status s
  in
  print "wrap %s, %s" (status hot) wrapped

let () =
  run "unicorn" `Unicorn;
  run "lifted" `Lifted
