(* Runs a few hand-made instructions with the bindings to Unicorn. *)

module Uc = Bap_unicorn

let code = 0x1000L

let reg arch name =
  match Uc.reg arch name with
  | Some reg -> reg
  | None -> failwith ("no register " ^ name)

let check name expected got =
  if expected <> got then
    failwith (Printf.sprintf "%s: expected 0x%Lx, got 0x%Lx" name expected got)

let with_engine arch mode bytes f =
  let uc = Uc.create arch mode in
  Uc.mem_map uc code 0x1000L Uc.Perm.all;
  Uc.mem_write uc code bytes;
  Fun.protect ~finally:(fun () -> Uc.close uc) (fun () -> f uc)

(* inc ecx; dec edx *)
let x86 () =
  with_engine X86 Uc.Mode.mode32 "\x41\x4a" @@ fun uc ->
  let ecx = reg X86 "ecx" and edx = reg X86 "EDX" in
  Uc.reg_write uc ecx 0x1234L;
  Uc.reg_write uc edx 0x7890L;
  let steps = ref [] in
  let _ = Uc.on_code uc (fun addr size -> steps := (addr, size) :: !steps) in
  Uc.start uc code ~until:(Int64.add code 2L);
  check "ecx" 0x1235L (Uc.reg_read uc ecx);
  check "edx" 0x788fL (Uc.reg_read uc edx);
  if List.rev !steps <> [ (code, 1); (0x1001L, 1) ] then
    failwith "x86: wrong instructions"

(* mov x0, #42; ldr x1, [x2] *)
let arm64 () =
  with_engine Arm64 Uc.Mode.arm "\x40\x05\x80\xd2\x41\x00\x40\xf9" @@ fun uc ->
  let x0 = reg Arm64 "x0" and x1 = reg Arm64 "x1" and x2 = reg Arm64 "x2" in
  let data = 0x10000L in
  Uc.reg_write uc x2 data;
  let faults = ref 0 in
  let _ =
    Uc.on_mem_invalid uc [ `read ] [ `unmapped ] (fun access addr _ _ ->
        incr faults;
        assert (access = Read_unmapped);
        check "fault" data addr;
        Uc.mem_map uc data 0x1000L Uc.Perm.read;
        Uc.mem_write uc data "\x88\x77\x66\x55\x44\x33\x22\x11";
        true)
  in
  Uc.start uc code ~until:(Int64.add code 8L);
  check "x0" 42L (Uc.reg_read uc x0);
  check "x1" 0x1122334455667788L (Uc.reg_read uc x1);
  if !faults <> 1 then failwith "arm64: the fault is not handled";
  (* the context restores the registers *)
  let saved = Uc.save uc in
  Uc.reg_write uc x0 0L;
  Uc.restore uc saved;
  check "restored x0" 42L (Uc.reg_read uc x0);
  if String.length (Uc.reg_read_bytes uc (reg Arm64 "q0")) <> 16 then
    failwith "arm64: q0 is not 16 bytes"

exception Stop

(* an exception of a hook stops the emulation and is reraised *)
let exn () =
  with_engine X86 Uc.Mode.mode32 "\x41\x41\x41\x41" @@ fun uc ->
  let count = ref 0 in
  let _ =
    Uc.on_code uc (fun _ _ ->
        incr count;
        if !count = 2 then raise Stop)
  in
  match Uc.start uc code ~until:(Int64.add code 4L) with
  | () -> failwith "exn: the exception is lost"
  | exception Stop ->
      if !count <> 2 then failwith "exn: the emulation is not stopped"

(* a hook that stops the emulation stops it before the instruction *)
let stop () =
  with_engine X86 Uc.Mode.mode32 "\x41\x41\x41\x41" @@ fun uc ->
  let ecx = reg X86 "ecx" and eip = reg X86 "eip" in
  Uc.reg_write uc ecx 0L;
  let _ = Uc.on_code uc ~first:0x1002L ~last:0x1002L (fun _ _ -> Uc.stop uc) in
  Uc.start uc code ~until:(Int64.add code 4L);
  check "ecx" 2L (Uc.reg_read uc ecx);
  check "eip" 0x1002L (Uc.reg_read uc eip);
  (* and it can be resumed from there *)
  Uc.start uc 0x1003L ~until:(Int64.add code 4L);
  check "resumed ecx" 3L (Uc.reg_read uc ecx)

(* a store to a read-only page faults and stops the emulation at the
   store, which, after the page is writable, runs again, as the executor
   tells the pages that the code wrote; the page that is read-only again
   faults again. Unicorn loses the store, if the hook makes the page
   writable and continues. *)
let dirty (arch : Uc.arch) mode insn (value, addr, pc) =
  with_engine arch mode insn @@ fun uc ->
  let data = 0x10000L in
  Uc.mem_map uc data 0x1000L Uc.Perm.read;
  Uc.reg_write uc (reg arch value) 0x11223344L;
  Uc.reg_write uc (reg arch addr) data;
  let faults = ref [] in
  let _ =
    Uc.on_mem_invalid uc [ `write ] [ `prot ] (fun access addr _ _ ->
        assert (access = Write_prot);
        faults := addr :: !faults;
        false)
  in
  let until = Int64.add code 4L in
  let run expected =
    (try Uc.start uc code ~until with Uc.Error _ -> ());
    (match !faults with
    | [ addr ] ->
        check "the store" code (Uc.reg_read uc (reg arch pc));
        Uc.mem_protect uc
          (Int64.logand addr (-4096L))
          0x1000L
          Uc.Perm.(read + write);
        Uc.start uc code ~until
    | _ -> ());
    if List.length !faults <> expected then
      failwith
        (Printf.sprintf "dirty: %d faults instead of %d" (List.length !faults)
           expected);
    faults := []
  in
  run 1;
  let stored = Uc.mem_read uc data 4 in
  if stored <> "\x44\x33\x22\x11" && stored <> "\x11\x22\x33\x44" then
    failwith "dirty: the store is lost";
  run 0;
  Uc.mem_protect uc data 0x1000L Uc.Perm.read;
  run 1

let dirty () =
  dirty X86 Uc.Mode.mode32 "\x89\x0b\x90\x90" ("ecx", "ebx", "eip");
  dirty Arm64 Uc.Mode.arm "\x41\x00\x00\xf9" ("x1", "x2", "pc");
  dirty Arm Uc.Mode.arm "\x00\x10\x82\xe5" ("r1", "r2", "pc");
  dirty Mips Uc.Mode.(mips32 + big_endian) "\xac\xc5\x00\x00" ("a1", "a2", "pc");
  dirty Ppc Uc.Mode.(ppc32 + big_endian) "\x90\x85\x00\x00" ("4", "5", "pc");
  dirty Riscv Uc.Mode.riscv64 "\x23\x30\xb6\x00" ("a1", "a2", "pc")

let read_values () =
  with_engine Ppc Uc.Mode.(ppc32 + big_endian) "\x80\x85\x00\x00" @@ fun uc ->
  let data = 0x10000L in
  Uc.mem_map uc data 0x1000L Uc.Perm.all;
  Uc.mem_write uc data "\x11\x22\x33\x44";
  Uc.reg_write uc (reg Ppc "5") data;
  let trace = Uc.Trace.create ~accesses:16 ~read_values:true 16 in
  let _ = Uc.trace ~memory:true uc trace in
  Uc.start uc code ~until:(Int64.add code 4L);
  check "big-endian loaded register" 0x11223344L (Uc.reg_read uc (reg Ppc "4"));
  let accesses = Uc.Trace.accesses trace in
  if Bigarray.Array2.dim1 accesses <> 1 then
    failwith
      (Printf.sprintf "read_values: wrong access count %d (%Ld total)"
         (Bigarray.Array2.dim1 accesses)
         (Uc.Trace.accesses_count trace));
  let open Bigarray.Array2 in
  check "big-endian loaded bytes" 0x44332211L (get accesses 0 2);
  if
    not
      (Int64.equal
         Int64.(logand (shift_right_logical (get accesses 0 3) 33) 1L)
         1L)
  then failwith "read_values: the loaded value is unavailable"

let error () =
  let uc = Uc.create X86 Uc.Mode.mode64 in
  match Uc.mem_map uc 0x1001L 0x1000L Uc.Perm.all with
  | () -> failwith "error: an unaligned map succeeded"
  | exception Uc.Error (_, _) -> Uc.close uc

let () =
  List.iter
    (fun arch -> if not (Uc.supported arch) then failwith "an arch is missing")
    [ Arm; Arm64; Mips; X86; Ppc; Riscv ];
  x86 ();
  arm64 ();
  exn ();
  stop ();
  dirty ();
  read_values ();
  error ();
  let major, minor = Uc.version () in
  Printf.printf "Unicorn %d.%d: ok\n" major minor
