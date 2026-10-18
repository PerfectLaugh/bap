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
  error ();
  let major, minor = Uc.version () in
  Printf.printf "Unicorn %d.%d: ok\n" major minor
