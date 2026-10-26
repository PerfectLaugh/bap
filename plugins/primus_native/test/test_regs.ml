(* Checks that the registers of BAP correspond to the registers of
   Unicorn: each register keeps the values written to it, and the
   results of a few instructions are seen in the registers of BAP. *)

open Core
open Bap_core_theory
open Bap.Std
module Uc = Bap_engine_unicorn
module Target = Bap_primus_native_plugin.Primus_native_target

let () =
  Arm_target.load ();
  X86_target.load ();
  Bap_mips_target.load ();
  Bap_powerpc_target.load ()

let target name =
  ignore Bap_riscv_target.parent;
  Theory.Target.get ~package:"bap" name

let width v =
  match Theory.Bitv.refine (Theory.Var.sort v) with
  | Some s -> Some (Theory.Bitv.size s)
  | None -> Option.map (Theory.Bool.refine (Theory.Var.sort v)) ~f:(fun _ -> 1)

let vars target =
  Set.to_list (Theory.Target.regs target)
  |> List.filter_map ~f:(fun v ->
      Option.map (width v) ~f:(fun w ->
          Var.create (Theory.Var.name v) (Type.imm w)))

let with_engine name f =
  let target = target name in
  match Target.engine target with
  | None -> failwithf "%s: no engine" name ()
  | Some (arch, mode) ->
      let uc = Uc.create arch mode in
      let regs = Target.Regs.create target arch uc in
      Exn.protect
        ~finally:(fun () -> Uc.close uc)
        ~f:(fun () -> f target arch mode uc regs)

(* the registers with the bits that the hardware fixes, e.g., the reserved
   ones of FPCR and FPSR of AArch64, the tags of x87, which Unicorn
   classifies, when they are read, and FCSR of RISC-V, whose 8 bits
   Unicorn accesses only while the floats are on *)
let masked =
  [ "EFLAGS"; "FPSCR"; "FPCR"; "FPSR"; "FPU_STATUS"; "FPU_TAG"; "FCSR" ]

let pattern w =
  let x = Word.of_int64 ~width:64 0x5A3C_96E1_2B4D_7F18L in
  let x =
    if w > 64 then
      Word.concat (Word.of_int64 ~width:(w - 64) 0x0123_4567_89AB_CDEFL) x
    else x
  in
  Word.extract_exn ~hi:(w - 1) x

let roundtrip name =
  with_engine name @@ fun target _ _ _ regs ->
  List.iter (vars target) ~f:(fun v ->
      if not (List.mem masked (Var.name v) ~equal:String.equal) then
        let w = match Var.typ v with Type.Imm w -> w | _ -> assert false in
        let x = pattern w in
        if Target.Regs.write regs v x then
          match Target.Regs.read regs v with
          | Some y when Word.equal x y -> ()
          | Some y ->
              failwithf "%s: %s: wrote %s, read %s" name (Var.name v)
                (Word.to_string x) (Word.to_string y) ()
          | None -> failwithf "%s: %s is not readable" name (Var.name v) ())

let reg name bits = Var.create name (Type.imm bits)

let set regs name bits x =
  if not (Target.Regs.write regs (reg name bits) (Word.of_int64 ~width:bits x))
  then failwithf "%s is not mapped" name ()

let expect target regs name bits x =
  match Target.Regs.read regs (reg name bits) with
  | None -> failwithf "%s: %s is not mapped" target name ()
  | Some y ->
      let x = Word.of_int64 ~width:bits x in
      if not (Word.equal x y) then
        failwithf "%s: %s: expected %s, got %s" target name (Word.to_string x)
          (Word.to_string y) ()

let code = 0x1000L

let run name bytes ~init ~check =
  with_engine name @@ fun _ arch mode uc regs ->
  Uc.mem_map uc code 0x1000L Uc.Perm.all;
  Uc.mem_write uc code bytes;
  init regs;
  Uc.reg_write uc (Target.pc arch mode) code;
  Uc.start uc code
    ~until:(Int64.( + ) code (Int64.of_int (String.length bytes)));
  check (expect name regs)

let () =
  List.iter ~f:roundtrip
    [
      "aarch64";
      "aarch64_be";
      "armv7+le";
      "armv7-m+le";
      "armeb";
      "i86";
      "i386";
      "x86_64";
      "mips";
      "mipsel";
      "mips64";
      "mips64el";
      "powerpc";
      "powerpc64";
      "riscv32";
      "riscv64";
    ];
  (* mov rax, -1; add rax, 1 *)
  run "x86_64" "\x48\xc7\xc0\xff\xff\xff\xff\x48\x83\xc0\x01"
    ~init:(fun regs -> set regs "CF" 1 0L)
    ~check:(fun expect ->
      expect "RAX" 64 0L;
      expect "EAX" 32 0L;
      expect "ZF" 1 1L;
      expect "CF" 1 1L;
      expect "SF" 1 0L);
  (* mov ah, 0x12; mov al, 0x34 *)
  run "i386" "\xb4\x12\xb0\x34"
    ~init:(fun regs -> set regs "EAX" 32 0xFFFF_FFFFL)
    ~check:(fun expect ->
      expect "EAX" 32 0xFFFF_1234L;
      expect "AX" 16 0x1234L;
      expect "AH" 8 0x12L);
  (* cmp x0, x1; mov w2, #-1 *)
  run "aarch64" "\x1f\x00\x01\xeb\x02\x00\x80\x12"
    ~init:(fun regs ->
      set regs "R0" 64 1L;
      set regs "R1" 64 2L;
      set regs "R2" 64 (-1L))
    ~check:(fun expect ->
      expect "NF" 1 1L;
      expect "ZF" 1 0L;
      expect "CF" 1 0L;
      expect "VF" 1 0L;
      expect "R2" 64 0xFFFF_FFFFL;
      expect "W2" 32 0xFFFF_FFFFL;
      expect "X2" 64 0xFFFF_FFFFL);
  (* cmp r0, r1 *)
  run "armv7+le" "\x01\x00\x50\xe1"
    ~init:(fun regs ->
      set regs "R0" 32 5L;
      set regs "R1" 32 5L)
    ~check:(fun expect ->
      expect "ZF" 1 1L;
      expect "CF" 1 1L;
      expect "NF" 1 0L);
  (* addu v0, a0, a1 *)
  run "mips" "\x00\x85\x10\x21"
    ~init:(fun regs ->
      set regs "R4" 32 40L;
      set regs "R5" 32 2L)
    ~check:(fun expect ->
      expect "R2" 32 42L;
      expect "V0" 32 42L);
  (* cmpw r3, r4 *)
  run "powerpc" "\x7c\x03\x20\x00"
    ~init:(fun regs ->
      set regs "R3" 32 1L;
      set regs "R4" 32 2L)
    ~check:(fun expect ->
      expect "CR0LT" 1 1L;
      expect "CR0GT" 1 0L;
      expect "CR0EQ" 1 0L);
  (* addi a0, zero, 42 *)
  run "riscv64" "\x13\x05\xa0\x02" ~init:ignore ~check:(fun expect ->
      expect "X10" 64 42L)
