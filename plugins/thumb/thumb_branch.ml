open Bap_core_theory
open Core
open KB.Syntax
open Thumb_core

type eff = unit Theory.effect_ KB.t

let mask = W32.int32 0xffff_fffel

let make_dests dst =
  let encoding =
    if W32.lsb dst then Arm_target.llvm_t32 else Arm_target.llvm_a32
  in
  Theory.Label.for_addr W32.(dst land mask) >>= fun lbl ->
  KB.provide Theory.Label.encoding lbl encoding >>| fun () ->
  Set.singleton (module Theory.Label) lbl

let switch_encoding dst sema =
  make_dests dst >>| fun dests ->
  KB.Value.put Bap.Std.Insn.Slot.dests sema (Some dests)

module Make (CT : Theory.Core) = struct
  module T = Thumb_core.Make (CT)
  open T
  open T.Syntax

  let b pc dst = goto (pc +> dst)

  let bcc pc cnd dst =
    match cnd with
    | `AL -> b pc dst
    | cnd -> CT.branch (holds cnd) (goto (pc +> dst)) (seq [])

  (* the link is the address of the next instruction, of the given size,
     with the bit 0 set, as the T32 state is kept on the return *)
  let link pc size = bitv W32.((pc + int size) lor int 1)

  let bli pc dst =
    seq [ data @@ [ lr := link pc 4 ]; (goto @@ W32.((pc +> dst) land mask)) ]

  (* the A32 code is word-aligned, so the target is relative to the
     word-aligned pc, Align(PC, 4) *)
  let blxi pc dst =
    let dst = W32.(((pc + int 4) land int32 0xffff_fffcl) + int dst) in
    seq [ data @@ [ lr := link pc 4 ]; goto dst ] >>= switch_encoding dst

  let bxr dst = ctrl @@ CT.jmp (var dst land bitv mask)

  let bxi pc off : eff =
    goto W32.((pc +> off) land mask) >>= switch_encoding (pc +> off)

  let blr pc dst =
    seq CT.[ data @@ [ lr := link pc 2 ]; ctrl @@ jmp (var dst land bitv mask) ]

  let blxr pc dst = blr pc dst

  let cbnz pc rn dst =
    CT.branch CT.(inv @@ is_zero (var rn)) (goto (pc +> dst)) (seq [])

  let cbz pc rn dst =
    CT.branch CT.(is_zero (var rn)) (goto (pc +> dst)) (seq [])
end
