open Bap_core_theory
open Base
open KB.Syntax

open Thumb_core
open Thumb_opcodes

type eff = cond -> unit Theory.effect_ KB.t

module Make(CT : Theory.Core) = struct
  module T = Thumb_core.Make(CT)
  open T open T.Syntax

  let unsigned x = CT.unsigned s32 x
  let signed x = CT.signed s32 x
  let half x = CT.low s16 x
  let byte x  = CT.low s8 x
  let var = CT.var

  (**************************************************************)


  let ldri rd r i =
    rd <-? load s32 (var r + const i)

  let ldrr rd rn rm =
    rd <-? load s32 (var rn + var rm)

  let ldrbi rd rn i =
    rd <-? unsigned @@ load s8 (var rn + const i)


  let ldrbr rd rn rm =
    rd <-? unsigned @@ load s8 (var rn + var rm)


  let ldrsb rd rn rm =
    rd <-? signed @@ load s8 (var rn + var rm)


  let ldrhi rd rn i =
    rd <-? unsigned @@ load s16 (var rn + const i)


  let ldrhr rd rn rm =
    rd <-? unsigned @@ load s16 (var rn + var rm)

  let ldrsh rd rn rm =
    rd <-? signed @@ load s16 (var rn + var rm)

  let ldrpci rd pc off =
    rd <-? load s32 @@ bitv W32.(pc land ~~(int 3)) + const off

  let ldm b regs cnd =
    branch cnd [
      foreachi regs @@ begin fun i r -> [
          r := load s32 @@ var b + const Int.(i*4);
        ]
      end;
      b += const Int.(List.length regs * 4);
    ] []

  let stri rd rm i =
    var rm + const i <--? var rd

  let strr rd rm rn =
    var rm + var rn <--? var rd

  let strhi rd rm i =
    var rm + const i <--? half (var rd)

  let strhr rd rm rn =
    var rm + var rn <--? half (var rd)

  let strbi rd rm i =
    var rm + const i <--? byte (var rd)


  let strbr rd rm rn =
    var rm + var rn <--? byte (var rd)

  let stm b regs cnd =
    branch cnd [
      foreachi regs @@ begin fun i r -> [
          var b + const Int.(i * 4) <-- var r;
        ]
      end;
      b += const Int.(List.length regs * 4);
    ] []

  let pop regs = ldm sp regs

  let popret regs cnd =
    let data = seq [
        foreachi regs @@ begin fun i r -> [
            r := load s32 @@ var sp + const Int.(i*4);
          ]
        end;
        sp += const Int.(List.length regs * 4);
      ] in
    let ctrl = CT.jmp (load s32 (var sp)) in
    match cnd with
    | `AL -> CT.blk null data ctrl
    | _ -> CT.branch ~?cnd (CT.blk null data ctrl) (seq [])


  let push regs cnd = branch cnd [
      sp -= const Int.(List.length regs * 4);
      foreachi regs @@ fun i r -> [
        var sp + const Int.(i*4) <-- var r;
      ]
    ] []

end
