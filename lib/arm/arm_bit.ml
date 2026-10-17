open Core
open Bap.Std
open Or_error
open Arm_types
open Arm_utils
module Env = Arm_env
module Shift = Arm_shift

let bits_of_size = function `H -> 16 | `B -> 8
let wordm x = Ok (Word.of_int x ~width:32)

let extend ~dest ~src ?src2 sign size ~rot cond =
  let rot = assert_imm [%here] rot in
  let dest = assert_reg [%here] dest in
  let amount =
    match Word.Int_err.(!$rot * wordm 8) with
    | Ok amount -> amount
    | Error err -> fail [%here] "failed to obtain amount"
  in
  let rotated, (_ : exp) =
    if Word.is_zero amount then (exp_of_op src, Bil.int (Word.zero 32))
    else Shift.lift_c ~src:(exp_of_op src) `ROR ~shift:(Bil.int amount) reg32_t
  in
  let extracted = Bil.(cast low (bits_of_size size) rotated) in
  let extent = cast_of_sign sign 32 extracted in
  let final =
    match src2 with Some s2 -> Bil.(exp_of_op s2 + extent) | None -> extent
  in
  exec [ assn (Env.of_reg dest) final ] cond

let bit_extract ~dest ~src sign ~lsb ~widthminus1 cond =
  let dest = assert_reg [%here] dest in
  let lsb = assert_imm [%here] lsb in
  let widthminus1 = assert_imm [%here] widthminus1 in
  let int_of_imm imm =
    match Word.to_int imm with
    | Ok imm -> imm
    | Error err ->
        fail [%here] "can't cast word to int: %s" @@ Error.to_string_hum err
  in
  let low = int_of_imm lsb in
  let high = low + int_of_imm widthminus1 in
  let extracted = Bil.extract ~hi:high ~lo:low (exp_of_op src) in
  let final = cast_of_sign sign 32 extracted in
  exec [ assn (Env.of_reg dest) final ] cond

(* the lowest bit and the width of the field of BFI and BFC from the
   inverted mask operand, which is the same in the A32 and T32
   encodings, unlike the fields of the instruction *)
let get_lsb_width bmask : int * int =
  let mask =
    lnot (Word.to_int_exn (assert_imm [%here] bmask)) land 0xffffffff
  in
  if mask = 0 then fail [%here] "BFI and BFC need a non-empty field";
  let rec lsb n = if mask land (1 lsl n) <> 0 then n else lsb (n + 1) in
  let rec msb n = if mask land (1 lsl n) <> 0 then n else msb (n - 1) in
  let lsb = lsb 0 in
  (lsb, msb 31 - lsb + 1)

let bit_field_insert ~dest ~src bmask cond =
  let dest = assert_reg [%here] dest in
  let d = Env.of_reg dest in
  let d_e = Bil.var d in
  let lsb, width = get_lsb_width bmask in
  let extracted = Bil.extract ~hi:(width - 1) ~lo:0 (exp_of_op src) in
  let ext_h b s = Bil.extract ~hi:31 ~lo:b s in
  let ext_l b s = Bil.extract ~hi:b ~lo:0 s in
  let inst =
    match (lsb + width - 1, lsb) with
    | 31, 0 -> extracted
    | 31, l -> Bil.concat extracted (ext_l (l - 1) d_e)
    | m, 0 -> Bil.concat (ext_h (m + 1) d_e) extracted
    | m, l ->
        Bil.concat
          (Bil.concat (ext_h (m + 1) d_e) extracted)
          (ext_l (l - 1) d_e)
  in
  exec [ Bil.move d inst ] cond
