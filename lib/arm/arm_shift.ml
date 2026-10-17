open Core
open Bap.Std
open Or_error
open Arm_types
open Arm_utils
module Env = Arm_env

let shift_of_word op =
  match Word.to_int op with
  | Ok 1 -> `ASR
  | Ok 2 -> `LSL
  | Ok 3 -> `LSR
  | Ok 4 -> `ROR
  | Ok 5 -> `RRX
  | _ -> fail [%here] "Imm %s, doesn't stand for shift" (Word.to_string op)

(* The result and the carry out of shifting [src] by the amount
   [shift], as the A32 shifter does: an amount of 0 leaves the value
   and the carry, amounts above the width shift all bits out (asr
   fills with the sign and keeps it as the carry) and ror rotates by
   the amount modulo the width. *)
let shift_c ~src shift_type ~shift t =
  let bits = bitlen t in
  let num n = Bil.int (Word.of_int n ~width:bits) in
  let zero = num 0 and one = num 1 and width = num bits in
  let last = num (bits - 1) in
  let nth_bit n e = Bil.(cast low 1 (e lsr n)) in
  let unless_zero carry =
    Bil.(ite ~if_:(shift = zero) ~then_:(var Env.cf) ~else_:carry)
  in
  match shift_type with
  | `ASR ->
      let in_range = Bil.(shift < width) in
      let shifted = Bil.(src asr ite ~if_:in_range ~then_:shift ~else_:last) in
      let carry =
        nth_bit Bil.(ite ~if_:in_range ~then_:(shift - one) ~else_:last) src
      in
      (shifted, unless_zero carry)
  | `LSL ->
      let shifted = Bil.(src lsl shift) in
      let carry = nth_bit Bil.(width - shift) src in
      (shifted, unless_zero carry)
  | `LSR ->
      let shifted = Bil.(src lsr shift) in
      let carry = nth_bit Bil.(shift - one) src in
      (shifted, unless_zero carry)
  | `ROR ->
      let m = Bil.(shift land last) in
      let shifted = Bil.((src lsr m) lor (src lsl (width - m))) in
      let carry =
        nth_bit Bil.(ite ~if_:(m = zero) ~then_:last ~else_:(m - one)) src
      in
      (shifted, unless_zero carry)
  | `RRX ->
      let ret1 = Bil.(src lsr one) in
      let carryin = Bil.(cast unsigned bits (var Env.cf) lsl last) in
      let shifted = Bil.(ret1 lor carryin) in
      let carry = nth_bit zero src in
      (shifted, carry)

(* the amount of a register-specified shift is the lowest byte of the
   register *)
let r_shift ~src shift_type ~shift t =
  let shift_type = assert_imm [%here] shift_type in
  let byte = Bil.int (Word.of_int 0xff ~width:(bitlen t)) in
  shift_c ~src (shift_of_word shift_type) ~shift:Bil.(shift land byte) t

(* in the immediate encodings the amount 0 of lsr and asr means 32 *)
let imm_amount shift_t amount width =
  match shift_t with
  | (`LSR | `ASR) when Word.is_zero amount -> Word.of_int width ~width
  | _ -> amount

let i_shift ~src shift_type t =
  let shift_type = assert_imm [%here] shift_type in
  let width = bitlen t in
  let mask = Word.of_int 7 ~width in
  let three = Word.of_int 3 ~width in
  (* lower three bits are type*)
  let r =
    Word.Int_err.(!$shift_type land !$mask) >>| shift_of_word >>= fun shift_t ->
    (* other bits are immediate *)
    Word.Int_err.((!$shift_type land lnot !$mask) lsr !$three)
    >>= fun shift_amt -> return (shift_t, shift_amt)
  in
  match r with
  | Error err -> fail [%here] "%s" Error.(to_string_hum err)
  | Ok (shift_t, shift_amt) ->
      let shift_amt = imm_amount shift_t shift_amt width in
      shift_c ~src shift_t ~shift:Bil.(int shift_amt) t

(* decodes a shifted operand for a memory operation
 * src - the operand to be shifted
 * shift - an int64,
 *            bits 11 through 0 represent the shift amount
 *            bits 12 represents whether the expression is added or subtracted
 *            bits 15 through 13 represent the shift type, valid shift types
 *              are number 1 through 5
 * typ - the type
 *)
let mem_shift ~src shift typ =
  let shift = assert_imm [%here] shift in
  let width = bitlen typ in
  let word = Word.of_int ~width in
  let wordm n = Ok (word n) in
  let shift_typ w =
    Word.Int_err.((!$w land wordm 0xE000) lsr wordm 13) >>| shift_of_word
  in
  (* Gets the shift amount from the immediate *)
  let shift_amt w = Word.Int_err.(!$w land wordm 0xFFF) >>| Bil.int in
  (* Converts the shift to a negative if the negative bit is set *)
  let to_neg w exp =
    match Word.Int_err.(wordm 0x1000 land !$w) with
    | Ok x when Word.equal x (word 0x1000) -> Bil.(int (Word.ones width) * exp)
    | _ -> exp
  in
  let r =
    shift_typ shift >>= fun t ->
    shift_amt shift >>= fun amt -> return (t, amt)
  in
  match r with
  | Error err -> fail [%here] "%s" Error.(to_string_hum err)
  | Ok (t, amount) ->
      let amount =
        match amount with
        | Bil.Int w -> Bil.int (imm_amount t w width)
        | amount -> amount
      in
      let exp, _ = shift_c ~src t ~shift:amount typ in
      to_neg shift exp

let lift_c = shift_c
let lift_i = i_shift
let lift_r = r_shift
let lift_mem = mem_shift
