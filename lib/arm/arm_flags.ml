open Core
open Bap.Std
open Arm_types
open Arm_utils
module Env = Arm_env

let set_nzf r t = [ Bil.move Env.nf (msb r); Bil.move Env.zf Bil.(r = zero t) ]

let set_vnzf_add s1 s2 r t =
  Bil.move Env.vf (msb Bil.(lnot (s1 lxor s2) land (s1 lxor r))) :: set_nzf r t

let set_add s1 s2 r t = Bil.move Env.cf Bil.(r < s1) :: set_vnzf_add s1 s2 r t

let set_vnzf_sub s1 s2 r t =
  Bil.move Env.vf (msb Bil.(s1 lxor s2 land (s1 lxor r))) :: set_nzf r t

let set_sub s1 s2 r t = Bil.move Env.cf Bil.(s2 <= s1) :: set_vnzf_sub s1 s2 r t

let set_adc s1 s2 r t =
  let sum_with_carry =
    let extend = Bil.(cast unsigned) (bitlen t + 1) in
    Bil.(extend s1 + extend s2 + extend (var Env.cf))
  in
  Bil.move Env.cf (msb sum_with_carry) :: set_vnzf_add s1 s2 r t

let set_sbc s1 s2 r t = set_adc s1 Bil.(lnot s2) r t

(* the carry out of a modified immediate is the bit 31 of its value
   when it is rotated, and the carry is not changed otherwise. The A32
   immediate [imm] is encoded, the rotation is in the bits 11-8 and the
   value in the bits 7-0, the T32 one is decoded, it is rotated if it
   is neither a byte nor a replicated byte pattern. *)
let set_cf_data ~t32 ~imm =
  let v = Word.to_int_exn imm land 0xffffffff in
  let byte k = (v lsr (8 * k)) land 0xff in
  let rotated, carry =
    if t32 then
      let plain =
        v <= 0xff
        || (byte 1 = 0 && byte 3 = 0 && byte 0 = byte 2)
        || (byte 0 = 0 && byte 2 = 0 && byte 1 = byte 3)
        || (byte 0 = byte 1 && byte 1 = byte 2 && byte 2 = byte 3)
      in
      (not plain, (v lsr 31) land 1 = 1)
    else
      let r = 2 * ((v lsr 8) land 0xf) in
      (r <> 0, r <> 0 && (byte 0 lsr (r - 1)) land 1 = 1)
  in
  if rotated then Bil.move Env.cf (Bil.int (Word.of_bool carry))
  else Bil.move Env.cf (Bil.var Env.cf)
