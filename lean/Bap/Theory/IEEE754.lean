import Bap.Core.Word

namespace Bap.Theory.IEEE754

structure Parameters where
  base : Nat
  bias : Nat
  k : Nat
  p : Nat
  w : Nat
  t : Nat
  deriving DecidableEq, Repr

private def round4Log2 (value : Nat) : Nat :=
  let lower := Nat.log2 (value ^ 4)
  if value ^ 8 ≥ 2 ^ (2 * lower + 1) then lower + 1 else lower

def binary (k : Nat) : Parameters :=
  let rounded := round4Log2 k
  let p := k - rounded + 13
  {
    base := 2
    bias := 2 ^ (k - p - 1) - 1
    k := k
    p := p
    w := rounded - 13
    t := k - (rounded - 13) - 1
  }

def decimal (k : Nat) : Parameters :=
  let p := (9 * k / 32) - 2
  let exp := (k / 16) + 3
  {
    base := 10
    bias := 3 * 2 ^ exp + p - 2
    k := k
    p := p
    w := (k / 16) + 9
    t := (15 * k / 16) - 10
  }

def binary16 : Parameters := ⟨2, 15, 16, 11, 5, 10⟩
def binary32 : Parameters := ⟨2, 127, 32, 24, 8, 23⟩
def binary64 : Parameters := binary 64
def binary80 : Parameters := ⟨2, 16383, 80, 64, 15, 64⟩
def binary128 : Parameters := binary 128
def decimal32 : Parameters := decimal 32
def decimal64 : Parameters := decimal 64
def decimal128 : Parameters := decimal 128

def binaryFormat (k : Nat) : Option Parameters :=
  if k = 16 then some binary16
  else if k = 32 then some binary32
  else if k = 80 then some binary80
  else if k > 0 && k % 32 = 0 then some (binary k)
  else none

def decimalFormat (k : Nat) : Option Parameters :=
  if k > 0 && k % 32 = 0 then some (decimal k) else none

inductive Value where
  | zero (sign : Bool)
  | subnormal (sign : Bool) (fraction : Nat)
  | normal (sign : Bool) (exponent : Int) (fraction : Nat)
  | infinity (sign : Bool)
  | nan (sign : Bool) (payload : Nat)
  deriving DecidableEq, Repr

namespace Value

def sign : Value → Bool
  | .zero sign | .subnormal sign _ | .normal sign _ _ | .infinity sign | .nan sign _ => sign

def isNan : Value → Bool
  | .nan _ _ => true
  | _ => false

def isInf : Value → Bool
  | .infinity _ => true
  | _ => false

def isZero : Value → Bool
  | .zero _ => true
  | _ => false

def isNormal : Value → Bool
  | .normal _ _ _ => true
  | _ => false

def isSubnormal : Value → Bool
  | .subnormal _ _ => true
  | _ => false

def isFinite (value : Value) : Bool := !value.isInf && !value.isNan
def isPositive (value : Value) : Bool := !value.sign
def isNegative (value : Value) : Bool := value.sign

end Value

private def standardBinary (parameters : Parameters) : Bool :=
  parameters.base = 2 && parameters.t + 1 = parameters.p && parameters.k = parameters.w + parameters.t + 1

def encode (parameters : Parameters) (value : Value) : Option (BitVec parameters.k) := do
  if !standardBinary parameters then
    none
  else
    let sign := value.sign.toNat * 2 ^ (parameters.k - 1)
    let fields ←
      match value with
      | .zero _ => some (0, 0)
      | .subnormal _ fraction =>
        if fraction > 0 && fraction < 2 ^ parameters.t then some (0, fraction) else none
      | .normal _ exponent fraction =>
        let biased := exponent + Int.ofNat parameters.bias
        if biased ≥ 1 && biased < Int.ofNat (2 ^ parameters.w - 1) && fraction < 2 ^ parameters.t then
          some (biased.toNat, fraction)
        else
          none
      | .infinity _ => some (2 ^ parameters.w - 1, 0)
      | .nan _ payload =>
        if payload > 0 && payload < 2 ^ parameters.t then some (2 ^ parameters.w - 1, payload) else none
    .some (BitVec.ofNat parameters.k (sign + fields.1 * 2 ^ parameters.t + fields.2))

def decode (parameters : Parameters) (raw : BitVec parameters.k) : Option Value := do
  if !standardBinary parameters then
    none
  else
    let raw := raw.toNat
    let sign := raw / 2 ^ (parameters.k - 1) % 2 = 1
    let exponent := raw / 2 ^ parameters.t % 2 ^ parameters.w
    let fraction := raw % 2 ^ parameters.t
    if exponent = 0 then
      if fraction = 0 then some (.zero sign) else some (.subnormal sign fraction)
    else if exponent = 2 ^ parameters.w - 1 then
      if fraction = 0 then some (.infinity sign) else some (.nan sign fraction)
    else
      some (.normal sign (Int.ofNat exponent - Int.ofNat parameters.bias) fraction)

def decodeEncoded (parameters : Parameters) (raw : Option (BitVec parameters.k)) : Option Value :=
  raw.bind (decode parameters)

inductive RMode where
  | rne
  | rtz
  | rtp
  | rtn
  | rna
  deriving DecidableEq, Repr

def roundRatio (mode : RMode) (numerator : Int) (denominator : Nat) : Option Int := do
  if denominator = 0 then
    none
  else
    let divisor := Int.ofNat denominator
    let floor := numerator.fdiv divisor
    let remainder := numerator - floor * divisor
    let upward := remainder > 0
    let rounded :=
      match mode with
      | .rtz => Int.tdiv numerator divisor
      | .rtn => floor
      | .rtp => if upward then floor + 1 else floor
      | .rne | .rna =>
        if 2 * remainder < divisor then
          floor
        else if 2 * remainder > divisor then
          floor + 1
        else
          match mode with
          | .rne => if floor % 2 = 0 then floor else floor + 1
          | _ => if numerator < 0 then floor else floor + 1
    .some rounded

@[simp] theorem binary64_parameters : binary64 = ⟨2, 1023, 64, 53, 11, 52⟩ := by
  decide

@[simp] theorem binary128_parameters : binary128 = ⟨2, 16383, 128, 113, 15, 112⟩ := by
  decide

@[simp] theorem decode_zero_binary32 :
    decodeEncoded binary32 (encode binary32 (.zero false)) = some (.zero false) := by
  rfl

@[simp] theorem round_rne_tie_even : roundRatio .rne 5 2 = some 2 := by
  decide

end Bap.Theory.IEEE754
