import Std

/-- `BitVec.ofNat`, without the power of two when the number is small enough to be less than it. The power of 64 and more
is a big number, to be computed each time. The bound fits 32 bits, so comparing with it is not of big numbers either. -/
def Bap.Word.ofNatFast (width value : Nat) : BitVec width :=
  if h : value < 0xffffffff ∧ 32 ≤ width then
    ⟨⟨value, Nat.lt_of_lt_of_le h.1 (by
      have : (2 : Nat) ^ 32 ≤ 2 ^ width := Nat.pow_le_pow_right (by omega) h.2
      have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
      omega)⟩⟩
  else BitVec.ofNat width value

@[csimp] theorem Bap.Word.ofNat_eq_fast : @BitVec.ofNat = @Bap.Word.ofNatFast := by
  funext width value
  unfold Bap.Word.ofNatFast
  split
  · rename_i h
    have hlt : value < 2 ^ width :=
      Nat.lt_of_lt_of_le h.1 (by
        have : (2 : Nat) ^ 32 ≤ 2 ^ width := Nat.pow_le_pow_right (by omega) h.2
        have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
        omega)
    exact BitVec.eq_of_toNat_eq (by simp [Nat.mod_eq_of_lt hlt])
  · rfl

namespace Bap

abbrev Word (width : Nat) := BitVec width

namespace Word

def ofNat (width value : Nat) : Word width := BitVec.ofNat width value
def zero (width : Nat) : Word width := BitVec.zero width
def ones (width : Nat) : Word width := BitVec.allOnes width
def toNat (value : Word width) : Nat := BitVec.toNat value
def toInt (value : Word width) : Int := BitVec.toInt value
def bool (value : Bool) : Word 1 := BitVec.ofNat 1 value.toNat

def udiv (left right : Word width) : Word width :=
  if right = 0 then ones width else left / right

def urem (left right : Word width) : Word width :=
  if right = 0 then left else left % right

/-- Upstream's documented definition and SMT-LIB `bvsdiv`: `udiv` of the magnitudes, by cases on the signs, and so
`x /$ 0` is all ones for `x ≥ 0` and `1` for `x < 0`. -/
def sdiv (left right : Word width) : Word width := BitVec.smtSDiv left right

def srem (left right : Word width) : Word width :=
  if right = 0 then left else BitVec.srem left right

/-- SMT-LIB `bvsmod`: the sign of a nonzero result follows the divisor, and `smod x 0 = x`. -/
def smod (left right : Word width) : Word width := BitVec.smod left right

def shl (value amount : Word width) : Word width := value <<< amount.toNat
def lshr (value amount : Word width) : Word width := value >>> amount.toNat
def ashr (value amount : Word width) : Word width := BitVec.sshiftRight value amount.toNat
def eq (left right : Word width) : Word 1 := bool (left == right)
def neq (left right : Word width) : Word 1 := bool (left != right)
def lt (left right : Word width) : Word 1 := bool (left < right)
def le (left right : Word width) : Word 1 := bool (left <= right)
def slt (left right : Word width) : Word 1 := bool (BitVec.slt left right)
def sle (left right : Word width) : Word 1 := bool (BitVec.sle left right)

def low (width : Nat) (value : Word source) : Word width := BitVec.zeroExtend width value
def unsigned (width : Nat) (value : Word source) : Word width := BitVec.zeroExtend width value
def signed (width : Nat) (value : Word source) : Word width := BitVec.signExtend width value

def high (width : Nat) (value : Word source) : Except String (Word width) :=
  if 0 < width ∧ width ≤ source then
    let shifted := BitVec.ushiftRight value (source - width)
    .ok (BitVec.zeroExtend width shifted)
  else
    .error "invalid high cast"

def extract (high low : Nat) (value : Word source) : Except String (Word (high - low + 1)) :=
  if high < low then
    .error "extract high bound is below low bound"
  else if high ≥ source then
    .error "extract high bound exceeds source width"
  else
    .ok (BitVec.extractLsb high low value)

def concat (left : Word leftWidth) (right : Word rightWidth) : Word (leftWidth + rightWidth) :=
  BitVec.append left right

def toHex (value : Word width) : String :=
  String.ofList (Nat.toDigits 16 value.toNat)

theorem udiv_zero (value : Word width) : udiv value 0 = ones width := by
  simp [udiv]

theorem urem_zero (value : Word width) : urem value 0 = value := by
  simp [urem]

theorem ofNat_toNat_mod (width value : Nat) :
    (ofNat width value).toNat = value % 2 ^ width := by
  exact BitVec.toNat_ofNat value width

end Word
end Bap
