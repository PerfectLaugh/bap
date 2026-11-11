/-! # Floating point in integers

The operations that lifted code names as `fadd_rne_ieee754_binary_64` and the like, on the bits of their operands. Each works out
the exact value in integers, with a sticky bit for what a division or a root leaves over, and one function rounds it to a format.
So there is one path for all formats and rounding modes, and an answer doesn't depend on the machine or on its floating point.

The NaNs are those of x86: the first NaN operand, made quiet, or else the default, which is negative. What an operation raises
is worked out from its result, by `raisedBy`, apart from it. -/

namespace Bap.Float

structure Format where
  exponentBits : Nat
  /-- The bits after the point. -/
  fractionBits : Nat
  /-- Whether the bit before the point is stored, as x87 does. -/
  explicit : Bool := false
  deriving DecidableEq, Repr

def formatOf : Nat → Option Format
  | 16 => some ⟨5, 10, false⟩
  | 32 => some ⟨8, 23, false⟩
  | 64 => some ⟨11, 52, false⟩
  | 80 => some ⟨15, 63, true⟩
  | 128 => some ⟨15, 112, false⟩
  | _ => none

namespace Format

def bias (format : Format) : Nat := 2 ^ (format.exponentBits - 1) - 1
def maxExponent (format : Format) : Nat := 2 ^ format.exponentBits - 1
/-- The bits of what is below the exponent. -/
def fieldBits (format : Format) : Nat := format.fractionBits + (if format.explicit then 1 else 0)
def width (format : Format) : Nat := 1 + format.exponentBits + format.fieldBits
/-- The exponent of the last bit of a number at the smallest exponent. -/
def lowest (format : Format) : Int := 1 - (format.bias : Int) - (format.fractionBits : Int)

end Format

/-- A number, as its sign and `mantissa * 2 ^ exponent`, whose mantissa isn't zero. -/
inductive Number where
  | nan (bits : Nat)
  | infinity (negative : Bool)
  | zero (negative : Bool)
  | finite (negative : Bool) (mantissa : Nat) (exponent : Int)
  deriving DecidableEq, Repr

/-- Of a format with its integer bit, as x87's, an encoding that the 387 and after take as an invalid operand: one whose exponent isn't
0 and whose integer bit is, an unnormal, a pseudo-infinity or a pseudo-NaN. -/
def noncanonical (format : Format) (bits : Nat) : Bool :=
  format.explicit && (bits >>> format.fieldBits) % 2 ^ format.exponentBits != 0 && (bits >>> format.fractionBits) % 2 == 0

def unpack (format : Format) (bits : Nat) : Number :=
  if noncanonical format bits then .nan bits else
  let negative := (bits >>> (format.width - 1)) % 2 == 1
  let exponent := (bits >>> format.fieldBits) % 2 ^ format.exponentBits
  let field := bits % 2 ^ format.fieldBits
  let fraction := field % 2 ^ format.fractionBits
  if exponent == format.maxExponent then
    if fraction == 0 then .infinity negative else .nan bits
  else
    let whole := if format.explicit then (field >>> format.fractionBits) % 2 else (if exponent == 0 then 0 else 1)
    let mantissa := whole * 2 ^ format.fractionBits + fraction
    if mantissa == 0 then .zero negative
    else .finite negative mantissa (format.lowest + ((max exponent 1 : Nat) - 1 : Nat))

private def signBit (format : Format) (negative : Bool) : Nat :=
  if negative then 2 ^ (format.width - 1) else 0

def packZero (format : Format) (negative : Bool) : Nat := signBit format negative

def packInfinity (format : Format) (negative : Bool) : Nat :=
  signBit format negative + format.maxExponent * 2 ^ format.fieldBits +
    (if format.explicit then 2 ^ format.fractionBits else 0)

/-- The NaN of an operation with no NaN among its operands. -/
def defaultNaN (format : Format) : Nat :=
  signBit format true + format.maxExponent * 2 ^ format.fieldBits +
    (if format.explicit then 3 * 2 ^ (format.fractionBits - 1) else 2 ^ (format.fractionBits - 1))

/-- The same NaN, made quiet. -/
def quiet (format : Format) (bits : Nat) : Nat :=
  let top := 2 ^ (format.fractionBits - 1)
  if (bits >>> (format.fractionBits - 1)) % 2 == 1 then bits else bits + top

private def bitLength (value : Nat) : Nat := Nat.log2 value + (if value == 0 then 0 else 1)

inductive Mode where
  /-- To nearest, ties to even. -/
  | rne
  /-- To nearest, ties away from zero. -/
  | rna
  | rtz
  /-- Towards positive and negative infinity. -/
  | rtp
  | rtn
  /-- To odd, whose last bit says that it isn't exact. -/
  | rod
  deriving DecidableEq, Repr

def Mode.ofName : String → Option Mode
  | "rne" | "rnx" | "rni" | "rns" | "rnq" => some .rne
  | "rna" | "rmm" => some .rna
  | "rtz" | "rzq" => some .rtz
  | "rtp" | "rup" | "rpq" => some .rtp
  | "rtn" | "rdn" | "rmq" => some .rtn
  | "rod" => some .rod
  | _ => none

/-- What is kept of `mantissa`, without the `shift` bits below it, rounded. `sticky` says that there is more below all of it. -/
def roundBits (mode : Mode) (negative : Bool) (mantissa shift : Nat) (sticky : Bool) : Nat :=
  let kept := mantissa >>> shift
  let half := shift > 0 && (mantissa >>> (shift - 1)) % 2 == 1
  let below := sticky || (shift > 1 && mantissa % 2 ^ (shift - 1) != 0)
  let up := match mode with
    | .rne => half && (below || kept % 2 == 1)
    | .rna => half
    | .rtz | .rod => false
    | .rtp => !negative && (half || below)
    | .rtn => negative && (half || below)
  if mode == .rod && (half || below) then kept ||| 1
  else if up then kept + 1 else kept

/-- A number of `mantissa * 2 ^ exponent`, and something below it if `sticky`, in a format. -/
def pack (format : Format) (mode : Mode) (negative : Bool) (mantissa : Nat) (exponent : Int) (sticky : Bool := false) : Nat :=
  if mantissa == 0 && !sticky then packZero format negative else
  let precision := format.fractionBits + 1
  let top := exponent + bitLength mantissa
  -- The exponent of the last bit that is kept.
  let last := max (top - precision) format.lowest
  let shift := last - exponent
  let (kept, last) :=
    if shift ≤ 0 then (roundBits mode negative (mantissa <<< (-shift).toNat) 0 sticky, last)
    else (roundBits mode negative mantissa shift.toNat sticky, last)
  let (kept, last) := if kept == 2 ^ precision then (kept / 2, last + 1) else (kept, last)
  if kept == 0 then packZero format negative else
  let biased := if kept < 2 ^ format.fractionBits then 0 else last - format.lowest + 1
  if biased ≥ format.maxExponent then
    let toInfinity := match mode with
      | .rne | .rna => true
      | .rtz | .rod => false
      | .rtp => !negative
      | .rtn => negative
    if toInfinity then packInfinity format negative
    else
      -- The largest finite number.
      signBit format negative + (format.maxExponent - 1) * 2 ^ format.fieldBits + (2 ^ format.fieldBits - 1)
  else
    let field := if format.explicit then kept else kept % 2 ^ format.fractionBits
    signBit format negative + biased.toNat * 2 ^ format.fieldBits + field

/-- An exact sum of signed values, in a format. Exactly opposite numbers are +0, or -0 when rounding down. -/
private def packSum (format : Format) (mode : Mode) (left right : Bool × Nat × Int) : Nat :=
  let exponent := min left.2.2 right.2.2
  let scaled (entry : Bool × Nat × Int) : Int :=
    let value : Int := (entry.2.1 <<< (entry.2.2 - exponent).toNat : Nat)
    if entry.1 then -value else value
  let sum := scaled left + scaled right
  if sum == 0 then packZero format (mode == .rtn)
  else pack format mode (sum < 0) sum.natAbs exponent

def add (format : Format) (mode : Mode) (left right : Nat) : Nat :=
  match unpack format left, unpack format right with
  | .nan bits, _ | _, .nan bits => quiet format bits
  | .infinity a, .infinity b => if a == b then left else defaultNaN format
  | .infinity _, _ => left
  | _, .infinity _ => right
  | .zero a, .zero b => if a == b then left else packZero format (mode == .rtn)
  | .zero _, _ => right
  | _, .zero _ => left
  | .finite a m e, .finite b n f => packSum format mode (a, m, e) (b, n, f)

private def negate (format : Format) (bits : Nat) : Nat :=
  if (bits >>> (format.width - 1)) % 2 == 1 then bits - 2 ^ (format.width - 1) else bits + 2 ^ (format.width - 1)

def sub (format : Format) (mode : Mode) (left right : Nat) : Nat :=
  match unpack format left, unpack format right with
  -- It is the operand, made quiet, and not what is negated.
  | .nan bits, _ | _, .nan bits => quiet format bits
  | _, _ => add format mode left (negate format right)

def mul (format : Format) (mode : Mode) (left right : Nat) : Nat :=
  match unpack format left, unpack format right with
  | .nan bits, _ | _, .nan bits => quiet format bits
  | .infinity _, .zero _ | .zero _, .infinity _ => defaultNaN format
  | .infinity a, .infinity b | .infinity a, .finite b _ _ | .finite a _ _, .infinity b => packInfinity format (a != b)
  | .zero a, .zero b | .zero a, .finite b _ _ | .finite a _ _, .zero b => packZero format (a != b)
  | .finite a m e, .finite b n f => pack format mode (a != b) (m * n) (e + f)

def div (format : Format) (mode : Mode) (left right : Nat) : Nat :=
  match unpack format left, unpack format right with
  | .nan bits, _ | _, .nan bits => quiet format bits
  | .infinity _, .infinity _ | .zero _, .zero _ => defaultNaN format
  | .infinity a, .zero b | .infinity a, .finite b _ _ | .finite a _ _, .zero b => packInfinity format (a != b)
  | .zero a, .infinity b | .zero a, .finite b _ _ | .finite a _ _, .infinity b => packZero format (a != b)
  | .finite a m e, .finite b n f =>
    let shift := format.fractionBits + 3 + bitLength n
    let scaled := m <<< shift
    pack format mode (a != b) (scaled / n) (e - f - shift) (scaled % n != 0)

/-- The integer square root, from above by Newton's method, which takes a few steps for each bit at most. -/
def isqrt (value : Nat) : Nat :=
  if value == 0 then 0 else
  let rec go : Nat → Nat → Nat
    | 0, guess => guess
    | fuel + 1, guess =>
      let next := (guess + value / guess) / 2
      if next ≥ guess then guess else go fuel next
  go (bitLength value + 8) (2 ^ ((bitLength value + 1) / 2))

def sqrt (format : Format) (mode : Mode) (bits : Nat) : Nat :=
  match unpack format bits with
  | .nan _ => quiet format bits
  | .zero _ => bits
  | .infinity negative => if negative then defaultNaN format else bits
  | .finite true _ _ => defaultNaN format
  | .finite false m e =>
    -- Twice the bits that are kept, and more, with an exponent that halves.
    let wanted := 2 * (format.fractionBits + 3)
    let shift := wanted - min wanted (bitLength m)
    let shift := if (e - shift) % 2 == 0 then shift else shift + 1
    let scaled := m <<< shift
    let root := isqrt scaled
    pack format mode false root ((e - shift) / 2) (root * root != scaled)

/-- `left * right + addend`, rounded once. -/
def fma (format : Format) (mode : Mode) (left right addend : Nat) : Nat :=
  match unpack format left, unpack format right, unpack format addend with
  | .nan bits, _, _ | _, .nan bits, _ | _, _, .nan bits => quiet format bits
  | .infinity _, .zero _, _ | .zero _, .infinity _, _ => defaultNaN format
  | .infinity a, .infinity b, c | .infinity a, .finite b _ _, c | .finite a _ _, .infinity b, c =>
    match c with
    | .infinity d => if (a != b) == d then addend else defaultNaN format
    | _ => packInfinity format (a != b)
  | _, _, .infinity _ => addend
  | .zero a, .zero b, .zero c | .zero a, .finite b _ _, .zero c | .finite a _ _, .zero b, .zero c =>
    if (a != b) == c then addend else packZero format (mode == .rtn)
  | .zero _, _, _ | _, .zero _, _ => addend
  | .finite a m e, .finite b n f, .zero _ => pack format mode (a != b) (m * n) (e + f)
  | .finite a m e, .finite b n f, .finite c k g => packSum format mode (a != b, m * n, e + f) (c, k, g)

/-- `(left * right + addend) / 2`, rounded once. -/
def fmaHalved (format : Format) (mode : Mode) (left right addend : Nat) : Nat :=
  let half (bits : Nat) : Nat := div format mode bits (pack format .rne false 1 1)
  match unpack format left, unpack format right, unpack format addend with
  | .finite a m e, .finite b n f, .finite c k g =>
    packSum format mode (a != b, m * n, e + f - 1) (c, k, g - 1)
  | .finite a m e, .finite b n f, .zero _ => pack format mode (a != b) (m * n) (e + f - 1)
  | _, _, _ => half (fma format mode left right addend)

/-- To an integer, in the same format. -/
def round (format : Format) (mode : Mode) (bits : Nat) : Nat :=
  match unpack format bits with
  | .nan _ => quiet format bits
  | .infinity _ | .zero _ => bits
  | .finite negative m e =>
    if e ≥ 0 then bits
    else
      let kept := roundBits mode negative m (-e).toNat false
      if kept == 0 then packZero format negative else pack format .rne negative kept 0

def convert (source target : Format) (mode : Mode) (bits : Nat) : Nat :=
  match unpack source bits with
  | .infinity negative => packInfinity target negative
  | .zero negative => packZero target negative
  | .finite negative m e => pack target mode negative m e
  | .nan _ =>
    -- What x87 takes for an invalid operand, an unnormal, a pseudo-infinity or a pseudo-NaN, is the indefinite, negative and quiet with
    -- nothing else, as the 387 and after store it.
    if noncanonical source bits then
      signBit target true + target.maxExponent * 2 ^ target.fieldBits + (if target.explicit then 2 ^ target.fractionBits else 0) +
        2 ^ (target.fractionBits - 1)
    else
    -- The sign and the top of the payload, made quiet.
    let negative := (bits >>> (source.width - 1)) % 2 == 1
    let fraction := bits % 2 ^ source.fractionBits
    let payload := if target.fractionBits ≥ source.fractionBits
      then fraction <<< (target.fractionBits - source.fractionBits)
      else fraction >>> (source.fractionBits - target.fractionBits)
    let payload := payload ||| 2 ^ (target.fractionBits - 1)
    signBit target negative + target.maxExponent * 2 ^ target.fieldBits +
      (if target.explicit then 2 ^ target.fractionBits else 0) + payload

/-- To an integer of `width` bits, as two's complement. What doesn't fit has its low bits, and a caller that cares checks it. -/
def toInteger (format : Format) (mode : Mode) (width bits : Nat) : Nat :=
  match unpack format bits with
  | .nan _ | .infinity _ => 2 ^ (width - 1)
  | .zero _ => 0
  | .finite negative m e =>
    let magnitude := if e ≥ 0 then m <<< e.toNat else roundBits mode negative m (-e).toNat false
    if negative then (2 ^ width - magnitude % 2 ^ width) % 2 ^ width else magnitude % 2 ^ width

def ofUnsigned (format : Format) (mode : Mode) (value : Nat) : Nat :=
  pack format mode false value 0

def ofSigned (format : Format) (mode : Mode) (width value : Nat) : Nat :=
  if value ≥ 2 ^ (width - 1) then pack format mode true (2 ^ width - value) 0
  else pack format mode false value 0

/-- Which way two numbers compare, as `some` of whether the first is less and whether they are equal, unless one is a NaN. -/
def compare (format : Format) (left right : Nat) : Option (Bool × Bool) :=
  let order : Number → Number → Option (Bool × Bool)
    | .nan _, _ | _, .nan _ => none
    | .infinity a, .infinity b => some (a && !b, a == b)
    | .infinity a, _ => some (a, false)
    | _, .infinity b => some (!b, false)
    | .zero _, .zero _ => some (false, true)
    | .zero _, .finite b _ _ => some (!b, false)
    | .finite a _ _, .zero _ => some (a, false)
    | .finite a m e, .finite b n f =>
      if a != b then some (a, false)
      else
        let exponent := min e f
        let x := m <<< (e - exponent).toNat
        let y := n <<< (f - exponent).toNat
        some (if a then y < x else x < y, x == y)
  order (unpack format left) (unpack format right)

/-- What an architecture does with NaNs, which is all that differs between them here. The arithmetic above is that of x86. -/
structure NaNRules where
  /-- Whether a signaling NaN comes before a quiet one that is before it. -/
  signalingFirst : Bool := false
  /-- Whether the result is always the default NaN, whatever the operands. -/
  canonical : Bool := false
  /-- The sign of the default NaN. -/
  negativeDefault : Bool := false
  /-- Whether a conversion to an integer saturates, and a NaN is the largest. Otherwise, the semantics says what it is. -/
  saturating : Bool := false
  /-- The NaNs of MIPS before NaN2008, as qemu has them: any NaN that goes in makes the default, whose top bit of the fraction
  is clear. An implementation may do otherwise. -/
  legacyMips : Bool := false
  /-- Whether what is too small to be normal is told of what an operation would give before it is rounded, as Arm does, rather than
  after. -/
  tininessBefore : Bool := false
  /-- Whether a fused multiply-add of an infinity and a zero is invalid whatever the addend is, a quiet NaN too, as Arm, RISC-V and
  PowerPC have it, where x86 raises nothing of it then. -/
  infinityZeroInvalid : Bool := false
  deriving DecidableEq, Repr

/-- The first NaN operand, made quiet, and a default that is negative. -/
def NaNRules.x86 : NaNRules := { negativeDefault := true }
/-- A signaling NaN first, and a default that is positive: Arm, unless `FPCR.DN` is set. -/
def NaNRules.arm : NaNRules := { signalingFirst := true, tininessBefore := true, infinityZeroInvalid := true }
/-- The first NaN operand, and a default that is positive. -/
def NaNRules.powerpc : NaNRules := { infinityZeroInvalid := true }
/-- Always the default, which is positive. -/
def NaNRules.riscv : NaNRules := { canonical := true, saturating := true, infinityZeroInvalid := true }
/-- Any NaN makes the default. -/
def NaNRules.mips : NaNRules := { legacyMips := true }

private def isNaN (format : Format) (bits : Nat) : Bool :=
  match unpack format bits with
  | .nan _ => true
  | _ => false

private def isSignaling (format : Format) (bits : Nat) : Bool :=
  isNaN format bits && (noncanonical format bits || (bits >>> (format.fractionBits - 1)) % 2 == 0)

/-- The result of an operation with a NaN among its operands, by these rules. -/
def chooseNaN (rules : NaNRules) (format : Format) (operands : List Nat) : Nat :=
  if rules.legacyMips then format.maxExponent * 2 ^ format.fieldBits + (2 ^ (format.fractionBits - 1) - 1)
  else
  let positive := if rules.negativeDefault then defaultNaN format else defaultNaN format - 2 ^ (format.width - 1)
  if rules.canonical then positive else
  -- What isn't an operand at all, of x87, gives the default, as an invalid operation does.
  let given := operands.filter (!noncanonical format ·)
  let signaling := if rules.signalingFirst then given.find? (isSignaling format) else none
  match signaling, given.find? (isNaN format) with
  | some bits, _ | none, some bits => quiet format bits
  | none, none => positive

private def bool (value : Bool) : Nat := if value then 1 else 0

/-- An intrinsic by its name, on the bits of its operands, as its width and its bits. -/
private def evaluateX86 (name : String) (inputs : List Nat) : Option (Nat × Nat) := do
  let parts := name.splitOn "_"
  let at_ ← parts.findIdx? (· == "ieee754")
  let before := parts.take at_
  let widths := (parts.drop (at_ + 2)).filterMap String.toNat?
  let mode := before.getLast?.bind Mode.ofName
  let operation := "_".intercalate (if mode.isSome then before.dropLast else before)
  let first ← widths.head?
  let last := widths.getLast?.getD first
  let same (result : Format → Mode → Option Nat) : Option (Nat × Nat) := do
    let format ← formatOf first
    pure (first, ← result format (mode.getD .rne))
  let test (result : Format → Option Bool) : Option (Nat × Nat) := do
    let format ← formatOf first
    pure (1, bool (← result format))
  match operation, inputs with
  | "fadd", [x, y] => same fun format mode => add format mode x y
  | "fsub", [x, y] => same fun format mode => sub format mode x y
  | "fmul", [x, y] => same fun format mode => mul format mode x y
  | "fdiv", [x, y] => same fun format mode => div format mode x y
  | "fsqrt", [x] => same fun format mode => sqrt format mode x
  | "fmad", [x, y, z] => same fun format mode => fma format mode x y z
  | "fmadh", [x, y, z] => same fun format mode => fmaHalved format mode x y z
  | "fround", [x] | "froundq", [x] => same fun format mode => round format mode x
  | "fconvert", [x] =>
    pure (last, convert (← formatOf first) (← formatOf last) (mode.getD .rne) x)
  | "cast_sint", [x] | "cast_int", [x] =>
    pure (last, toInteger (← formatOf first) (mode.getD .rtz) last x)
  | "cast_sfloat", [x] => pure (last, ofSigned (← formatOf last) (mode.getD .rne) first x)
  | "cast_float", [x] => pure (last, ofUnsigned (← formatOf last) (mode.getD .rne) x)
  | "forder", [x, y] | "forders", [x, y] => test fun format => pure ((compare format x y).any (·.1))
  | "fgt", [x, y] => test fun format => pure ((compare format y x).any (·.1))
  | "fge", [x, y] => test fun format => pure ((compare format x y).any fun order => !order.1)
  | "feq", [x, y] => test fun format => pure ((compare format x y).any (·.2))
  | "is_nan", [x] => test fun format => pure (match unpack format x with | .nan _ => true | _ => false)
  | "is_inf", [x] => test fun format => pure (match unpack format x with | .infinity _ => true | _ => false)
  | "is_fzero", [x] => test fun format => pure (match unpack format x with | .zero _ => true | _ => false)
  | _, _ => none

/-! ## What isn't an operation of IEEE 754

The functions of x87, `F2XM1`, `FSIN`, `FCOS`, `FPTAN`, `FPATAN`, `FYL2X` and `FYL2XP1`, are worked out in fixed point of many more bits
than the format has, and rounded once: within an ulp of what x87 gives, which isn't always the nearest either. `FPREM` and `FPREM1` and
`FXTRACT` are exact, as are the estimates of Arm, `FRECPE` and `FRSQRTE`, which its pseudocode says to the bit. Those of SSE, `RCPSS`
and `RSQRTSS`, are to 12 bits, as the manual says of them, and no more than that is the same as a processor's. -/

/-- A real number in fixed point, as an integer of `2 ^ -precision`. -/
private def fixedMul (precision : Nat) (a b : Int) : Int := (a * b) / (2 ^ precision : Nat)

private def fixedDiv (precision : Nat) (a b : Int) : Int := if b == 0 then 0 else (a * (2 ^ precision : Nat)) / b

/-- `atanh (1 / k)`, or with `alternating` `atan (1 / k)`, of `precision` bits: the sum of `± 1 / (n k ^ n)` of odd `n`. -/
private def arcOfRecip (precision k : Nat) (alternating : Bool) : Int := Id.run do
  let one : Int := (2 ^ precision : Nat)
  let mut power : Int := one / k
  let mut total : Int := 0
  let mut n := 1
  let mut negative := false
  for _ in List.range (precision + 2) do
    if power == 0 then break
    let term := power / n
    total := if negative then total - term else total + term
    power := power / (k * k)
    n := n + 2
    if alternating then negative := !negative
  pure total

/-- `ln 2`, as `2 atanh (1 / 3)`. -/
private def ln2Fixed (precision : Nat) : Int := 2 * arcOfRecip (precision + 16) 3 false / (2 ^ 16 : Nat)

/-- `π`, as Machin's `16 atan (1 / 5) - 4 atan (1 / 239)`. -/
private def piFixed (precision : Nat) : Int :=
  (16 * arcOfRecip (precision + 16) 5 true - 4 * arcOfRecip (precision + 16) 239 true) / (2 ^ 16 : Nat)

/-- `e ^ x` of `|x| ≤ 1`. -/
private def expFixed (precision : Nat) (x : Int) : Int := Id.run do
  let one : Int := (2 ^ precision : Nat)
  let mut term := one
  let mut total := one
  for n in List.range (precision + 2) do
    term := fixedMul precision term x / (n + 1)
    if term == 0 then break
    total := total + term
  pure total

/-- `atanh z` of `|z| ≤ 1 / 2`. -/
private def atanhFixed (precision : Nat) (z : Int) : Int := Id.run do
  let square := fixedMul precision z z
  let mut power := z
  let mut total : Int := 0
  let mut n := 1
  for _ in List.range (precision + 2) do
    if power == 0 then break
    total := total + power / n
    power := fixedMul precision power square
    n := n + 2
  pure total

/-- `ln (1 + x)` of `x > -1`, as `2 atanh (x / (2 + x))`, which keeps what is small of a small `x`; of a large one, by its power of two
first. -/
private def ln1pFixed (precision : Nat) (x : Int) : Int :=
  let one : Int := (2 ^ precision : Nat)
  if x.natAbs ≤ (one / 2).toNat then 2 * atanhFixed precision (fixedDiv precision x (2 * one + x))
  else
    -- `1 + x = s 2 ^ k`, with `s` in [1, 2).
    let whole := one + x
    let k : Int := (Nat.log2 whole.toNat : Int) - precision
    let s : Int := if k ≥ 0 then whole / (2 ^ k.toNat : Nat) else whole * (2 ^ (-k).toNat : Nat)
    k * ln2Fixed precision + 2 * atanhFixed precision (fixedDiv precision (s - one) (s + one))

/-- `sin x` and `cos x` of `|x| ≤ π / 4`. -/
private def sinCosSmall (precision : Nat) (x : Int) : Int × Int := Id.run do
  let one : Int := (2 ^ precision : Nat)
  let square := fixedMul precision x x
  let mut sinTerm := x
  let mut sinTotal := x
  let mut cosTerm := one
  let mut cosTotal := one
  let mut n := 1
  for _ in List.range (precision + 2) do
    if sinTerm == 0 && cosTerm == 0 then break
    cosTerm := -(fixedMul precision cosTerm square) / ((n + 1) * n)
    sinTerm := -(fixedMul precision sinTerm square) / ((n + 2) * (n + 1))
    cosTotal := cosTotal + cosTerm
    sinTotal := sinTotal + sinTerm
    n := n + 2
  pure (sinTotal, cosTotal)

/-- `sin x` and `cos x`, of `x` brought to within `π / 4` of a multiple of `π / 2`. -/
private def sinCosFixed (precision : Nat) (x : Int) : Int × Int :=
  let half := piFixed (precision + 80) / 2
  let wide := x * (2 ^ 80 : Nat)
  let quarter := (wide + half / 2).fdiv half
  let rest := (wide - quarter * half) / (2 ^ 80 : Nat)
  let (s, c) := sinCosSmall precision rest
  match quarter.emod 4 with
  | 0 => (s, c)
  | 1 => (c, -s)
  | 2 => (-s, -c)
  | _ => (-c, s)

/-- The square root of what is in fixed point. -/
private def sqrtFixed (precision : Nat) (x : Int) : Int := (Nat.sqrt (x.toNat * 2 ^ precision) : Int)

/-- `atan t`: of more than 1, `π / 2 - atan (1 / t)`; and of what is within 1, halved three times by `t / (1 + √(1 + t²))`. -/
private def atanFixed (precision : Nat) (t : Int) : Int := Id.run do
  let one : Int := (2 ^ precision : Nat)
  if t < 0 then return -(atanFixed' precision (-t))
  pure (atanFixed' precision t)
where
  atanFixed' (precision : Nat) (t : Int) : Int := Id.run do
    let one : Int := (2 ^ precision : Nat)
    if t > one then return piFixed precision / 2 - atanSmall precision (fixedDiv precision one t)
    pure (atanSmall precision t)
  atanSmall (precision : Nat) (t : Int) : Int := Id.run do
    let one : Int := (2 ^ precision : Nat)
    let mut t := t
    for _ in List.range 3 do
      t := fixedDiv precision t (one + sqrtFixed precision (one + fixedMul precision t t))
    let square := fixedMul precision t t
    let mut power := t
    let mut total : Int := 0
    let mut n := 1
    let mut negative := false
    for _ in List.range (precision + 2) do
      if power == 0 then break
      let term := power / n
      total := if negative then total - term else total + term
      power := fixedMul precision power square
      n := n + 2
      negative := !negative
    pure (8 * total)

/-- A finite value as fixed point. -/
private def toFixed (precision : Nat) (negative : Bool) (mantissa : Nat) (exponent : Int) : Int :=
  let magnitude : Int := if exponent + precision ≥ 0 then (mantissa * 2 ^ (exponent + precision).toNat : Nat)
    else (mantissa / 2 ^ (-(exponent + precision)).toNat : Nat)
  if negative then -magnitude else magnitude

/-- What is in fixed point, rounded to a format, and whether it is something other than zero below what it keeps. -/
private def ofFixed (format : Format) (mode : Mode) (precision : Nat) (value : Int) : Nat :=
  -- The last bit is sticky, as there is always more of what isn't exact.
  pack format mode (value < 0) (value.natAbs * 2 + 1) (-(precision : Int) - 1)

/-- How many bits of fixed point an operand of exponent `exponent` needs, to have 160 of its own and more than any result's. -/
private def precisionFor (exponents : List Int) : Nat :=
  let smallest := exponents.foldl min 0
  min 17000 (256 + (-smallest).toNat)

/-- The integer that is nearest to a value, or by `truncate` towards zero, as its sign and magnitude. -/
private def integerOf (truncate : Bool) (negative : Bool) (mantissa : Nat) (exponent : Int) : Nat :=
  if exponent ≥ 0 then mantissa * 2 ^ exponent.toNat
  else if truncate then mantissa / 2 ^ (-exponent).toNat
  else roundBits .rne negative mantissa (-exponent).toNat false

/-- The bits of a format with exponent field `biased` and what is below it. -/
private def bitsOf (format : Format) (negative : Bool) (biased field : Nat) : Nat :=
  signBit format negative + biased * 2 ^ format.fieldBits + field

/-- `FPREM` and `FPREM1`: the remainder, exact, of a quotient towards zero or to nearest, and the status of the quotient's last three
bits in C0, C3 and C1, with C2 when it is only part of the way, as of more than 63 binary places, which goes 63 at a time. -/
private def remainder (nearest : Bool) (format : Format) (x y : Nat) : Nat × Nat :=
  match unpack format x, unpack format y with
  | .nan _, _ | _, .nan _ => (chooseNaN .x86 format [x, y], 0)
  | .infinity _, _ | _, .zero _ => (defaultNaN format, 0)
  | .zero _, _ | _, .infinity _ => (x, 0)
  | .finite xs xm xe, .finite _ ym ye =>
    -- Of the exponents of their leading bits.
    let difference := (xe + bitLength xm) - (ye + bitLength ym)
    let low := min xe ye
    let a := xm * 2 ^ (xe - low).toNat
    let b := ym * 2 ^ (ye - low).toNat
    if difference ≥ 64 then
      -- Part of the way: of `y 2 ^ (difference - N)`, towards zero whichever it is, where `N` is of 32 to 63 bits, as the processor
      -- has it: `32 + difference mod 32`.
      let scaled := b * 2 ^ (difference - 32 - difference % 32).toNat
      let r := a % scaled
      (pack format .rne xs r low, 0x400)
    else
      let q := a / b
      let r := a % b
      let (q, r, flip) :=
        if nearest && (2 * r > b || (2 * r == b && q % 2 == 1)) then (q + 1, b - r, true) else (q, r, false)
      let negative := if flip then !xs else xs
      let status := (if q % 2 == 1 then 0x200 else 0) + (if q / 2 % 2 == 1 then 0x4000 else 0) + (if q / 4 % 2 == 1 then 0x100 else 0)
      (if r == 0 then packZero format xs else pack format .rne negative r low, status)

/-- `FXTRACT`: the exponent, as a number, and the significand, of 1 to 2. -/
private def extract (format : Format) (exponentOf : Bool) (x : Nat) : Nat :=
  match unpack format x with
  | .nan _ => quiet format x
  | .infinity negative => if exponentOf then packInfinity format false else packInfinity format negative
  | .zero negative => if exponentOf then packInfinity format true else packZero format negative
  | .finite negative m e =>
    let top := e + bitLength m - 1
    if exponentOf then pack format .rne (top < 0) top.natAbs 0
    else pack format .rne negative m (e - top)

/-- `FBLD`: 18 decimal digits, two to a byte from the lowest, and the sign in the top bit. -/
private def ofDecimal (format : Format) (bits : Nat) : Nat :=
  let value := (List.range 18).foldr (fun index total => total * 10 + (bits >>> (4 * index)) % 16) 0
  let negative := (bits >>> 79) % 2 == 1
  if value == 0 then packZero format negative else pack format .rne negative value 0

/-- `FBSTP`: what rounds to 18 decimal digits, and otherwise the decimal indefinite. -/
private def toDecimal (format : Format) (mode : Mode) (bits : Nat) : Nat :=
  let indefinite := 0xffff * 2 ^ 64 + 0xc0 * 2 ^ 56
  match unpack format bits with
  | .nan _ | .infinity _ => indefinite
  | .zero negative => if negative then 2 ^ 79 else 0
  | .finite negative m e =>
    let value := if e ≥ 0 then m * 2 ^ e.toNat else roundBits mode negative m (-e).toNat false
    if value ≥ 10 ^ 18 then indefinite
    else
      let digits := (List.range 18).foldl (fun (total, rest) index => (total + (rest % 10) * 2 ^ (4 * index), rest / 10)) (0, value)
      digits.1 + (if negative then 2 ^ 79 else 0)

/-- The estimate of `FRECPE`, of 9 bits of an operand: `RecipEstimate`. -/
private def recipEstimate (a : Nat) : Nat :=
  let a := a * 2 + 1
  let b := 2 ^ 19 / a
  (b + 1) / 2

/-- The estimate of `FRSQRTE`: `RecipSqrtEstimate`. -/
private def recipSqrtEstimate (a : Nat) : Nat := Id.run do
  let a := if a < 256 then a * 2 + 1 else (a / 2 * 2 + 1) * 2
  let mut b := 512
  for _ in List.range 512 do
    if a * (b + 1) * (b + 1) ≥ 2 ^ 28 then break
    b := b + 1
  pure ((b + 1) / 2)

/-- `FPRecipEstimate` and `FPRSqrtEstimate` of Arm, of a number that isn't a NaN, an infinity or a zero, and isn't negative of a root.
`flushed` says that a denormal is a zero, as the standard value of the FPSCR that NEON goes by has it. -/
private def armEstimate (format : Format) (mode : Mode) (root : Bool) (bits : Nat) : Nat :=
  let width := format.width
  let fractionBits := format.fractionBits
  let negative := (bits >>> (width - 1)) % 2 == 1
  let biasedField := (bits >>> fractionBits) % 2 ^ format.exponentBits
  let fraction := bits % 2 ^ fractionBits
  if !root then
    -- What is too small to have a reciprocal in the format overflows, by the rounding mode.
    let tiny := biasedField == 0 && fraction < 2 ^ (fractionBits - 2)
    if tiny then
      let toInfinity := match mode with
        | .rtp => !negative
        | .rtn => negative
        | .rtz => false
        | _ => true
      if toInfinity then packInfinity format negative
      else bitsOf format negative (format.maxExponent - 1) (2 ^ fractionBits - 1)
    else
      let (exponent, fraction) : Int × Nat :=
        if biasedField == 0 then
          if fraction / 2 ^ (fractionBits - 1) == 0 then (-1, fraction % 2 ^ (fractionBits - 2) * 4)
          else (0, fraction % 2 ^ (fractionBits - 1) * 2)
        else (biasedField, fraction)
      let scaled := 256 + fraction / 2 ^ (fractionBits - 8)
      let resultExponent : Int := 2 * (format.bias : Int) - 1 - exponent
      let estimate := recipEstimate scaled % 256
      let field := estimate * 2 ^ (fractionBits - 8)
      let (resultExponent, field) :=
        if resultExponent == 0 then (0, (2 ^ fractionBits + field) / 2)
        else if resultExponent == -1 then (0, (2 ^ fractionBits + field) / 4)
        else (resultExponent, field)
      bitsOf format negative resultExponent.toNat field
  else
    let (exponent, fraction) : Int × Nat := Id.run do
      if biasedField != 0 then return (biasedField, fraction)
      let mut exponent : Int := 0
      let mut fraction := fraction
      for _ in List.range fractionBits do
        if fraction / 2 ^ (fractionBits - 1) == 1 then break
        fraction := fraction % 2 ^ (fractionBits - 1) * 2
        exponent := exponent - 1
      pure (exponent, fraction % 2 ^ (fractionBits - 1) * 2)
    let scaled := if exponent % 2 == 0 then 256 + fraction / 2 ^ (fractionBits - 8) else 128 + fraction / 2 ^ (fractionBits - 7)
    let resultExponent := (3 * (format.bias : Int) - 1 - exponent) / 2
    let estimate := recipSqrtEstimate scaled % 256
    bitsOf format false resultExponent.toNat (estimate * 2 ^ (fractionBits - 8))

/-- `RCPSS` and `RSQRTSS`: to 12 bits, a little less than the reciprocal, as processors give it, of what isn't a denormal, which is a
zero to them. -/
private def sseEstimate (format : Format) (root : Bool) (bits : Nat) : Nat :=
  match unpack format bits with
  | .nan _ => quiet format bits
  | .infinity negative => if root && negative then defaultNaN format else packZero format negative
  | .zero negative => packInfinity format negative
  | .finite negative m e =>
    if (bits >>> format.fractionBits) % 2 ^ format.exponentBits == 0 then packInfinity format negative
    else if root && negative then defaultNaN format
    else
      let precision := 200
      let value := toFixed precision false m e
      let one : Int := (2 ^ precision : Nat)
      let result := if root then fixedDiv precision one (sqrtFixed precision value) else fixedDiv precision one value
      -- Of 12 bits, to the nearest; what is less than a normal number is a zero.
      let top := (Nat.log2 result.toNat : Int) - precision
      let shift := Nat.log2 result.toNat - 11
      let kept := roundBits .rne false result.toNat shift false * 2 ^ shift
      if top < format.lowest + format.fractionBits then packZero format negative
      else pack format .rtz negative kept (-(precision : Int))

/-- An operation that this part serves, by its name without its rounding mode and formats. -/
def specialOperations : List String :=
  ["f2xm1", "fsin", "fcos", "ftan", "fatan2", "fyl2x", "fyl2xp1", "fexponent", "fsignificand", "fprem", "fprem1", "fprem_status",
    "fprem1_status", "frcp", "frsqrt", "frecpe", "frsqrte", "fbld", "fbstp"]

/-- What an operation of these gives, if `name` is of one, as its width and its bits. -/
def evaluateSpecial (rules : NaNRules) (name : String) (inputs : List Nat) : Option (Nat × Nat) := do
  let parts := name.splitOn "_"
  let at_ ← parts.findIdx? (· == "ieee754")
  let before := parts.take at_
  let mode := before.getLast?.bind Mode.ofName
  let operation := "_".intercalate (if mode.isSome then before.dropLast else before)
  if !specialOperations.contains operation then none
  let width ← ((parts.drop (at_ + 2)).filterMap String.toNat?).head?
  let format ← formatOf width
  let mode := mode.getD .rne
  let nan (operands : List Nat) : Nat × Nat := (width, chooseNaN rules format operands)
  match operation, inputs with
  | "fprem", [x, y] => pure (width, (remainder false format x y).1)
  | "fprem1", [x, y] => pure (width, (remainder true format x y).1)
  | "fprem_status", [x, y] => pure (16, (remainder false format x y).2)
  | "fprem1_status", [x, y] => pure (16, (remainder true format x y).2)
  | "fbld", [x] => pure (width, ofDecimal format x)
  | "fbstp", [x] => pure (width, toDecimal format mode x)
  | "fexponent", [x] => pure (width, extract format true x)
  | "fsignificand", [x] => pure (width, extract format false x)
  | "frcp", [x] => pure (width, sseEstimate format false x)
  | "frsqrt", [x] => pure (width, sseEstimate format true x)
  | "frecpe", [x] | "frsqrte", [x] =>
    let root := operation == "frsqrte"
    match unpack format x with
    | .nan _ => pure (nan [x])
    | .infinity negative =>
      if root && negative then pure (width, chooseNaN rules format []) else pure (width, packZero format (negative && !root))
    | .zero negative => pure (width, packInfinity format negative)
    | .finite negative _ _ =>
      if root && negative then pure (width, chooseNaN rules format [])
      else pure (width, armEstimate format mode root x)
  | "f2xm1", [x] =>
    match unpack format x with
    | .nan _ => pure (nan [x])
    | .infinity negative => pure (width, if negative then pack format mode true 1 0 else x)
    | .zero _ => pure (width, x)
    | .finite negative m e =>
      let precision := precisionFor [e + bitLength m]
      let value := toFixed precision negative m e
      pure (width, ofFixed format mode precision (expFixed precision (fixedMul precision value (ln2Fixed precision)) - (2 ^ precision : Nat)))
  | "fsin", [x] | "fcos", [x] | "ftan", [x] =>
    match unpack format x with
    | .nan _ => pure (nan [x])
    | .infinity _ => pure (width, defaultNaN format)
    | .zero _ => pure (width, if operation == "fcos" then pack format mode false 1 0 else x)
    | .finite negative m e =>
      -- Of 2^63 or more, the operand is as it was, which C2 would say.
      if e + bitLength m > 63 then return (width, x)
      let precision := precisionFor [e + bitLength m]
      let (s, c) := sinCosFixed precision (toFixed precision negative m e)
      let result := match operation with
        | "fsin" => s
        | "fcos" => c
        | _ => fixedDiv precision s c
      pure (width, ofFixed format mode precision result)
  | "fatan2", [y, x] =>
    match unpack format y, unpack format x with
    | .nan _, _ | _, .nan _ => pure (nan [y, x])
    | ys, xs =>
      let precision := 256
      let pi := piFixed precision
      let negativeY := (y >>> (format.width - 1)) % 2 == 1
      let negativeX := (x >>> (format.width - 1)) % 2 == 1
      let signed (value : Int) : Nat × Nat := (width, ofFixed format mode precision (if negativeY then -value else value))
      match ys, xs with
      | .zero _, _ => pure (if negativeX then signed pi else (width, packZero format negativeY))
      | .infinity _, .infinity _ => pure (signed (if negativeX then 3 * pi / 4 else pi / 4))
      | .infinity _, _ | _, .zero _ => pure (signed (pi / 2))
      | _, .infinity _ => pure (if negativeX then signed pi else (width, packZero format negativeY))
      | .finite _ ym ye, .finite _ xm xe =>
        -- Of the quotient of their magnitudes, from the quadrant of x.
        let wide := precisionFor [ye + bitLength ym - (xe + bitLength xm)]
        let ratio : Int := ((ym * 2 ^ wide : Nat) : Int) * (if ye ≥ xe then (2 ^ (ye - xe).toNat : Nat) else 1) /
          ((xm * (if xe > ye then 2 ^ (xe - ye).toNat else 1) : Nat) : Int)
        let angle := atanFixed wide ratio
        let angle := if negativeX then piFixed wide - angle else angle
        pure (width, ofFixed format mode wide (if negativeY then -angle else angle))
      | _, _ => pure (nan [y, x])
  | "fyl2x", [y, x] | "fyl2xp1", [y, x] =>
    let plusOne := operation == "fyl2xp1"
    match unpack format y, unpack format x with
    | .nan _, _ | _, .nan _ => pure (nan [y, x])
    | ys, xs =>
      let negativeY := (y >>> (format.width - 1)) % 2 == 1
      -- What `log2` is of: x, or 1 + x, as its sign and whether it is 0, 1 or infinite.
      let precision := precisionFor (match xs with | .finite _ m e => [e + bitLength m] | _ => [])
      let one : Int := (2 ^ precision : Nat)
      let argument : Option Int := match xs with
        | .finite negative m e => some (toFixed precision negative m e + (if plusOne then one else 0))
        | .zero _ => some (if plusOne then one else 0)
        | _ => none
      match xs, argument with
      | .infinity true, _ => pure (width, defaultNaN format)
      | .infinity false, _ =>
        match ys with
        | .zero _ => pure (width, defaultNaN format)
        | _ => pure (width, packInfinity format negativeY)
      | _, some value =>
        if value < 0 then pure (width, defaultNaN format)
        else if value == 0 then
          match ys with
          | .zero _ => pure (width, defaultNaN format)
          | _ => pure (width, packInfinity format !negativeY)
        else
          match ys with
          | .infinity _ =>
            if value == one then pure (width, defaultNaN format)
            else pure (width, packInfinity format (if value > one then negativeY else !negativeY))
          | .zero _ => pure (width, packZero format (if value ≥ one then negativeY else !negativeY))
          | .finite yn ym ye =>
            let logarithm := fixedDiv precision (if plusOne then ln1pFixed precision (value - one) else ln1pFixed precision (value - one))
              (ln2Fixed precision)
            if logarithm == 0 then pure (width, packZero format (if value ≥ one then yn else !yn))
            else
              let product := (ym : Int) * logarithm
              pure (width, pack format mode ((product < 0) != yn) (product.natAbs * 2 + 1) (ye - precision - 1))
          | _ => pure (nan [y, x])
      | _, _ => pure (nan [y, x])
  | _, _ => none

/-- An intrinsic by its name, by the rules of an architecture for NaNs. The arithmetic is the same. A NaN that an operation makes
out of nothing is the default of x86 there, and this says what it is here. -/
def evaluateWith (rules : NaNRules) (name : String) (inputs : List Nat) : Option (Nat × Nat) := do
  if let some result := evaluateSpecial rules name inputs then return result
  let (width, bits) ← evaluateX86 name inputs
  let parts := name.splitOn "_"
  let widths := (parts.reverse.takeWhile fun part => part.toNat?.isSome).reverse.filterMap String.toNat?
  -- Of x86, what doesn't fit, after it is rounded, or isn't a number, is the integer indefinite: the top bit of a signed one, and all
  -- ones of an unsigned one, as `CVTSD2SI`, `FIST` and `VCVTSD2USI` give it.
  if parts.headD "" == "cast" && ["sint", "int"].contains (parts.getD 1 "") && rules == .x86 then
    if let (some source, some target, [input]) := (widths.head?, widths.getLast?, inputs) then
      if let some format := formatOf source then
        let signed := parts.getD 1 "" == "sint"
        let indefinite := if signed then 2 ^ (target - 1) else 2 ^ target - 1
        let mode := (parts.getD 2 "" |> Mode.ofName).getD .rtz
        match unpack format input with
        | .nan _ | .infinity _ => return (target, indefinite)
        | .zero _ => pure ()
        | .finite negative m e =>
          let magnitude := if e ≥ 0 then m <<< e.toNat else roundBits mode negative m (-e).toNat false
          let fits := if signed then (if negative then magnitude ≤ 2 ^ (target - 1) else magnitude < 2 ^ (target - 1))
            else (!negative || magnitude == 0) && magnitude < 2 ^ target
          if !fits then return (target, indefinite)
  if parts.headD "" == "cast" && ["sint", "int"].contains (parts.getD 1 "") && rules.saturating then
    if let (some source, some target, [input]) := (widths.head?, widths.getLast?, inputs) then
      if let some format := formatOf source then
        let signed := parts.getD 1 "" == "sint"
        let highest := if signed then 2 ^ (target - 1) - 1 else 2 ^ target - 1
        let lowest := if signed then 2 ^ (target - 1) else 0
        let mode := (parts.getD 2 "" |> Mode.ofName).getD .rtz
        match unpack format input with
        | .nan _ => return (target, highest)
        | .infinity negative => return (target, if negative then lowest else highest)
        | .zero _ => return (target, 0)
        | .finite negative m e =>
          let magnitude := if e ≥ 0 then m <<< e.toNat else roundBits mode negative m (-e).toNat false
          if negative then
            if signed then
              return (target, if magnitude ≥ 2 ^ (target - 1) then lowest else (2 ^ target - magnitude) % 2 ^ target)
            else return (target, 0)
          else return (target, if magnitude > highest then highest else magnitude)
  -- A NaN that is converted is by the rules of the format that it goes to.
  if parts.headD "" == "fconvert" then
    if let (some source, some target, [input]) := (widths.head?, widths.getLast?, inputs) then
      if let (some from_, some to_) := (formatOf source, formatOf target) then
        if isNaN from_ input && rules.canonical then
          return (target, chooseNaN rules to_ [])
        if isNaN from_ input && rules.legacyMips then
          return (target, chooseNaN rules to_ [])
  let arithmetic := ["fadd", "fsub", "fmul", "fdiv", "fsqrt", "fmad", "fmadh", "fround", "froundq"].contains (parts.headD "")
  match formatOf width with
  | some format =>
    if arithmetic && (inputs.any (isNaN format) || bits == defaultNaN format) then
      pure (width, chooseNaN rules format inputs)
    else pure (width, bits)
  | none => pure (width, bits)

/-- By the rules of x86. -/
def evaluate : String → List Nat → Option (Nat × Nat) := evaluateWith .x86

/-- The exceptions of IEEE 754 that an operation raises. -/
structure Raised where
  invalid : Bool := false
  divideByZero : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  inexact : Bool := false
  /-- Of what x86 alone says: that an operand is a denormal. -/
  denormal : Bool := false
  deriving DecidableEq, Repr

/-- Whether bits are a denormal of a format. -/
def isDenormal (format : Format) (bits : Nat) : Bool :=
  (bits >>> format.fieldBits) % 2 ^ format.exponentBits == 0 && bits % 2 ^ format.fieldBits != 0

/-- A denormal as a zero of its sign. -/
def flush (format : Format) (bits : Nat) : Nat :=
  if isDenormal format bits then signBit format (bits >>> (format.width - 1) % 2 == 1) else bits

/-- The formats of the operands and of the result of what is named, where they are floating point. -/
def formatsOf (name : String) : Option Format × Option Format :=
  let parts := name.splitOn "_"
  match parts.findIdx? (· == "ieee754") with
  | none => (none, none)
  | some at_ =>
    let widths := (parts.drop (at_ + 2)).filterMap String.toNat?
    let first := widths.head?.bind formatOf
    let last := widths.getLast?.bind formatOf
    match parts.headD "" with
    | "fadd" | "fsub" | "fmul" | "fdiv" | "fsqrt" | "fmad" | "fmadh" | "fround" | "froundq" | "fconvert" => (first, last)
    | "frecpe" | "frsqrte" | "frcp" | "frsqrt" => (first, last)
    | "forder" | "forders" | "fgt" | "fge" | "feq" => (first, none)
    | "cast" =>
      match parts.getD 1 "" with
      | "sint" | "int" => (first, none)
      | _ => (none, last)
    | _ => (none, none)

/-- The result of what is named for one that must not be a NaN of its operands. -/
def defaultFor (rules : NaNRules) (name : String) (bits : Nat) : Nat :=
  match (formatsOf name).2 with
  | some format => if isNaN format bits then chooseNaN { rules with signalingFirst := false } format [] else bits
  | none => bits

/-- The name of an operation with another rounding mode, as it is the same operation but for that. -/
private def withMode (name mode : String) : String :=
  "_".intercalate ((name.splitOn "_").map fun part => if (Mode.ofName part).isSome then mode else part)

/-- A format of the same precision with four more bits of exponent, in which an operation of the other is rounded as if there were no
end to its exponents, as IEEE 754 says overflow and underflow of. -/
private def widened (format : Format) : Format := { format with exponentBits := format.exponentBits + 4, explicit := false }

/-- What an arithmetic operation of `source` that gives `target` comes to with the precision of `target` and as many exponents as it
takes, in a mode. -/
private def unboundedResult (operation : String) (source target : Format) (mode : Mode) (inputs : List Nat) : Option Number :=
  let wide := widened source
  -- The operands, which a format of more exponents has as they are.
  match operation, inputs.map (convert source wide .rne) with
  | "fadd", [x, y] => some (unpack wide (add wide mode x y))
  | "fsub", [x, y] => some (unpack wide (sub wide mode x y))
  | "fmul", [x, y] => some (unpack wide (mul wide mode x y))
  | "fdiv", [x, y] => some (unpack wide (div wide mode x y))
  | "fsqrt", [x] => some (unpack wide (sqrt wide mode x))
  | "fmad", [x, y, z] => some (unpack wide (fma wide mode x y z))
  | "fmadh", [x, y, z] => some (unpack wide (fmaHalved wide mode x y z))
  | "fconvert", [_] => inputs.head?.map fun x => unpack (widened target) (convert source (widened target) mode x)
  | _, _ => none

/-- Whether a number is past the largest finite one of a format, or below its smallest normal one, by its highest bit. -/
private def beyond (format : Format) : Number → Bool
  | .finite _ mantissa exponent => exponent + Nat.log2 mantissa ≥ ((format.maxExponent - 1 - format.bias : Nat) : Int) + 1
  | .infinity _ => true
  | _ => false

private def tiny (format : Format) : Number → Bool
  | .finite _ mantissa exponent => exponent + Nat.log2 mantissa < 1 - (format.bias : Int)
  | _ => false

/-- A number of a sign, `m * 2 ^ e`, rounded to an integer in a mode: its magnitude, and whether it wasn't one already. -/
private def roundToInteger (negative : Bool) (m : Nat) (e : Int) (mode : Mode) : Nat × Bool :=
  if e ≥ 0 then (m <<< e.toNat, false)
  else
    let shift := (-e).toNat
    let kept := m >>> shift
    let rest := m % 2 ^ shift
    let half := 2 ^ (shift - 1)
    let up := match mode with
      | .rne => rest > half || (rest == half && kept % 2 == 1)
      | .rna => rest ≥ half
      | .rtz => false
      | .rtp => !negative && rest != 0
      | .rtn => negative && rest != 0
      | .rod => rest != 0 && kept % 2 == 0
    (if up then kept + 1 else kept, rest != 0)

/-- What an operation of these raises, if `name` is of one. -/
def raisedSpecial (name : String) (inputs : List Nat) (result : Nat) : Option Raised := do
  let parts := name.splitOn "_"
  let at_ ← parts.findIdx? (· == "ieee754")
  let before := parts.take at_
  let mode := before.getLast?.bind Mode.ofName
  let operation := "_".intercalate (if mode.isSome then before.dropLast else before)
  if !specialOperations.contains operation then none
  let width ← ((parts.drop (at_ + 2)).filterMap String.toNat?).head?
  let format ← formatOf width
  let signaling := inputs.any (isSignaling format)
  let anyNaN := inputs.any (isNaN format)
  let denormal := inputs.any fun bits => (bits >>> format.fieldBits) % 2 ^ format.exponentBits == 0 && bits % 2 ^ format.fieldBits != 0
  let zeroIn := inputs.any fun bits => match unpack format bits with | .zero _ => true | _ => false
  let resultNaN := isNaN format result
  match operation with
  | "fbld" => some {}
  | "fbstp" =>
    let input := inputs.headD 0
    let invalid := result == 0xffff * 2 ^ 64 + 0xc0 * 2 ^ 56
    let inexact := match unpack format input with
      | .finite _ m e => e < 0 && m % 2 ^ (-e).toNat != 0
      | _ => false
    some { invalid, inexact := inexact && !invalid }
  | "frcp" | "frsqrt" => some {}
  | "frecpe" | "frsqrte" =>
    let input := inputs.headD 0
    let negative := (input >>> (format.width - 1)) % 2 == 1
    -- What is too small to have a reciprocal overflows, as `armEstimate` has it.
    let tiny := operation == "frecpe" && (match unpack format input with | .finite _ _ _ => true | _ => false) &&
      (input >>> format.fractionBits) % 2 ^ format.exponentBits == 0 && input % 2 ^ format.fractionBits < 2 ^ (format.fractionBits - 2)
    if signaling then return { invalid := true }
    if anyNaN then return {}
    match unpack format input with
    | .zero _ => some { divideByZero := true }
    | .infinity _ => some { invalid := operation == "frsqrte" && negative }
    | _ => some { invalid := operation == "frsqrte" && negative, overflow := tiny, inexact := tiny }
  | "fprem" | "fprem1" | "fprem_status" | "fprem1_status" =>
    let invalid := signaling || (!anyNaN && (match inputs with
      | [x, y] => (match unpack format x with | .infinity _ => true | _ => false) || (match unpack format y with | .zero _ => true | _ => false)
      | _ => false))
    some { invalid, denormal := denormal && !anyNaN }
  | "fexponent" | "fsignificand" =>
    some { invalid := signaling, divideByZero := operation == "fexponent" && zeroIn && !anyNaN, denormal := denormal && !anyNaN }
  | _ =>
    -- What is out of the domain is invalid, of a NaN that it made; a pole divides by zero; and what isn't exact is inexact, which
    -- of these is all but what is zero or infinite.
    let made := resultNaN && !anyNaN
    let infiniteIn := inputs.any fun bits => match unpack format bits with | .infinity _ => true | _ => false
    let infiniteResult := match unpack format result with | .infinity _ => true | _ => false
    let pole := (operation == "fyl2x" || operation == "fyl2xp1") && infiniteResult &&
      !inputs.any fun bits => match unpack format bits with | .infinity _ => true | _ => false
    let exactResult := match unpack format result with
      | .zero _ | .infinity _ | .nan _ => true
      | _ => zeroIn && operation != "fcos" && operation != "fatan2"
    some { invalid := signaling || made, divideByZero := pole, inexact := !exactResult && !anyNaN && !infiniteIn,
           denormal := denormal && !anyNaN }

/-- What an operation that gave `result` raises. Whether a result was rounded is whether rounding up and down come to
something else, which takes evaluating it twice, so that `known` says not to when `inexact` won't change anything. -/
def raisedBy (rules : NaNRules) (name : String) (inputs : List Nat) (result : Nat) (known : Bool := false) : Raised := Id.run do
  if let some raised := raisedSpecial name inputs result then return raised
  let parts := name.splitOn "_"
  let some at_ := parts.findIdx? (· == "ieee754") | return {}
  let before := parts.take at_
  let hasMode := (before.getLast?.bind Mode.ofName).isSome
  -- A step of what an instruction does, and not what it does.
  if before.getLast? == some "rni" then return {}
  let comparing := ["forder", "forders", "fgt", "fge", "feq"].contains (before.headD "")
  if comparing then
    let widths := (parts.drop (at_ + 2)).filterMap String.toNat?
    let some format := widths.head?.bind formatOf | return {}
    -- `forders` is a comparison that signals, as x86's `COMISD`, `MINSD` and the predicates of `CMPSD` that say so are: of any NaN,
    -- quiet or not, rather than of one that signals.
    let signaling := inputs.any fun input =>
      if before.headD "" == "forders" then isNaN format input
      else if rules.legacyMips then isNaN format input && !isSignaling format input else isSignaling format input
    return { invalid := signaling, denormal := inputs.any (isDenormal format) && !inputs.any (isNaN format) }
  if !hasMode then return {}
  let operation := "_".intercalate before.dropLast
  let widths := (parts.drop (at_ + 2)).filterMap String.toNat?
  let some first := widths.head? | return {}
  let last := widths.getLast?.getD first
  let some source := formatOf first | return {}
  let rounded := if !known then true else false
  let differs : Bool :=
    match evaluateWith rules (withMode name "rtp") inputs, evaluateWith rules (withMode name "rtn") inputs with
    | some up, some down =>
      -- Exactly nothing has the sign of the mode.
      let zero (bits : Nat) := match formatOf last with
        | some target => (match unpack target bits with | .zero _ => true | _ => false)
        | none => false
      up.2 != down.2 && !(zero up.2 && zero down.2)
    | _, _ => false
  match operation with
  | "cast_sfloat" | "cast_float" => return { inexact := rounded && differs }
  | "cast_sint" | "cast_int" =>
    -- Of the integer that it rounds to in its mode, as x86 and RISC-V have it: out of range is invalid, whatever is given for it, and
    -- otherwise what isn't an integer is inexact, also of what saturates.
    let signed := operation == "cast_sint"
    let some input := inputs.head? | return {}
    let mode := (before.getLast?.bind Mode.ofName).getD .rtz
    match unpack source input with
    | .nan _ | .infinity _ => return { invalid := true }
    | .zero _ => return {}
    | .finite negative m e =>
      let (integer, notExact) := roundToInteger negative m e mode
      let invalid := if negative && integer != 0 then !signed || integer > 2 ^ (last - 1)
        else integer ≥ (if signed then 2 ^ (last - 1) else 2 ^ last)
      return { invalid, inexact := !invalid && rounded && notExact }
  | "fround" | "froundq" =>
    -- To an integer of the format: a signaling NaN is invalid, and what wasn't an integer inexact, but of `froundq`, which says
    -- nothing of that, as ROUNDSD of its bit 3.
    let some input := inputs.head? | return {}
    let signaling := if rules.legacyMips then isNaN source input && !isSignaling source input else isSignaling source input
    if isNaN source input then return { invalid := signaling }
    -- Of a denormal, only x87's FRNDINT, of 80 bits, says so: ROUNDSD doesn't.
    return { inexact := operation == "fround" && rounded && result != input, denormal := source.explicit && isDenormal source input }
  | "fadd" | "fsub" | "fmul" | "fdiv" | "fsqrt" | "fmad" | "fmadh" | "fconvert" =>
    let target := if operation == "fconvert" then (formatOf last).getD source else source
    -- The quiet bit of the NaNs of legacy MIPS says the opposite.
    let signaling := inputs.any fun input =>
      if rules.legacyMips then isNaN source input && !isSignaling source input else isSignaling source input
    let anyNaN := inputs.any (isNaN source)
    let denormal := inputs.any (isDenormal source)
    let resultNaN := isNaN target result
    -- Of what is raised, these leave no denormal to say.
    let infinityTimesZero := operation == "fmad" && rules.infinityZeroInvalid && (match inputs with
      | x :: y :: _ =>
        let infinite (bits : Nat) : Bool := match unpack source bits with | .infinity _ => true | _ => false
        let zero (bits : Nat) : Bool := match unpack source bits with | .zero _ => true | _ => false
        (infinite x && zero y) || (zero x && infinite y)
      | _ => false)
    if anyNaN || resultNaN then return { invalid := signaling || !anyNaN || infinityTimesZero }
    let infiniteInput := inputs.any fun input => match unpack source input with | .infinity _ => true | _ => false
    let divideByZero := operation == "fdiv" && !infiniteInput && (match inputs with
      | [numerator, denominator] =>
        (match unpack source denominator with | .zero _ => true | _ => false) &&
          (match unpack source numerator with | .zero _ => false | _ => true)
      | _ => false)
    if divideByZero then return { divideByZero }
    if infiniteInput then return { denormal }
    -- What is at an end of the format has to be told from what fits there, whatever is known.
    let field := (result >>> target.fieldBits) % 2 ^ target.exponentBits
    -- What rounds up to the smallest normal number may be tiny too.
    let edge := field ≤ 1 || field ≥ target.maxExponent - 1
    if known && !edge then return { denormal }
    -- Overflow is of the result in its mode with no end to its exponents, and underflow is of what is tiny and not exact: tiny after
    -- rounding as that, or before, which rounding toward zero says, as it is past no power of two that it isn't past.
    let mode := (before.getLast?.bind Mode.ofName).getD .rne
    let overflow := (unboundedResult operation source target mode inputs).any (beyond target)
    let tinyResult := unboundedResult operation source target (if rules.tininessBefore then .rtz else mode) inputs
    let inexact := differs || overflow
    return { inexact, overflow, underflow := inexact && tinyResult.any (tiny target), denormal }
  | _ => return {}

/-- Of PowerPC, which invalid operation an intrinsic was, as the bits of FPSCR that say so, numbered from the least significant one:
VXSNAN 24 of a signaling NaN, VXISI 23 of ∞ - ∞, VXIDI 22 of ∞ / ∞, VXZDZ 21 of 0 / 0, VXIMZ 20 of ∞ × 0, VXVC 19 of an ordered
comparison of a NaN, VXSQRT 9 of the root of what is negative, and VXCVI 8 of a conversion to an integer that can't be. -/
def powerpcInvalid (name : String) (inputs : List Nat) : Nat := Id.run do
  let parts := name.splitOn "_"
  let some at_ := parts.findIdx? (· == "ieee754") | return 0
  let operation := parts.headD ""
  let some width := ((parts.drop (at_ + 2)).filterMap String.toNat?).head? | return 0
  let some format := formatOf width | return 0
  let kind (bits : Nat) : Number := unpack format bits
  let infinite (bits : Nat) : Bool := match kind bits with | .infinity _ => true | _ => false
  let zero (bits : Nat) : Bool := match kind bits with | .zero _ => true | _ => false
  let negative (bits : Nat) : Bool := (bits >>> (format.width - 1)) % 2 == 1
  let mut bits := if inputs.any (isSignaling format) then 2 ^ 24 else 0
  -- ∞ × 0 of a fused multiply-add is invalid whatever its addend is.
  if let ("fmad", x :: y :: _) := (operation, inputs) then
    if (infinite x && zero y) || (zero x && infinite y) then bits := bits ||| 2 ^ 20
  if inputs.any (isNaN format) then
    if operation == "forders" then bits := bits ||| 2 ^ 19
    if operation == "cast" then bits := bits ||| 2 ^ 8
    return bits
  match operation, inputs with
  | "fadd", [x, y] => if infinite x && infinite y && negative x != negative y then bits := bits ||| 2 ^ 23
  | "fsub", [x, y] => if infinite x && infinite y && negative x == negative y then bits := bits ||| 2 ^ 23
  | "fdiv", [x, y] =>
    if infinite x && infinite y then bits := bits ||| 2 ^ 22
    if zero x && zero y then bits := bits ||| 2 ^ 21
  | "fmul", [x, y] => if (infinite x && zero y) || (zero x && infinite y) then bits := bits ||| 2 ^ 20
  | "fmad", [x, y, z] =>
    if (infinite x && zero y) || (zero x && infinite y) then bits := bits ||| 2 ^ 20
    else if (infinite x || infinite y) && infinite z && (negative x != negative y) != negative z then bits := bits ||| 2 ^ 23
  | "fsqrt", [x] => if negative x && !zero x then bits := bits ||| 2 ^ 9
  | "cast", _ => if raisedBy .powerpc name inputs 0 |>.invalid then bits := bits ||| 2 ^ 8
  | _, _ => pure ()
  pure bits

/-- The class of a result, as FPRF of PowerPC has it: C, FL, FG, FE and FU, from the most significant. -/
def powerpcClass (format : Format) (bits : Nat) : Nat :=
  let negative := (bits >>> (format.width - 1)) % 2 == 1
  match unpack format bits with
  | .nan _ => 0x11
  | .infinity _ => if negative then 0x09 else 0x05
  | .zero _ => if negative then 0x12 else 0x02
  | .finite _ _ _ =>
    if isDenormal format bits then (if negative then 0x18 else 0x14) else (if negative then 0x08 else 0x04)

/-- Whether an operation that isn't exact gave what is further from zero than it is, as FR of PowerPC says. -/
def roundedUp (rules : NaNRules) (name : String) (inputs : List Nat) (result : Nat) : Bool :=
  match evaluateWith rules (withMode name "rtz") inputs with
  | some (_, truncated) => truncated != result
  | none => false

/-- What is in a format rounded to `precision` bits of significand, its exponents as they are, as x87 rounds by its precision control.
Of what was rounded to odd with more bits than that, which keeps whether it was exact, this is rounded once. -/
def narrowPrecision (format : Format) (mode : Mode) (precision : Nat) (bits : Nat) : Nat :=
  match unpack format bits with
  | .finite negative m e =>
    let length := bitLength m
    if length ≤ precision then bits
    else pack format .rne negative (roundBits mode negative m (length - precision) false) (e + (length - precision))
  | _ => bits

/-- Whether `evaluate` knows an operation of this name. -/
def serves (name : String) : Bool :=
  let parts := name.splitOn "_"
  match parts.findIdx? (· == "ieee754") with
  | none => false
  | some at_ =>
    let before := parts.take at_
    let before := if (before.getLast?.bind Mode.ofName).isSome then before.dropLast else before
    ["fadd", "fsub", "fmul", "fdiv", "fsqrt", "fmad", "fmadh", "fround", "froundq", "fconvert", "cast_sint", "cast_int", "cast_sfloat",
      "cast_float",
      "forder", "forders", "fgt", "fge", "feq", "is_nan", "is_inf", "is_fzero"].contains ("_".intercalate before) ||
      specialOperations.contains ("_".intercalate before)

end Bap.Float
