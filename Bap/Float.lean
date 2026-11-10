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
  | "rne" | "rnx" | "rni" => some .rne
  | "rna" | "rmm" => some .rna
  | "rtz" => some .rtz
  | "rtp" | "rup" => some .rtp
  | "rtn" | "rdn" => some .rtn
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
  deriving DecidableEq, Repr

/-- The first NaN operand, made quiet, and a default that is negative. -/
def NaNRules.x86 : NaNRules := { negativeDefault := true }
/-- A signaling NaN first, and a default that is positive: Arm, unless `FPCR.DN` is set. -/
def NaNRules.arm : NaNRules := { signalingFirst := true, tininessBefore := true }
/-- The first NaN operand, and a default that is positive. -/
def NaNRules.powerpc : NaNRules := {}
/-- Always the default, which is positive. -/
def NaNRules.riscv : NaNRules := { canonical := true, saturating := true }
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
  | "forder", [x, y] => test fun format => pure ((compare format x y).any (·.1))
  | "fgt", [x, y] => test fun format => pure ((compare format y x).any (·.1))
  | "fge", [x, y] => test fun format => pure ((compare format x y).any fun order => !order.1)
  | "feq", [x, y] => test fun format => pure ((compare format x y).any (·.2))
  | "is_nan", [x] => test fun format => pure (match unpack format x with | .nan _ => true | _ => false)
  | "is_inf", [x] => test fun format => pure (match unpack format x with | .infinity _ => true | _ => false)
  | "is_fzero", [x] => test fun format => pure (match unpack format x with | .zero _ => true | _ => false)
  | _, _ => none

/-- An intrinsic by its name, by the rules of an architecture for NaNs. The arithmetic is the same. A NaN that an operation makes
out of nothing is the default of x86 there, and this says what it is here. -/
def evaluateWith (rules : NaNRules) (name : String) (inputs : List Nat) : Option (Nat × Nat) := do
  let (width, bits) ← evaluateX86 name inputs
  let parts := name.splitOn "_"
  let widths := (parts.reverse.takeWhile fun part => part.toNat?.isSome).reverse.filterMap String.toNat?
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
    | "forder" | "fgt" | "fge" | "feq" => (first, none)
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

/-- What an operation that gave `result` raises. Whether a result was rounded is whether rounding up and down come to
something else, which takes evaluating it twice, so that `known` says not to when `inexact` won't change anything. -/
def raisedBy (rules : NaNRules) (name : String) (inputs : List Nat) (result : Nat) (known : Bool := false) : Raised := Id.run do
  let parts := name.splitOn "_"
  let some at_ := parts.findIdx? (· == "ieee754") | return {}
  let before := parts.take at_
  let hasMode := (before.getLast?.bind Mode.ofName).isSome
  -- A step of what an instruction does, and not what it does.
  if before.getLast? == some "rni" then return {}
  let comparing := ["forder", "fgt", "fge", "feq"].contains (before.headD "")
  if comparing then
    let widths := (parts.drop (at_ + 2)).filterMap String.toNat?
    let some format := widths.head?.bind formatOf | return {}
    let signaling := inputs.any fun input =>
      if rules.legacyMips then isNaN format input && !isSignaling format input else isSignaling format input
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
    return { inexact := operation == "fround" && rounded && result != input, denormal := isDenormal source input }
  | "fadd" | "fsub" | "fmul" | "fdiv" | "fsqrt" | "fmad" | "fmadh" | "fconvert" =>
    let target := if operation == "fconvert" then (formatOf last).getD source else source
    -- The quiet bit of the NaNs of legacy MIPS says the opposite.
    let signaling := inputs.any fun input =>
      if rules.legacyMips then isNaN source input && !isSignaling source input else isSignaling source input
    let anyNaN := inputs.any (isNaN source)
    let denormal := inputs.any (isDenormal source)
    let resultNaN := isNaN target result
    -- Of what is raised, these leave no denormal to say.
    if anyNaN || resultNaN then return { invalid := signaling || !anyNaN }
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
      "forder", "fgt", "fge", "feq", "is_nan", "is_inf", "is_fzero"].contains ("_".intercalate before)

end Bap.Float
