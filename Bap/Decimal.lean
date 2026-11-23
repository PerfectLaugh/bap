/-! # Decimal arithmetic

The decimal floating point of IEEE 754-2008 in the densely packed encoding, as the instructions of PowerPC have it, and the signed
decimals of its vector registers: on the bits of the operands, in integers. A number is unpacked to its sign, its coefficient and its
exponent, an operation works out the exact result, and one function rounds it to a format, by one of the eight rounding modes that
FPSCR has for the decimals. What an operation raises comes with its result, as the bits of FPSCR that it sets.

`serve` is what the semantics of PowerPC name `powerpc-d…` and `powerpc-bcd…`. -/

namespace Bap.Decimal

/-! ## The encoding -/

/-- A format: the digits of its coefficient, and the bits of the continuation of its exponent. -/
structure Format where
  width : Nat
  exponentBits : Nat
  deriving DecidableEq

def decimal32 : Format := ⟨32, 6⟩
def decimal64 : Format := ⟨64, 8⟩
def decimal128 : Format := ⟨128, 12⟩

namespace Format

/-- The bits of the continuation of the coefficient, which are declets of three digits each. -/
def coefficientBits (format : Format) : Nat := format.width - 6 - format.exponentBits
def digits (format : Format) : Nat := format.coefficientBits / 10 * 3 + 1
/-- The greatest exponent of a coefficient that is an integer, as it is encoded, and what is taken from an encoded one. -/
def maxBiased (format : Format) : Nat := 3 * 2 ^ format.exponentBits - 1
def bias (format : Format) : Nat := (format.maxBiased + 1) / 2 + format.digits - 2
def maxExponent (format : Format) : Int := (format.maxBiased : Int) - format.bias
def minExponent (format : Format) : Int := -(format.bias : Int)

end Format

inductive Kind where
  | finite | infinity | quiet | signaling
  deriving DecidableEq

/-- A number: of a finite one, the coefficient times ten to the exponent; of a NaN, the coefficient is its payload. -/
structure Number where
  negative : Bool := false
  kind : Kind := .finite
  coefficient : Nat := 0
  exponent : Int := 0

namespace Number
def isNaN (number : Number) : Bool := number.kind == .quiet || number.kind == .signaling
def isSpecial (number : Number) : Bool := number.kind != .finite
def isZero (number : Number) : Bool := number.kind == .finite && number.coefficient == 0
def isInfinite (number : Number) : Bool := number.kind == .infinity
end Number

/-- The digits of a number, of which zero has one. -/
def digitsOf (value : Nat) : Nat := if value == 0 then 1 else (Nat.toDigits 10 value).length

/-- Three digits of a declet of the densely packed encoding. -/
def declet (bits : Nat) : Nat :=
  let bit (index : Nat) : Nat := (bits >>> index) % 2
  let (p, q, r, s, t, u, v, w, x, y) := (bit 9, bit 8, bit 7, bit 6, bit 5, bit 4, bit 3, bit 2, bit 1, bit 0)
  let (high, middle, low) :=
    if v == 0 then (4 * p + 2 * q + r, 4 * s + 2 * t + u, 4 * w + 2 * x + y)
    else match w, x with
      | 0, 0 => (4 * p + 2 * q + r, 4 * s + 2 * t + u, 8 + y)
      | 0, _ => (4 * p + 2 * q + r, 8 + u, 4 * s + 2 * t + y)
      | _, 0 => (8 + r, 4 * s + 2 * t + u, 4 * p + 2 * q + y)
      | _, _ => match s, t with
        | 0, 0 => (8 + r, 8 + u, 4 * p + 2 * q + y)
        | 0, _ => (8 + r, 4 * p + 2 * q + u, 8 + y)
        | _, 0 => (4 * p + 2 * q + r, 8 + u, 8 + y)
        | _, _ => (8 + r, 8 + u, 8 + y)
  100 * high + 10 * middle + low

/-- The declet of three digits: the canonical one, which is the least of those that are them. -/
def decletOf : Nat → Nat :=
  let table : Array Nat := (List.range 1024).foldr (fun bits table => table.set! (declet bits) bits) (Array.replicate 1000 0)
  fun value => table[value % 1000]!

private def decletsValue (count bits : Nat) : Nat :=
  (List.range count).foldl (fun value index => value * 1000 + declet ((bits >>> (10 * (count - 1 - index))) % 1024)) 0

private def decletsOf (count value : Nat) : Nat :=
  (List.range count).foldl (fun bits index => bits ||| (decletOf (value / 1000 ^ index % 1000) <<< (10 * index))) 0

def decode (format : Format) (bits : Nat) : Number :=
  let negative := (bits >>> (format.width - 1)) % 2 == 1
  let combination := (bits >>> (format.width - 6)) % 32
  let continuation := (bits >>> format.coefficientBits) % 2 ^ format.exponentBits
  let rest := decletsValue (format.coefficientBits / 10) (bits % 2 ^ format.coefficientBits)
  if combination == 30 then { negative, kind := .infinity }
  else if combination == 31 then
    { negative, kind := if continuation >>> (format.exponentBits - 1) == 1 then .signaling else .quiet, coefficient := rest }
  else
    let (high, lead) := if combination >>> 3 == 3 then ((combination >>> 1) % 4, 8 + combination % 2) else (combination >>> 3, combination % 8)
    { negative, coefficient := lead * 10 ^ (format.digits - 1) + rest
      exponent := ((high <<< format.exponentBits) + continuation : Nat) - (format.bias : Int) }

/-- The bits of a number, whose coefficient and exponent are those of the format. -/
def encode (format : Format) (number : Number) : Nat :=
  let sign := if number.negative then 2 ^ (format.width - 1) else 0
  let field (combination continuation rest : Nat) : Nat :=
    sign + (combination <<< (format.width - 6)) + (continuation <<< format.coefficientBits) + rest
  let count := format.coefficientBits / 10
  match number.kind with
  | .infinity => field 30 0 0
  | .quiet => field 31 0 (decletsOf count (number.coefficient % 10 ^ (format.digits - 1)))
  | .signaling => field 31 (2 ^ (format.exponentBits - 1)) (decletsOf count (number.coefficient % 10 ^ (format.digits - 1)))
  | .finite =>
    let biased := (number.exponent + format.bias).toNat
    let lead := number.coefficient / 10 ^ (format.digits - 1) % 10
    let high := biased >>> format.exponentBits
    let combination := if lead ≥ 8 then 24 + 2 * high + (lead - 8) else 8 * high + lead
    field combination (biased % 2 ^ format.exponentBits) (decletsOf count (number.coefficient % 10 ^ (format.digits - 1)))

/-! ## Rounding -/

/-- The rounding modes, as DRN of FPSCR numbers them: to the nearest with ties to even, toward zero, up, down, to the nearest with ties
away from zero, to the nearest with ties toward zero, away from zero, and to prepare for a shorter precision. -/
inductive Mode where
  | halfEven | down | ceiling | floor | halfUp | halfDown | up | prepare
  deriving DecidableEq

def Mode.ofField (value : Nat) : Mode :=
  match value % 8 with
  | 0 => .halfEven | 1 => .down | 2 => .ceiling | 3 => .floor | 4 => .halfUp | 5 => .halfDown | 6 => .up | _ => .prepare

/-- What an operation raises, and what it says of its result. -/
structure Flags where
  inexact : Bool := false
  roundedUp : Bool := false
  overflow : Bool := false
  underflow : Bool := false
  /-- The bits of FPSCR of what is invalid, and of a division by zero. -/
  status : Nat := 0

/-- A coefficient without its `drop` low digits, rounded: what is kept, whether anything was dropped, and whether it was rounded up. -/
def roundDigits (mode : Mode) (negative : Bool) (coefficient drop : Nat) : Nat × Bool × Bool :=
  if drop == 0 then (coefficient, false, false) else
  let unit := 10 ^ drop
  let (kept, rest) := (coefficient / unit, coefficient % unit)
  let half := unit / 2
  let up := rest != 0 && match mode with
    | .halfEven => rest > half || (rest == half && kept % 2 == 1)
    | .halfUp => rest ≥ half
    | .halfDown => rest > half
    | .down => false
    | .up => true
    | .ceiling => !negative
    | .floor => negative
    | .prepare => kept % 10 == 0 || kept % 10 == 5
  (if up then kept + 1 else kept, rest != 0, up)

/-- A number of a sign, a coefficient of any length and an exponent, in a format: rounded once to its precision, or to fewer digits
where it is below the least normal number, with its coefficient padded where its exponent is past the greatest. -/
def finish (format : Format) (mode : Mode) (negative : Bool) (coefficient : Nat) (exponent : Int) : Number × Flags :=
  let precision := format.digits
  let (least, greatest) := (format.minExponent, format.maxExponent)
  if coefficient == 0 then ({ negative, exponent := max least (min exponent greatest) }, {}) else
  let length := digitsOf coefficient
  let drop := max (max ((length : Int) - precision) (least - exponent)) 0
  let (kept, inexact, up) := roundDigits mode negative coefficient drop.toNat
  let exponent := exponent + drop
  let (kept, exponent) := if digitsOf kept > precision then (kept / 10, exponent + 1) else (kept, exponent)
  if kept == 0 then ({ negative, exponent }, { inexact, roundedUp := up, underflow := inexact }) else
  if exponent + digitsOf kept - 1 > greatest + precision - 1 then
    let toInfinity := match mode with
      | .halfEven | .halfUp | .halfDown | .up => true
      | .down | .prepare => false
      | .ceiling => !negative
      | .floor => negative
    (if toInfinity then { negative, kind := .infinity }
     else { negative, coefficient := 10 ^ precision - 1, exponent := greatest },
     { inexact := true, roundedUp := toInfinity, overflow := true })
  else
    let subnormal := kept < 10 ^ (precision - 1) && exponent == least
    let (kept, exponent) := if exponent > greatest then (kept * 10 ^ (exponent - greatest).toNat, greatest) else (kept, exponent)
    ({ negative, coefficient := kept, exponent }, { inexact, roundedUp := up, underflow := inexact && subnormal })

/-! ## FPSCR -/

def fx : Nat := 1 <<< 31
def vx : Nat := 1 <<< 29
def ox : Nat := 1 <<< 28
def ux : Nat := 1 <<< 27
def zx : Nat := 1 <<< 26
def xx : Nat := 1 <<< 25
def vxsnan : Nat := 1 <<< 24
def vxisi : Nat := 1 <<< 23
def vxidi : Nat := 1 <<< 22
def vxzdz : Nat := 1 <<< 21
def vximz : Nat := 1 <<< 20
def vxvc : Nat := 1 <<< 19
def fr : Nat := 1 <<< 18
def fi : Nat := 1 <<< 17
def vxcvi : Nat := 1 <<< 8

/-- The class of a result, as FPRF has it: C and the four bits of FPCC. -/
def classOf (format : Format) (number : Number) : Nat :=
  match number.kind with
  | .signaling => 0x01
  | .quiet => 0x11
  | .infinity => if number.negative then 0x09 else 0x05
  | .finite =>
    if number.coefficient == 0 then (if number.negative then 0x12 else 0x02)
    else
      let subnormal : Bool := number.exponent + digitsOf number.coefficient - 1 < format.minExponent + format.digits - 1
      if number.negative then (if subnormal then 0x18 else 0x08) else (if subnormal then 0x14 else 0x04)

/-- What an intrinsic gives the semantics: the bits of its result in the low 128, and above them the bits of FPSCR that it sets, at
their places, with whether FPRF, FR and FI, or FPCC alone, are those of this result. -/
def packed (value status : Nat) (fprf : Option Nat := none) (rounding : Option (Bool × Bool) := none) (fpcc : Option Nat := none) :
    Nat × Nat :=
  let status := status ||| (match fprf with | some c => c <<< 12 | none => 0) ||| (match fpcc with | some c => c <<< 12 | none => 0) |||
    (match rounding with | some (inexact, up) => (if inexact then fi else 0) ||| (if up then fr else 0) | none => 0)
  (192, value % 2 ^ 128 + (status <<< 128) + (if fprf.isSome then 2 ^ 160 else 0) + (if rounding.isSome then 2 ^ 161 else 0) +
    (if fpcc.isSome then 2 ^ 162 else 0))

private def statusOf (flags : Flags) : Nat :=
  flags.status ||| (if flags.inexact then xx else 0) ||| (if flags.overflow then ox else 0) ||| (if flags.underflow then ux else 0)

/-- A result of arithmetic in a format, with all that it says. -/
private def arithmetic (format : Format) (result : Number × Flags) : Nat × Nat :=
  packed (encode format result.1) (statusOf result.2) (some (classOf format result.1)) (some (result.2.inexact, result.2.roundedUp))

/-! ## Arithmetic -/

private def defaultNaN : Number := { kind := .quiet }

/-- The NaN of an operation of two operands, if either is one: a signaling one first, quiet, with its sign and its payload. -/
private def nanOf (a b : Number) : Option (Number × Flags) :=
  let signals := a.kind == .signaling || b.kind == .signaling
  let chosen := if a.kind == .signaling then some a else if b.kind == .signaling then some b else if a.isNaN then some a
    else if b.isNaN then some b else none
  chosen.map fun nan => ({ nan with kind := .quiet }, { status := if signals then vxsnan else 0 })

private def invalid (status : Nat) : Number × Flags := (defaultNaN, { status })

private def signedValue (number : Number) (exponent : Int) : Int :=
  let magnitude : Int := (number.coefficient * 10 ^ (number.exponent - exponent).toNat : Nat)
  if number.negative then -magnitude else magnitude

def add (format : Format) (mode : Mode) (a b : Number) : Number × Flags :=
  if let some nan := nanOf a b then nan else
  match a.kind, b.kind with
  | .infinity, .infinity => if a.negative == b.negative then (a, {}) else invalid vxisi
  | .infinity, _ => (a, {})
  | _, .infinity => (b, {})
  | _, _ =>
    let exponent := min a.exponent b.exponent
    -- Where one is beyond what the other can change of it, a digit below all of it stands for the other: the sum is of numbers that
    -- are no more than twice the precision apart.
    let reach : Int := 2 * format.digits + 4
    let far (big small : Number) : Bool :=
      big.coefficient != 0 && small.coefficient != 0 &&
        big.exponent - small.exponent - digitsOf small.coefficient > reach
    let sum : Int × Int :=
      if far a b then
        let base := a.exponent - reach
        (signedValue a base + (if b.negative then -1 else 1), base)
      else if far b a then
        let base := b.exponent - reach
        (signedValue b base + (if a.negative then -1 else 1), base)
      else (signedValue a exponent + signedValue b exponent, exponent)
    if sum.1 == 0 then
      let negative := if a.negative == b.negative then a.negative else mode == .floor
      finish format mode negative 0 exponent
    else finish format mode (sum.1 < 0) sum.1.natAbs sum.2

def sub (format : Format) (mode : Mode) (a b : Number) : Number × Flags :=
  if a.isNaN || b.isNaN then add format mode a b else add format mode a { b with negative := !b.negative }

def mul (format : Format) (mode : Mode) (a b : Number) : Number × Flags :=
  if let some nan := nanOf a b then nan else
  let negative := a.negative != b.negative
  match a.kind, b.kind with
  | .infinity, _ => if b.isZero then invalid vximz else ({ negative, kind := .infinity }, {})
  | _, .infinity => if a.isZero then invalid vximz else ({ negative, kind := .infinity }, {})
  | _, _ => finish format mode negative (a.coefficient * b.coefficient) (a.exponent + b.exponent)

def div (format : Format) (mode : Mode) (a b : Number) : Number × Flags :=
  if let some nan := nanOf a b then nan else
  let negative := a.negative != b.negative
  match a.kind, b.kind with
  | .infinity, .infinity => invalid vxidi
  | .infinity, _ => ({ negative, kind := .infinity }, {})
  | _, .infinity => ({ negative, exponent := format.minExponent }, {})
  | _, _ =>
    if b.coefficient == 0 then
      if a.coefficient == 0 then invalid vxzdz else ({ negative, kind := .infinity }, { status := zx })
    else if a.coefficient == 0 then finish format mode negative 0 (a.exponent - b.exponent)
    else
      let ideal := a.exponent - b.exponent
      let scale := format.digits + digitsOf b.coefficient + 2
      let scaled := a.coefficient * 10 ^ scale
      let (quotient, rest) := (scaled / b.coefficient, scaled % b.coefficient)
      if rest == 0 then
        -- An exact quotient has the exponent nearest the ideal one that it can.
        let rec strip : Nat → Nat → Int → Nat × Int
          | 0, quotient, exponent => (quotient, exponent)
          | fuel + 1, quotient, exponent =>
            if exponent < ideal && quotient % 10 == 0 then strip fuel (quotient / 10) (exponent + 1) else (quotient, exponent)
        let (quotient, exponent) := strip scale quotient (ideal - scale)
        finish format mode negative quotient exponent
      else finish format mode negative (quotient * 10 + 1) (ideal - scale - 1)

/-- The order of two numbers that aren't NaNs: less, greater or equal, as a field of the condition register. -/
def compare (a b : Number) : Nat :=
  let value (number : Number) (exponent : Int) : Int := signedValue number exponent
  let order : Int :=
    match a.kind, b.kind with
    | .infinity, .infinity => (if a.negative then -1 else 1) - (if b.negative then -1 else 1)
    | .infinity, _ => if a.negative then -1 else 1
    | _, .infinity => if b.negative then 1 else -1
    | _, _ =>
      if a.coefficient == 0 || b.coefficient == 0 then
        (if a.coefficient == 0 then 0 else if a.negative then -1 else 1) - (if b.coefficient == 0 then 0 else if b.negative then -1 else 1)
      else if a.negative != b.negative then (if a.negative then -1 else 1)
      else
        -- By their magnitudes, which their lengths tell apart when their exponents are far.
        let (top, other) := (a.exponent + digitsOf a.coefficient, b.exponent + digitsOf b.coefficient)
        let magnitude : Int := if top != other then (if top < other then -1 else 1) else
          let exponent := min a.exponent b.exponent
          (value { a with negative := false } exponent) - (value { b with negative := false } exponent)
        if a.negative then -magnitude else magnitude
  if order < 0 then 8 else if order > 0 then 4 else 2

/-- A number at an exponent, if its coefficient fits there: `decNumberQuantize`. -/
def quantize (format : Format) (mode : Mode) (number : Number) (exponent : Int) : Option (Number × Flags) :=
  if exponent ≥ number.exponent then
    let (kept, inexact, up) := roundDigits mode number.negative number.coefficient (exponent - number.exponent).toNat
    if digitsOf kept > format.digits then none
    else some ({ number with coefficient := kept, exponent }, { inexact, roundedUp := up })
  else
    let padded := number.coefficient * 10 ^ (number.exponent - exponent).toNat
    if number.coefficient != 0 && digitsOf padded > format.digits then none
    else some ({ number with coefficient := padded, exponent }, {})

/-- The rounding mode of a quantization, by RMC: to the nearest even, toward zero, to the nearest away, or as FPSCR says. -/
private def quantizeMode (current : Mode) (rmc : Nat) : Mode :=
  match rmc % 4 with
  | 0 => .halfEven | 1 => .down | 2 => .halfUp | _ => current

/-- That of a rounding to an integer, by R and RMC. -/
private def integerMode (current : Mode) (r rmc : Nat) : Mode :=
  if r % 2 == 0 then quantizeMode current rmc
  else match rmc % 4 with
    | 0 => .ceiling | 1 => .floor | 2 => .up | _ => .halfDown

/-- `dqua` and `dquai`: `b` at the exponent of `a`. Of the NaNs, a signaling one of `a` is first. -/
private def quantizeTo (format : Format) (mode : Mode) (a b : Number) : Number × Flags :=
  if let some nan := nanOf a b then nan else
  match a.kind, b.kind with
  | .infinity, .infinity => (b, {})
  | .infinity, _ | _, .infinity => invalid vxcvi
  | _, _ =>
    match quantize format mode b a.exponent with
    | some result => result
    | none => invalid vxcvi

/-- `drrnd`: `b` with no more than `significance` digits. -/
private def reround (format : Format) (mode : Mode) (significance : Nat) (b : Number) : Number × Flags :=
  let length := digitsOf b.coefficient
  if b.isSpecial || significance == 0 || length ≤ significance then
    if b.kind == .signaling then ({ b with kind := .quiet }, { status := vxsnan }) else (b, {})
  else
    let exponent := b.exponent + length - significance
    if exponent > format.maxExponent then invalid vxcvi else
    let (kept, inexact, up) := roundDigits mode b.negative b.coefficient (length - significance)
    let (kept, exponent) := if digitsOf kept > significance then (kept / 10, exponent + 1) else (kept, exponent)
    if exponent > format.maxExponent then invalid vxcvi
    else ({ b with coefficient := kept, exponent }, { inexact, roundedUp := up })

/-- `drintx` and `drintn`: `b` as an integer, of which the latter doesn't say that it isn't exact. -/
private def toIntegral (format : Format) (mode : Mode) (b : Number) (exact : Bool) : Number × Flags :=
  match b.kind with
  | .signaling => ({ b with kind := .quiet }, { status := vxsnan })
  | .quiet | .infinity => (b, {})
  | .finite =>
    if b.exponent ≥ 0 then (b, {}) else
    match quantize format mode b 0 with
    | some (number, flags) => (number, if exact then flags else {})
    | none => (b, {})

/-- A number of a wider format in a narrower one, or of a narrower in a wider. -/
private def convert (target : Format) (mode : Mode) (number : Number) : Number × Flags :=
  match number.kind with
  | .finite => finish target mode number.negative number.coefficient number.exponent
  | .infinity => (number, {})
  | _ => ({ number with coefficient := if digitsOf number.coefficient < target.digits then number.coefficient else 0 }, {})

private def signedOf (width bits : Nat) : Int := if bits ≥ 2 ^ (width - 1) then (bits : Int) - 2 ^ width else bits

/-- An integer of a width as a number of a format. -/
private def ofInteger (format : Format) (mode : Mode) (width bits : Nat) : Number × Flags :=
  let value := signedOf width bits
  finish format mode (value < 0) value.natAbs 0

/-- A number as an integer of a width, rounded as FPSCR says: what doesn't fit is the greatest or the least, and a NaN the least. -/
private def toInteger (format : Format) (mode : Mode) (width : Nat) (b : Number) : Nat × Flags :=
  let least : Nat := 2 ^ (width - 1)
  let greatest : Nat := 2 ^ (width - 1) - 1
  match b.kind with
  | .infinity => (if b.negative then least else greatest, { status := vxcvi })
  | .quiet => (least, { status := vxcvi })
  | .signaling => (least, { status := vxcvi ||| vxsnan })
  | .finite =>
    if b.coefficient == 0 then (0, {}) else
    -- What has more digits than an integer of the width can is past it whatever it rounds to.
    if b.exponent + digitsOf b.coefficient > 40 then (if b.negative then least else greatest, { status := vxcvi }) else
    let (magnitude, flags) : Nat × Flags :=
      if b.exponent ≥ 0 then (b.coefficient * 10 ^ b.exponent.toNat, {})
      else
        let (kept, inexact, up) := roundDigits mode b.negative b.coefficient (-b.exponent).toNat
        (kept, { inexact, roundedUp := up })
    let _ := format
    if (b.negative && magnitude > least) || (!b.negative && magnitude > greatest) then
      (if b.negative then least else greatest, { status := vxcvi })
    else ((if b.negative then 2 ^ width - magnitude else magnitude) % 2 ^ width, flags)

/-! ## The intrinsics of the decimal floating point -/

/-- The format of an instruction by its name: of a quad if it ends in `q`. -/
private def formatOf (quad : Bool) : Format := if quad then decimal128 else decimal64

/-- The nibbles of the coefficient of a number, from the least. -/
private def nibblesOf (value count : Nat) : Nat :=
  (List.range count).foldl (fun bits index => bits ||| ((value / 10 ^ index % 10) <<< (4 * index))) 0

private def serveDecimal (operation : String) (quad : Bool) (inputs : List Nat) : Option (Nat × Nat) :=
  let format := formatOf quad
  let width := format.width
  let number := decode format
  let two (apply : Mode → Number → Number → Number × Flags) : Option (Nat × Nat) :=
    match inputs with
    | [rounding, a, b] => some (arithmetic format (apply (Mode.ofField rounding) (number a) (number b)))
    | _ => none
  -- A comparison or a test: its field, which FPCC has too.
  let field (value status : Nat) : Option (Nat × Nat) := some (packed value status (fpcc := some value))
  match operation, inputs with
  | "dadd", _ => two (add format)
  | "dsub", _ => two (sub format)
  | "dmul", _ => two (mul format)
  | "ddiv", _ => two (div format)
  | "dqua", [rounding, a, b, rmc] =>
    some (arithmetic format (quantizeTo format (quantizeMode (Mode.ofField rounding) rmc) (number a) (number b)))
  | "dquai", [rounding, exponent, b, rmc] =>
    let exponent : Int := signedOf 5 (exponent % 32)
    some (arithmetic format (quantizeTo format (quantizeMode (Mode.ofField rounding) rmc) { coefficient := 1, exponent } (number b)))
  | "drrnd", [rounding, a, b, rmc] =>
    some (arithmetic format (reround format (quantizeMode (Mode.ofField rounding) rmc) (a % 64) (number b)))
  | "drintx", [rounding, r, b, rmc] =>
    some (arithmetic format (toIntegral format (integerMode (Mode.ofField rounding) r rmc) (number b) true))
  | "drintn", [rounding, r, b, rmc] =>
    let (result, flags) := toIntegral format (integerMode (Mode.ofField rounding) r rmc) (number b) false
    some (packed (encode format result) (statusOf flags) (some (classOf format result)) (some (false, flags.roundedUp)))
  | "dcmpu", [_, a, b] | "dcmpo", [_, a, b] =>
    let (a, b) := (number a, number b)
    if a.isNaN || b.isNaN then
      let signals := a.kind == .signaling || b.kind == .signaling
      field 1 (if operation == "dcmpu" then (if signals then vxsnan else 0) else if signals then vxsnan ||| vxvc else vxvc)
    else field (compare a b) 0
  | "dtstex", [_, a, b] =>
    let (a, b) := (number a, number b)
    let kind (number : Number) : Nat := if number.isNaN then 4 else if number.isInfinite then 2 else 1
    if a.isSpecial || b.isSpecial then field (if kind a != kind b then 1 else 2) 0
    else field (if a.exponent < b.exponent then 8 else if a.exponent > b.exponent then 4 else 2) 0
  | "dtstsf", [_, significance, b] =>
    let b := number b
    let significance := significance % 64
    if b.isSpecial then field 1 0
    else if significance == 0 || b.coefficient == 0 then field 4 0
    else
      let length := digitsOf b.coefficient
      field (if significance < length then 8 else if significance > length then 4 else 2) 0
  | "dtstdc", [_, a, mask] =>
    let a := number a
    let subnormal := classOf format a % 16 != 2 && classOf format a ≥ 16 && a.kind == .finite
    let normal := a.kind == .finite && a.coefficient != 0 && !subnormal
    let hit := (mask.testBit 5 && a.isZero) || (mask.testBit 4 && subnormal) || (mask.testBit 3 && normal) ||
      (mask.testBit 2 && a.isInfinite) || (mask.testBit 1 && a.kind == .quiet) || (mask.testBit 0 && a.kind == .signaling)
    field ((if a.negative then 8 else 0) + (if hit then 2 else 0)) 0
  | "dtstdg", [_, a, mask] =>
    let a := number a
    let finite := a.kind == .finite
    let extreme := finite && (a.exponent == format.maxExponent || a.exponent == format.minExponent)
    let subnormal := finite && a.coefficient != 0 && classOf format a ≥ 16
    let normal := finite && a.coefficient != 0 && !subnormal
    let leading := digitsOf a.coefficient == format.digits
    let hit := (mask.testBit 5 && a.isZero && !extreme) || (mask.testBit 4 && a.isZero && extreme) ||
      (mask.testBit 3 && (subnormal || (normal && extreme))) || (mask.testBit 2 && normal && !extreme && !leading) ||
      (mask.testBit 1 && normal && !extreme && leading) || (mask.testBit 0 && a.isSpecial)
    field ((if a.negative then 8 else 0) + (if hit then 2 else 0)) 0
  | "dxex", [_, b] =>
    let b := number b
    let value : Int := match b.kind with
      | .infinity => -1 | .quiet => -2 | .signaling => -3
      | .finite => b.exponent + format.bias
    some (packed (value % 2 ^ 64).toNat 0)
  | "diex", [_, exponent, bits] =>
    let exponent := signedOf 64 (exponent % 2 ^ 64)
    if exponent < 0 || exponent > format.maxBiased then
      -- An infinity or a NaN, with the sign and the continuation of the coefficient as they are.
      let special := if exponent == -1 then 30 * 2 ^ format.exponentBits else if exponent == -3 then 31 * 2 ^ format.exponentBits + 2 ^ (format.exponentBits - 1)
        else 31 * 2 ^ format.exponentBits
      let kept := bits % 2 ^ format.coefficientBits + (bits >>> (width - 1)) * 2 ^ (width - 1)
      some (packed (kept + (special <<< format.coefficientBits)) 0)
    else
      let b := number bits
      let (result, _) := finish format .halfEven b.negative b.coefficient (exponent - format.bias)
      some (packed (encode format result) 0)
  | "dscli", [_, a, shift] | "dscri", [_, a, shift] =>
    let shift := shift % 64
    if shift > format.digits then
      -- Nothing of the coefficient, with the sign and the exponent as they are: the digit that the combination has is cleared.
      let top := a >>> format.coefficientBits
      let combination := (top >>> format.exponentBits) % 32
      let cleared := if combination ≥ 30 then combination else if combination ≥ 24 then (combination >>> 1) % 4 * 8 else combination / 8 * 8
      some (packed ((((top >>> (format.exponentBits + 5)) * 32 + cleared) * 2 ^ format.exponentBits + top % 2 ^ format.exponentBits) <<<
        format.coefficientBits) 0)
    else
      let value := number a
      let shifted := if operation == "dscli" then value.coefficient * 10 ^ shift % 10 ^ format.digits else value.coefficient / 10 ^ shift
      let shifted := if value.isSpecial then shifted % 10 ^ (format.digits - 1) else shifted
      some (packed (encode format { value with coefficient := shifted }) 0)
  | "ddedpd", [_, sign, b] =>
    let value := number b
    let nibbles := width / 4
    let digits := nibblesOf value.coefficient nibbles
    if sign % 4 ≥ 2 then
      let code := if value.negative then 0xd else if sign % 2 == 1 then 0xf else 0xc
      some (packed ((digits <<< 4) % 2 ^ width + code) 0)
    else some (packed digits 0)
  | "denbcd", [_, sign, bits] =>
    let nibbles := width / 4
    let nibble (index : Nat) : Nat := (bits >>> (4 * index)) % 16
    let signed := sign % 2 == 1
    let code := nibble 0
    let digits := (List.range nibbles).drop (if signed then 1 else 0)
    let valid := digits.all (nibble · ≤ 9) && (!signed || code ≥ 10)
    if !valid then some (packed (encode format defaultNaN) vxcvi)
    else
      let coefficient := digits.foldr (fun index value => value * 10 + nibble index) 0
      let negative := signed && (code == 0xb || code == 0xd)
      let (result, _) := finish format .halfEven negative coefficient 0
      some (packed (encode format result) 0 (some (classOf format result)))
  | _, _ => none

/-- The conversions, each of its own formats. -/
private def serveConversion (name : String) (inputs : List Nat) : Option (Nat × Nat) :=
  let converted (format : Format) (result : Number × Flags) : Option (Nat × Nat) := some (arithmetic format result)
  let integer (result : Nat × Flags) : Option (Nat × Nat) :=
    some (packed result.1 (statusOf result.2) none (if result.2.status == 0 then some (result.2.inexact, result.2.roundedUp) else none))
  match name, inputs with
  | "dctdp", [_, b] =>
    let (result, _) := convert decimal64 .halfEven (decode decimal32 (b % 2 ^ 32))
    some (packed (encode decimal64 result) 0 (some (classOf decimal64 result)))
  | "drsp", [rounding, b] =>
    let (result, flags) := convert decimal32 (Mode.ofField rounding) (decode decimal64 b)
    some (packed (encode decimal32 result) (statusOf flags) (some (classOf decimal32 result)) (some (flags.inexact, flags.roundedUp)))
  | "dctqpq", [_, b] =>
    let source := decode decimal64 b
    let result := if source.kind == .signaling then ({ source with kind := .quiet }, { status := vxsnan }) else (source, ({} : Flags))
    converted decimal128 result
  | "drdpq", [rounding, b] =>
    let source := decode decimal128 b
    let (result, flags) := convert decimal64 (Mode.ofField rounding) source
    -- A signaling NaN is quiet in the result, and says so.
    let (result, flags) := if source.kind == .signaling then ({ result with kind := .quiet }, { flags with status := vxsnan }) else (result, flags)
    -- In the second register of the pair, with zeros in the first.
    some (packed (encode decimal64 result) (statusOf flags) (some (classOf decimal64 result)) (some (flags.inexact, flags.roundedUp)))
  | "dcffix", [rounding, b] => converted decimal64 (ofInteger decimal64 (Mode.ofField rounding) 64 b)
  | "dcffixq", [rounding, b] => converted decimal128 (ofInteger decimal128 (Mode.ofField rounding) 64 b)
  | "dcffixqq", [rounding, b] => converted decimal128 (ofInteger decimal128 (Mode.ofField rounding) 128 b)
  | "dctfix", [rounding, b] => integer (toInteger decimal64 (Mode.ofField rounding) 64 (decode decimal64 b))
  | "dctfixq", [rounding, b] => integer (toInteger decimal128 (Mode.ofField rounding) 64 (decode decimal128 b))
  | "dctfixqq", [rounding, b] => integer (toInteger decimal128 (Mode.ofField rounding) 128 (decode decimal128 b))
  | _, _ => none

/-! ## The signed decimals of the vector registers -/

/-- A field of the condition register: less, greater, equal, and that the result overflowed or an operand wasn't valid. -/
private def crLess : Nat := 8
private def crGreater : Nat := 4
private def crEqual : Nat := 2
private def crOverflow : Nat := 1

private def nibbleAt (value index : Nat) : Nat := (value >>> (4 * index)) % 16

/-- The sign of a signed decimal: 1, -1, or 0 of a code that isn't one. -/
private def signOf (value : Nat) : Int :=
  match value % 16 with
  | 0xa | 0xc | 0xe | 0xf => 1
  | 0xb | 0xd => -1
  | _ => 0

/-- The magnitude of the 31 digits of a signed decimal, if they are digits. -/
private def magnitudeOf (value : Nat) : Option Nat :=
  if (List.range 31).all fun index => nibbleAt value (index + 1) ≤ 9 then
    some ((List.range 31).foldr (fun index total => total * 10 + nibbleAt value (index + 1)) 0)
  else none

private def preferred (sign : Int) (ps : Nat) : Nat := if sign ≥ 0 then (if ps % 2 == 1 then 0xf else 0xc) else 0xd

/-- A signed decimal of a magnitude of 31 digits and a sign code. -/
private def signedDecimal (magnitude code : Nat) : Nat := (nibblesOf (magnitude % 10 ^ 31) 31 <<< 4) + code

/-- The field of a result: equal if its digits are zeros, or its sign. -/
private def zeroOrSign (value : Nat) : Nat :=
  if value >>> 4 == 0 then crEqual else if signOf value == 1 then crGreater else crLess

private def vector (value field : Nat) : Option (Nat × Nat) := some (132, value % 2 ^ 128 + (field <<< 128))

private def allOnes : Nat := 2 ^ 128 - 1

private def serveVector (name : String) (inputs : List Nat) : Option (Nat × Nat) :=
  -- A shift count: the signed byte 7 of a register, from the most significant.
  let count (a : Nat) : Int := signedOf 8 ((a >>> 64) % 256)
  match name, inputs with
  | "bcdadd", [a, b, ps] | "bcdsub", [a, b, ps] =>
    let signA := signOf a
    let signB := if name == "bcdsub" then -(signOf b) else signOf b
    match magnitudeOf a, magnitudeOf b with
    | some x, some y =>
      if signA == 0 || signB == 0 then vector allOnes crOverflow else
      if signA == signB then
        let sum := x + y
        let result := signedDecimal sum (preferred signA ps)
        vector result (zeroOrSign result ||| (if sum ≥ 10 ^ 31 then crOverflow else 0))
      else if x > y then vector (signedDecimal (x - y) (preferred signA ps)) (if signA > 0 then crGreater else crLess)
      else if x < y then vector (signedDecimal (y - x) (preferred signB ps)) (if signB > 0 then crGreater else crLess)
      else vector (signedDecimal 0 (preferred 0 ps)) crEqual
    | _, _ => vector allOnes crOverflow
  | "bcdcfn", [b, ps] =>
    let half (index : Nat) : Nat := (b >>> (16 * index)) % 2 ^ 16
    let sign := half 0
    let digits := (List.range 7).map fun index => half (index + 1)
    let valid := (sign == 0x2b || sign == 0x2d) && digits.all fun digit => 0x30 ≤ digit && digit ≤ 0x39
    let magnitude := digits.foldr (fun digit total => total * 10 + digit % 16) 0
    let result := signedDecimal magnitude (if sign == 0x2b then preferred 1 ps else 0xd)
    if valid then vector result (zeroOrSign result) else vector result crOverflow
  | "bcdctn", [b, _] =>
    match magnitudeOf b with
    | some magnitude =>
      if signOf b == 0 then vector 0 crOverflow else
      let digits := (List.range 7).foldl (fun bits index => bits ||| ((0x30 + magnitude / 10 ^ index % 10) <<< (16 * (index + 1)))) 0
      vector (digits + (if signOf b == -1 then 0x2d else 0x2b)) (zeroOrSign b ||| (if magnitude ≥ 10 ^ 7 then crOverflow else 0))
    | none => vector 0 crOverflow
  | "bcdcfz", [b, ps] =>
    let byte (index : Nat) : Nat := (b >>> (8 * index)) % 256
    let zone := if ps % 2 == 1 then 0xf else 0x3
    let sign := byte 0 >>> 4
    let valid := !(sign < 0xa && ps % 2 == 1) &&
      (List.range 16).all fun index => byte index % 16 ≤ 9 && (index == 0 || byte index >>> 4 == zone)
    let magnitude := (List.range 16).foldr (fun index total => total * 10 + byte index % 16) 0
    let negative := if ps % 2 == 1 then sign == 0xb || sign == 0xd else sign &&& 4 != 0
    let result := signedDecimal magnitude (if negative then 0xd else 0xc)
    if valid then vector result (zeroOrSign result) else vector result crOverflow
  | "bcdctz", [b, ps] =>
    match magnitudeOf b with
    | some magnitude =>
      if signOf b == 0 then vector 0 crOverflow else
      let zone := if ps % 2 == 1 then 0xf0 else 0x30
      let zoned := (List.range 16).foldl (fun bits index => bits ||| ((zone + magnitude / 10 ^ index % 10) <<< (8 * index))) 0
      let code := if ps % 2 == 1 then (if signOf b == 1 then 0xc else 0xd) else (if signOf b == 1 then 0x3 else 0x7)
      vector (zoned % 16 + code * 16 + zoned / 256 * 256) (zeroOrSign b ||| (if magnitude ≥ 10 ^ 16 then crOverflow else 0))
    | none => vector 0 crOverflow
  | "bcdcfsq", [b, ps] =>
    let value := signedOf 128 b
    -- What has more than 31 digits has no result: zeros, with its sign in the field.
    if value.natAbs ≥ 10 ^ 31 then vector 0 ((if value < 0 then crLess else crGreater) ||| crOverflow) else
    let result := signedDecimal value.natAbs (if value < 0 then 0xd else preferred 0 ps)
    vector result (zeroOrSign result)
  | "bcdctsq", [b, _] =>
    match magnitudeOf b with
    | some magnitude =>
      if signOf b == 0 then vector 0 crOverflow
      else vector (if signOf b == -1 then (2 ^ 128 - magnitude) % 2 ^ 128 else magnitude) (zeroOrSign b)
    | none => vector 0 crOverflow
  | "bcdcpsgn", [a, b, _] =>
    if signOf a == 0 || signOf b == 0 || (magnitudeOf a).isNone || (magnitudeOf b).isNone then vector allOnes crOverflow
    else
      let result := a / 16 * 16 + b % 16
      vector result (zeroOrSign result)
  | "bcdsetsgn", [b, ps] =>
    if signOf b == 0 || (magnitudeOf b).isNone then vector allOnes crOverflow
    else
      let result := b / 16 * 16 + preferred (signOf b) ps
      vector result (zeroOrSign result)
  | "bcds", [a, b, ps] | "bcdsr", [a, b, ps] =>
    match magnitudeOf b with
    | some magnitude =>
      if signOf b == 0 then vector allOnes crOverflow else
      let shift := max (-31) (min (count a) 31)
      let (shifted, overflow) : Nat × Bool :=
        if shift ≥ 0 then (magnitude * 10 ^ shift.toNat, magnitude * 10 ^ shift.toNat ≥ 10 ^ 31)
        else
          let unit := 10 ^ (-shift).toNat
          -- A shift to the right that rounds takes the digit that it drops last to the next of what is left.
          (if name == "bcdsr" && magnitude % unit ≥ unit / 2 then magnitude / unit + 1 else magnitude / unit, false)
      let result := signedDecimal shifted (preferred (signOf b) ps)
      vector result (zeroOrSign result ||| (if overflow then crOverflow else 0))
    | none => vector allOnes crOverflow
  | "bcdus", [a, b, _] =>
    if !((List.range 32).all fun index => nibbleAt b index ≤ 9) then vector allOnes crOverflow else
    let shift := count a
    let (result, overflow) : Nat × Bool :=
      if shift ≥ 32 then (0, b != 0) else if shift ≤ -32 then (0, false)
      else if shift ≥ 0 then ((b <<< (4 * shift.toNat)) % 2 ^ 128, b >>> (128 - 4 * shift.toNat) != 0)
      else (b >>> (4 * (-shift).toNat), false)
    vector result ((if result == 0 then crEqual else crGreater) ||| (if overflow then crOverflow else 0))
  | "bcdtrunc", [a, b, ps] =>
    match magnitudeOf b with
    | some magnitude =>
      if signOf b == 0 then vector allOnes crOverflow else
      let length := min ((a >>> 64) % 2 ^ 16) 31
      let result := signedDecimal (magnitude % 10 ^ length) (preferred (signOf b) ps)
      vector result (zeroOrSign result ||| (if magnitude ≥ 10 ^ length then crOverflow else 0))
    | none => vector allOnes crOverflow
  | "bcdutrunc", [a, b, _] =>
    if !((List.range 32).all fun index => nibbleAt b index ≤ 9) then vector allOnes crOverflow else
    let length := min ((a >>> 64) % 2 ^ 16) 32
    let result := b % 2 ^ (4 * length)
    vector result ((if result == 0 then crEqual else crGreater) ||| (if result != b then crOverflow else 0))
  | _, _ => none

/-- What serves an intrinsic of the decimals of PowerPC, by its name without `powerpc-`: of the decimal floating point, with the
rounding mode of FPSCR first of what it is given, of a long format, or of an extended one if its name ends in `q`; or of the vector
registers. -/
def serve (name : String) (inputs : List Nat) : Option (Nat × Nat) :=
  if name.startsWith "bcd" then serveVector name inputs else
  (serveConversion name inputs).orElse fun _ =>
    (serveDecimal name false inputs).orElse fun _ =>
      if name.endsWith "q" then serveDecimal (name.take (name.length - 1)).toString true inputs else none

end Bap.Decimal
