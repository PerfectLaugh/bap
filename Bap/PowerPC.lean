import Bap.Float
import Bap.Decimal

/-! # What the semantics of PowerPC leave to a machine that is a function of its operands

The intrinsics whose names start with `powerpc-`: each is what an instruction of the ISA 3.1 computes that the Lisp of the semantics has
no theory of, as a function of the values that the semantics give it, to the bits that they take its result as. `serve` is what an
emulator has for its intrinsic server beside the floating point of `Bap.Float`:

- `powerpc-hash`: the hash of `hashst` and `hashchk`;
- `powerpc-xxgenpcv`: the permute controls of `xxgenpcvbm` and those of the other sizes;
- `powerpc-exptefp` and `powerpc-logefp`: the estimates of AltiVec, which are the powers of 2 and the logarithms of base 2 rounded to the
  nearest single, which is within what the ISA asks of them;
- `powerpc-xv…ger…` and `powerpc-pmxv…ger…`: the outer products of the matrix-multiply assist;
- `powerpc-d…` and `powerpc-bcd…`: the decimal floating point and the decimals of the vector registers, which are of `Bap.Decimal`. -/

namespace Bap.PowerPC

/-! ## The hash of a return address -/

private def rotateLeft16 (value count : Nat) : Nat := ((value <<< count) ||| (value >>> (16 - count))) % 2 ^ 16
private def rotateRight16 (value count : Nat) : Nat := rotateLeft16 value (16 - count)
private def rotateRight64 (value count : Nat) : Nat :=
  let count := count % 64
  if count == 0 then value % 2 ^ 64 else ((value >>> count) ||| (value <<< (64 - count))) % 2 ^ 64

/-- `SIMON_LIKE_32_64` of the ISA 3.1B: a word of 32 bits by a key of 64, of a lane, which says how the words of the key are taken: 32
rounds of a Feistel network on halves of 16 bits, with the key schedule of the constant sequence z0. -/
def simonLike (x key lane : Nat) : Nat := Id.run do
  let c := 0xfffc
  let z0 := 0xfa2561cdf44ac398
  let mut k : Array Nat := (List.range 4).toArray.map fun index => (key >>> (16 * (3 - index))) % 2 ^ 16
  for i in [0:28] do
    let z := (z0 >>> (63 - i)) % 2
    let temp := rotateRight16 k[i + 3]! 3 ^^^ k[i + 1]!
    k := k.push (c ^^^ z ^^^ k[i]! ^^^ temp ^^^ rotateRight16 temp 1)
  let mut left := x % 2 ^ 16
  let mut right := (x >>> 16) % 2 ^ 16
  for i in [0:32] do
    let effective := k[4 * (i / 4) + (i % 4 + lane) % 4]!
    let f := (rotateLeft16 left 1 &&& rotateLeft16 left 8) ^^^ rotateLeft16 left 2
    let next := right ^^^ f ^^^ effective
    right := left
    left := next
  pure ((right <<< 16) ||| left)

/-- The digest of `hashst` and `hashchk`: of the registers RA and RB, whose bytes are interleaved to two doublewords, each half of which
is a lane of the cipher. -/
def hashDigest (ra rb key : Nat) : Nat := Id.run do
  let mut high := 0
  let mut low := 0
  let mut ra := ra % 2 ^ 64
  let mut rb := rb % 2 ^ 64
  for i in [0:4] do
    high := high ||| rotateRight64 (rb % 256) (8 * (2 * i + 1))
    high := high ||| (((ra >>> 32) % 256) <<< (16 * i))
    low := low ||| rotateRight64 ((rb >>> 32) % 256) (8 * (2 * i + 1))
    low := low ||| ((ra % 256) <<< (16 * i))
    rb := rb >>> 8
    ra := ra >>> 8
  let first := (simonLike (high >>> 32) key 0 <<< 32) ||| simonLike (high % 2 ^ 32) key 1
  let second := (simonLike (low >>> 32) key 2 <<< 32) ||| simonLike (low % 2 ^ 32) key 3
  pure (first ^^^ second)

/-- The key of the hashes of a process, HASHKEYR, which Linux makes of random bits as a program starts: a run is the same each time, so
it is the same bits each time. -/
def hashKey : Nat := 0x9e3779b97f4a7c15

/-! ## The permute controls -/

/-- The bytes of a vector register, from the most significant. -/
private def bytesOf (count value : Nat) : List Nat := (List.range count).map fun index => (value >>> (8 * (count - 1 - index))) % 256
private def ofBytes (bytes : List Nat) : Nat := bytes.foldl (fun value byte => value * 256 + byte % 256) 0

/-- `xxgenpcvbm` and those of halfwords, words and doublewords: the control of a permutation that expands, by the elements that the
most significant bits of the elements of `mask` pick, or that compresses to them, with the bytes numbered from the most significant
(0 and 1 of `mode`) or from the least (2 and 3). What a compression leaves is zeros, as what the ISA leaves undefined, and so is the
whole of a mode that is reserved. -/
def permuteControl (mask mode size : Nat) : Nat :=
  let bytes := size / 8
  let count := 16 / bytes
  -- Of the bytes from the most significant, or, if `little`, of those from the least, in which the bit that picks an element is of
  -- the last of its bytes.
  let big (mask : List Nat) (compress little : Bool) : List Nat := Id.run do
    let picked (index : Nat) : Bool := mask.getD (index * bytes + (if little then bytes - 1 else 0)) 0 ≥ 128
    let mut out : Array Nat := Array.replicate 16 0
    let mut next := 0
    for index in [0:count] do
      if picked index then
        for k in [0:bytes] do
          if compress then out := out.set! (next * bytes + k) (index * bytes + k)
          else out := out.set! (index * bytes + k) (next * bytes + k)
        next := next + 1
      else if !compress then
        for k in [0:bytes] do
          out := out.set! (index * bytes + k) (index * bytes + k + 16)
    pure out.toList
  let source := bytesOf 16 mask
  match mode with
  | 0 => ofBytes (big source false false)
  | 1 => ofBytes (big source true false)
  | 2 => ofBytes (big source.reverse false true).reverse
  | 3 => ofBytes (big source.reverse true true).reverse
  | _ => 0

/-! ## The estimates of AltiVec -/

private def single : Float.Format := ⟨8, 23, false⟩

/-- The bits of a fixed point number that the estimates are worked out with. -/
private def precision : Nat := 320

/-- The natural logarithm of 2, in fixed point: the sum of `1 / (k 2^k)`. -/
private def ln2 : Nat := (List.range 400).foldl (fun sum index => sum + 2 ^ precision / ((index + 1) * 2 ^ (index + 1))) 0

/-- The logarithm of base 2 of a single, rounded to the nearest: of a NaN the quiet one, of a negative number the default NaN, of a
zero the negative infinity. The fraction comes a bit at a time from squaring the significand, with more bits than rounding takes. -/
def logEstimate (bits : Nat) : Nat :=
  match Float.unpack single bits with
  | .nan _ => Float.quiet single bits
  | .zero _ => Float.packInfinity single true
  | .infinity negative => if negative then 0x7fc00000 else bits
  | .finite true _ _ => 0x7fc00000
  | .finite false mantissa exponent =>
    -- The significand in [1, 2), and the integer part of the logarithm.
    let length := Nat.log2 mantissa
    let whole : Int := exponent + length
    let scale := 2 ^ precision
    let start := mantissa * scale / 2 ^ length
    let (fraction, _) := (List.range 96).foldl (fun (state : Nat × Nat) _ =>
      let squared := state.2 * state.2 / scale
      if squared ≥ 2 * scale then (2 * state.1 + 1, squared / 2) else (2 * state.1, squared)) (0, start)
    -- The value is `whole + fraction / 2^96`, and what is below is there unless the significand is 1.
    let value : Int := whole * 2 ^ 96 + fraction
    if value == 0 && start == scale then 0
    else Float.pack single .rne (value < 0) value.natAbs (-96) (start != scale)

/-- 2 to the power of a single, rounded to the nearest: of a NaN the quiet one, of the negative infinity zero. The power of the
fraction is the exponential series of it times the logarithm of 2. -/
def exponentEstimate (bits : Nat) : Nat :=
  match Float.unpack single bits with
  | .nan _ => Float.quiet single bits
  | .zero _ => 0x3f800000
  | .infinity negative => if negative then 0 else bits
  | .finite negative mantissa exponent =>
    -- Past what a single has there is nothing to work out: the infinity, or zero.
    if exponent + Nat.log2 mantissa ≥ 8 then (if negative then 0 else Float.packInfinity single false) else
    let scale := 2 ^ precision
    -- The number in fixed point, its floor and what is left of it, which isn't negative.
    let magnitude : Nat := if exponent ≥ 0 then (mantissa <<< exponent.toNat) * scale else mantissa * scale / 2 ^ (-exponent).toNat
    let fixed : Int := if negative then -(magnitude : Int) else (magnitude : Int)
    let exact := exponent ≥ 0 || mantissa * scale % 2 ^ (-exponent).toNat == 0
    let whole : Int := fixed.fdiv (scale : Int)
    let rest := (fixed - whole * (scale : Int)).toNat
    let power := rest * ln2 / scale
    let (sum, _) := (List.range 120).foldl (fun (state : Nat × Nat) index =>
      let term := state.2 * power / scale / (index + 1)
      (state.1 + term, term)) (scale, scale)
    let integral := rest == 0 && exact
    Float.pack single .rne false (if integral then scale else sum) (whole - precision) (!integral)

/-! ## The outer products of the matrix-multiply assist -/

private def float (name : String) (inputs : List Nat) : Nat :=
  ((Float.evaluateWith .powerpc name inputs).map (·.2)).getD 0

/-- Whether the bits of a format of a width are a NaN, and the quiet one of it. -/
private def isNaN (width bits : Nat) : Bool :=
  match Float.formatOf width with
  | some format => (match Float.unpack format bits with | .nan _ => true | _ => false)
  | none => false

private def quiet (width bits : Nat) : Nat :=
  match Float.formatOf width with
  | some format => Float.quiet format bits
  | none => bits

/-- An operation of a width whose NaN is the first of its operands that is one, in the order that PowerPC has of a multiplication and
an addition: the multiplicand, the addend, and the multiplier. -/
private def firstNaN (width : Nat) (order : List Nat) (otherwise : Nat) : Nat :=
  match order.find? (isNaN width) with
  | some nan => quiet width nan
  | none => otherwise

private def modeName (rounding : Nat) : String := ["rne", "rtz", "rtp", "rtn"].getD (rounding % 4) "rne"

/-- An element of `size` bits of a register of `width`, from the most significant. -/
private def element (width size value index : Nat) : Nat := (value >>> (width - size * (index + 1))) % 2 ^ size

private def signed (size value : Nat) : Int := if value ≥ 2 ^ (size - 1) then (value : Int) - 2 ^ size else value

private def saturate (value : Int) : Int := max (-(2 ^ 31 : Int)) (min value (2 ^ 31 - 1))

private def wrap (value : Int) : Nat := (value % 2 ^ 32).toNat

/-- The negative of a number that isn't a NaN, as the products that are taken away are. -/
private def negate (width bits : Nat) : Nat :=
  let magnitude := bits % 2 ^ (width - 1)
  let exponentBits := if width == 32 then 8 else 11
  if magnitude > (2 ^ exponentBits - 1) * 2 ^ (width - 1 - exponentBits) then bits
  else if bits ≥ 2 ^ (width - 1) then magnitude else magnitude + 2 ^ (width - 1)

/-- The masks of a prefixed form, or all of each: of the rows, of the columns, and of the products of a sum. -/
structure Masks where
  rows : Nat := 15
  columns : Nat := 15
  products : Nat := 255

/-- What a name of an outer product says: its elements, whether it accumulates and with which signs, and whether it saturates. -/
structure Product where
  kind : String
  accumulates : Bool := false
  negativeProduct : Bool := false
  negativeSum : Bool := false
  saturatesSum : Bool := false
  /-- Of a form that doesn't accumulate: the sum of its products saturates. -/
  saturates : Bool := false

/-- The product of a name without its prefix, e.g., `xvf32gerpn`. -/
def Product.ofName (name : String) : Option Product :=
  let kinds := ["xvi4ger8", "xvi8ger4", "xvi16ger2", "xvf16ger2", "xvbf16ger2", "xvf32ger", "xvf64ger"]
  kinds.findSome? fun kind =>
    if name.startsWith kind then
      match (name.drop kind.length).toString with
      | "" => some { kind }
      | "s" => some { kind, saturates := true }
      | "pp" => some { kind, accumulates := true }
      | "pn" => some { kind, accumulates := true, negativeSum := true }
      | "np" => some { kind, accumulates := true, negativeProduct := true }
      | "nn" => some { kind, accumulates := true, negativeProduct := true, negativeSum := true }
      | "spp" => some { kind, accumulates := true, saturatesSum := true }
      | _ => none
    else none

/-- An accumulator after an outer product of two registers: 4 rows of 4 words, or of 2 doublewords, of the sum of the products of the
parts of an element of each, or of the elements, with what it had if it accumulates. An element that a mask leaves out is zero. -/
def outerProduct (product : Product) (rounding : Nat) (masks : Masks) (accumulator x y : Nat) : Nat := Id.run do
  let mode := modeName rounding
  let double := product.kind == "xvf64ger"
  let (size, columns) := if double then (64, 2) else (32, 4)
  let mut out := 0
  for row in [0:4] do
    for column in [0:columns] do
      let old := element 512 size accumulator (row * columns + column)
      let on := (masks.rows >>> (3 - row)) % 2 == 1 && (masks.columns >>> (columns - 1 - column)) % 2 == 1
      let a := element (if double then 256 else 128) size x row
      let b := element 128 size y column
      -- The products of the parts of the two elements that the mask has, of `parts` each.
      let integers (parts bits : Nat) (signedSecond : Bool) : Int :=
        (List.range parts).foldl (fun sum index =>
          if (masks.products >>> (parts - 1 - index)) % 2 == 1 then
            let left := signed bits (element 32 bits a index)
            let right : Int := if signedSecond then signed bits (element 32 bits b index) else element 32 bits b index
            sum + left * right
          else sum) 0
      let integer (sum : Int) (saturates : Bool) : Nat :=
        let sum := if saturates then saturate sum else sum
        if !product.accumulates then wrap sum
        else if product.saturatesSum then wrap (saturate (sum + signed 32 old))
        else wrap (sum + signed 32 old)
      -- Halves, of either format, as doubles, in which their products are exact: the sum of the two is rounded once, to a single.
      let halves (widen : Nat → Nat) : Nat :=
        let part (value index : Nat) : Nat :=
          if (masks.products >>> (1 - index)) % 2 == 1 then widen (element 32 16 value index) else 0
        let first := firstNaN 64 [part a 0, part b 0] (float "fmul_rne_ieee754_binary_64" [part a 0, part b 0])
        let wide (bits : Nat) : Nat := float "fconvert_rne_ieee754_binary_64_128" [bits]
        let sum := firstNaN 64 [part a 1, first, part b 1]
          (float "fconvert_rod_ieee754_binary_128_64" [float "fmad_rod_ieee754_binary_128" [wide (part a 1), wide (part b 1), wide first]])
        -- A NaN keeps the bits that a single has of it; a number, rounded to odd in more bits than a single, is rounded once.
        let result := if isNaN 64 sum then
            (sum >>> 63) * 2 ^ 31 + 0x7fc00000 + ((sum >>> 29) % 2 ^ 22)
          else float s!"fconvert_{mode}_ieee754_binary_64_32" [sum]
        if !product.accumulates then result
        else
          let result := if product.negativeProduct then negate 32 result else result
          let old := if product.negativeSum then negate 32 old else old
          firstNaN 32 [result, old] (float s!"fadd_{mode}_ieee754_binary_32" [result, old])
      let fused (width : Nat) : Nat :=
        if !product.accumulates then firstNaN width [a, b] (float s!"fmul_{mode}_ieee754_binary_{width}" [a, b])
        else
          -- As the ISA has them: the product with what was there added or, of `pn` and `np`, taken away, and of `np` and `nn` the
          -- negative of that, which a NaN isn't.
          let addend := if product.negativeSum != product.negativeProduct then negate width old else old
          let sum := float s!"fmad_{mode}_ieee754_binary_{width}" [a, b, addend]
          firstNaN width [a, old, b] (if product.negativeProduct then negate width sum else sum)
      let value := if !on then 0 else match product.kind with
        | "xvi4ger8" => integer (integers 8 4 true) false
        | "xvi8ger4" => integer (integers 4 8 false) false
        | "xvi16ger2" => integer (integers 2 16 true) product.saturates
        | "xvf16ger2" => halves fun half => float "fconvert_rne_ieee754_binary_16_64" [half]
        | "xvbf16ger2" => halves fun half => float "fconvert_rne_ieee754_binary_32_64" [half <<< 16]
        | "xvf32ger" => fused 32
        | _ => fused 64
      out := out ||| (value <<< (512 - size * (row * columns + column + 1)))
  pure out

/-- An outer product by the name of its instruction and what the semantics give it: the rounding mode, the accumulator if it
accumulates, the two registers, and the masks of a prefixed form. -/
private def serveProduct (name : String) (inputs : List Nat) : Option (Nat × Nat) := do
  let prefixed := name.startsWith "pm"
  let product ← Product.ofName (if prefixed then (name.drop 2).toString else name)
  if product.saturates && product.kind != "xvi16ger2" then none
  let (rounding, inputs) ← match inputs with
    | rounding :: rest => some (rounding, rest)
    | [] => none
  let (accumulator, inputs) ← if product.accumulates then
      match inputs with
      | accumulator :: rest => some (accumulator, rest)
      | [] => none
    else some (0, inputs)
  match inputs with
  | [x, y] => some (512, outerProduct product rounding {} accumulator x y)
  | [x, y, rows, columns] => some (512, outerProduct product rounding { rows, columns } accumulator x y)
  | [x, y, rows, columns, products] =>
    -- The mask of the products of a sum of 2 or of 4 is of as many bits, and that of 8 of 8.
    some (512, outerProduct product rounding { rows, columns, products } accumulator x y)
  | _ => none

/-- What serves an intrinsic of PowerPC that isn't of the floating point: its width and its bits, by its name and its operands. -/
def serve (name : String) (inputs : List Nat) : Option (Nat × Nat) :=
  if !name.startsWith "powerpc-" then none else
  let name := (name.drop 8).toString
  match name, inputs with
  | "hash", [ra, rb] => some (64, hashDigest ra rb hashKey)
  | "xxgenpcv", [mask, mode, size] => some (128, permuteControl mask mode size)
  | "exptefp", [x] => some (32, exponentEstimate x)
  | "logefp", [x] => some (32, logEstimate x)
  | _, _ => (serveProduct name inputs).orElse fun _ => Decimal.serve name inputs

end Bap.PowerPC
