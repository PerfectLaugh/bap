import BapTests.Support

namespace Bap.Tests.IEEE754

open Bap
open Bap.Theory.IEEE754

private def roundTrip (parameters : Parameters) (value : Theory.IEEE754.Value) : Option Theory.IEEE754.Value :=
  decodeEncoded parameters (encode parameters value)

private def encoded (parameters : Parameters) (value : Theory.IEEE754.Value) : Option Nat :=
  (encode parameters value).map BitVec.toNat

def run : IO Unit := do
  assertEqual "binary64 parameters" (some ⟨2, 1023, 64, 53, 11, 52⟩) (binaryFormat 64)
  assertEqual "binary128 parameters" (some ⟨2, 16383, 128, 113, 15, 112⟩) (binaryFormat 128)
  assertEqual "invalid binary width" none (binaryFormat 0)
  assertEqual "invalid odd binary width" none (binaryFormat 31)
  assertEqual "decimal width accepted" (some (decimal 32)) (decimalFormat 32)
  assertEqual "binary32 one encoding" (some 0x3f800000) (encoded binary32 (.normal false 0 0))
  assertEqual "binary32 negative two encoding" (some 0xc0000000) (encoded binary32 (.normal true 1 0))
  assertEqual "binary32 infinity encoding" (some 0x7f800000) (encoded binary32 (.infinity false))
  assertEqual "binary32 one round trip" (some (.normal false 0 0)) (roundTrip binary32 (.normal false 0 0))
  assertEqual "binary32 infinity round trip" (some (.infinity true)) (roundTrip binary32 (.infinity true))
  assertEqual "binary32 NaN round trip" (some (.nan false 0x400000)) (roundTrip binary32 (.nan false 0x400000))
  assertEqual "signed zero round trip" (some (.zero true)) (roundTrip binary32 (.zero true))
  assertEqual "binary16 subnormal encoding" (some 1) (encoded binary16 (.subnormal false 1))
  assertEqual "binary16 minimum normal encoding" (some 0x0400) (encoded binary16 (.normal false (-14) 0))
  assertEqual "binary16 subnormal round trip" (some (.subnormal true 1)) (roundTrip binary16 (.subnormal true 1))
  assertEqual "invalid normal rejected" none (encoded binary32 (.normal false 10000 0))
  assertEqual "binary80 zero encoding" (some 0) (encoded binary80 (.zero false))
  assertEqual "binary80 one encoding" (some 0x3fff8000000000000000) (encoded binary80 (.normal false 0 0))
  assertEqual "binary80 negative two encoding" (some 0xc0008000000000000000) (encoded binary80 (.normal true 1 0))
  assertEqual "binary80 infinity encoding" (some 0x7fff8000000000000000) (encoded binary80 (.infinity false))
  assertEqual "binary80 quiet NaN encoding" (some 0x7fffc000000000000000)
    (encoded binary80 (.nan false 0x4000000000000000))
  assertEqual "binary80 subnormal encoding" (some 1) (encoded binary80 (.subnormal false 1))
  assertEqual "binary80 minimum normal encoding" (some 0x00018000000000000000)
    (encoded binary80 (.normal false (-16382) 0))
  assertEqual "binary80 maximum encoding" (some 0x7ffeffffffffffffffff)
    (encoded binary80 (.normal false 16383 (2 ^ 63 - 1)))
  assertEqual "binary80 oversized fraction rejected" none (encoded binary80 (.normal false 0 (2 ^ 63)))
  assertEqual "binary80 one round trip" (some (.normal false 0 0)) (roundTrip binary80 (.normal false 0 0))
  assertEqual "binary80 infinity round trip" (some (.infinity true)) (roundTrip binary80 (.infinity true))
  assertEqual "binary80 NaN round trip" (some (.nan true 5)) (roundTrip binary80 (.nan true 5))
  assertEqual "binary80 subnormal round trip" (some (.subnormal false 7)) (roundTrip binary80 (.subnormal false 7))
  assertEqual "binary80 pseudo-infinity is infinity" (some (.infinity false))
    (decode binary80 (BitVec.ofNat 80 0x7fff0000000000000000))
  assertEqual "binary80 unnormal is NaN" (some (.nan false 1))
    (decode binary80 (BitVec.ofNat 80 0x3fff0000000000000001))
  assertEqual "binary80 pseudo-denormal keeps integer bit" (some (.subnormal false (2 ^ 63)))
    (decode binary80 (BitVec.ofNat 80 0x00008000000000000000))
  assertTrue "NaN classification" (Theory.IEEE754.Value.isNan (.nan false 1))
  assertTrue "infinity classification" (Theory.IEEE754.Value.isInf (.infinity false))
  assertTrue "zero classification" (Theory.IEEE754.Value.isZero (.zero false))
  assertTrue "subnormal classification" (Theory.IEEE754.Value.isSubnormal (.subnormal false 1))
  assertEqual "nearest-even positive tie" (some 2) (roundRatio .rne 5 2)
  assertEqual "nearest-even next tie" (some 4) (roundRatio .rne 7 2)
  assertEqual "nearest-even negative tie" (some (-2)) (roundRatio .rne (-5) 2)
  assertEqual "nearest-even negative odd tie" (some (-4)) (roundRatio .rne (-7) 2)
  assertEqual "nearest-away positive tie" (some 3) (roundRatio .rna 5 2)
  assertEqual "nearest-away negative tie" (some (-3)) (roundRatio .rna (-5) 2)
  assertEqual "round toward zero" (some (-3)) (roundRatio .rtz (-7) 2)
  assertEqual "round toward positive infinity" (some (-3)) (roundRatio .rtp (-7) 2)
  assertEqual "round toward negative infinity" (some (-4)) (roundRatio .rtn (-7) 2)
  assertEqual "division by zero rejected" none (roundRatio .rne 1 0)

/-- What conversions to an integer and rounding to one raise, as x86 and RISC-V have them: of the integer of the mode that the name
says, also of what saturates, and of ROUNDSD, but for what its bit 3 keeps quiet. -/
def runRaised : IO Unit := do
  let raised (rules : Bap.Float.NaNRules) (name : String) (input : Nat) : Bap.Float.Raised :=
    Bap.Float.raisedBy rules name [input] (((Bap.Float.evaluateWith rules name [input]).map (·.2)).getD 0)
  let half := 0x41DFFFFFFFE00000
  assertEqual "x86 cvtsd2si of 2147483647.5 to nearest is invalid, and no more" ({ invalid := true } : Bap.Float.Raised)
    (raised .x86 "cast_sint_rne_ieee754_binary_64_32" half)
  assertEqual "RISC-V fcvt.w.d of 2147483647.5 to nearest is invalid" ({ invalid := true } : Bap.Float.Raised)
    (raised .riscv "cast_sint_rne_ieee754_binary_64_32" half)
  assertEqual "-0.5 down to an unsigned integer is invalid" ({ invalid := true } : Bap.Float.Raised)
    (raised .x86 "cast_int_rtn_ieee754_binary_64_32" 0xBFE0000000000000)
  assertEqual "RISC-V fcvt.wu.d of -0.5 toward zero is 0 and inexact" ({ inexact := true } : Bap.Float.Raised)
    (raised .riscv "cast_int_rtz_ieee754_binary_64_32" 0xBFE0000000000000)
  assertEqual "RISC-V fcvt.wu.d of 4294967295.5 toward zero is inexact" ({ inexact := true } : Bap.Float.Raised)
    (raised .riscv "cast_int_rtz_ieee754_binary_64_32" 0x41EFFFFFFFF00000)
  assertEqual "roundsd of a signaling NaN is invalid" ({ invalid := true } : Bap.Float.Raised)
    (raised .x86 "fround_rne_ieee754_binary_64" 0x7FF0000000000001)
  assertEqual "roundsd of 1.5 is inexact" ({ inexact := true } : Bap.Float.Raised) (raised .x86 "fround_rne_ieee754_binary_64" 0x3FF8000000000000)
  assertEqual "roundsd of 1.5 with bit 3 is quiet" ({} : Bap.Float.Raised) (raised .x86 "froundq_rne_ieee754_binary_64" 0x3FF8000000000000)
  assertEqual "and gives 2" (some 0x4000000000000000) ((Bap.Float.evaluateWith .x86 "froundq_rne_ieee754_binary_64" [0x3FF8000000000000]).map (·.2))
  -- An unnormal and a pseudo-infinity of x87, which the 387 and after take as invalid operands: the default NaN, the indefinite.
  let one := (0x3fff <<< 64) ||| 0x8000000000000000
  for (label, operand) in [("an unnormal", (0x3fff <<< 64) ||| 0x4000000000000000), ("a pseudo-infinity", 0x7fff <<< 64)] do
    let given := [operand, one]
    let result := ((Bap.Float.evaluateWith .x86 "fadd_rne_ieee754_binary_80" given).map (·.2)).getD 0
    assertEqual s!"x87 fadd of {label} is invalid" true (Bap.Float.raisedBy .x86 "fadd_rne_ieee754_binary_80" given result).invalid
    assertEqual s!"and gives the indefinite, of {label}" 0xFFFFC000000000000000 result

end Bap.Tests.IEEE754
