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
  assertEqual "binary80 encoding rejected explicitly" none (encoded binary80 (.zero false))
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

end Bap.Tests.IEEE754
