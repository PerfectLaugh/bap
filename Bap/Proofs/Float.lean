import Bap.Float

/-! Known values of the software float, checked by the kernel, in the formats and the corners that go wrong first. That it agrees
with a real processor in general is tested (`testsuite/src/libc-floats.c`), and so are the names of `evaluate`. -/

namespace Bap.Float

private abbrev f32 : Format := ⟨8, 23, false⟩
private abbrev f64 : Format := ⟨11, 52, false⟩
private abbrev f80 : Format := ⟨15, 63, true⟩

/-- 1 + 1 = 2. -/
theorem one_plus_one : add f64 .rne 0x3ff0000000000000 0x3ff0000000000000 = 0x4000000000000000 := by decide +kernel

/-- 0.1 + 0.2 is 0.30000000000000004, which rounding gets. -/
theorem tenths : add f64 .rne 0x3fb999999999999a 0x3fc999999999999a = 0x3fd3333333333334 := by decide +kernel

/-- 1 / 3 rounds down at the last bit, and 2 / 3 up. -/
theorem thirds : div f64 .rne 0x3ff0000000000000 0x4008000000000000 = 0x3fd5555555555555 ∧
    div f64 .rne 0x4000000000000000 0x4008000000000000 = 0x3fe5555555555555 := by decide +kernel

/-- Rounding modes differ where they should: 1 / 3 towards positive infinity is one bit up. -/
theorem directed : div f64 .rtp 0x3ff0000000000000 0x4008000000000000 = 0x3fd5555555555556 ∧
    div f64 .rtn 0x3ff0000000000000 0x4008000000000000 = 0x3fd5555555555555 := by decide +kernel

/-- The root of 2. -/
theorem root_two : sqrt f64 .rne 0x4000000000000000 = 0x3ff6a09e667f3bcd := by decide +kernel

/-- The smallest number halves to zero, ties to even, and twice it is exact. -/
theorem smallest : div f64 .rne 1 0x4000000000000000 = 0 ∧ add f64 .rne 1 1 = 2 := by decide +kernel

/-- Overflow goes to infinity, or to the largest number towards zero, and x - x is +0, or -0 rounding down. -/
theorem corners : mul f64 .rne 0x7fe0000000000000 0x4000000000000000 = 0x7ff0000000000000 ∧
    mul f64 .rtz 0x7fe0000000000000 0x4000000000000000 = 0x7fefffffffffffff ∧
    sub f64 .rne 0x3ff8000000000000 0x3ff8000000000000 = 0 ∧
    sub f64 .rtn 0x3ff8000000000000 0x3ff8000000000000 = 0x8000000000000000 := by decide +kernel

/-- What has no answer is the default NaN of x86: 0 / 0, and the root of -1. -/
theorem invalid : div f64 .rne 0 0 = 0xfff8000000000000 ∧ sqrt f64 .rne 0xbff0000000000000 = 0xfff8000000000000 := by
  decide +kernel

/-- A NaN is no less than anything, nor anything than it, and -0 and +0 are equal. -/
theorem order : compare f64 0x7ff8000000000000 0x3ff0000000000000 = none ∧
    compare f64 0x3ff0000000000000 0x7ff8000000000000 = none ∧
    compare f64 0x8000000000000000 0 = some (false, true) := by decide +kernel

/-- 1.5 is the same in each format. -/
theorem conversions : convert f64 f32 .rne 0x3ff8000000000000 = 0x3fc00000 ∧
    convert f64 f80 .rne 0x3ff8000000000000 = 0x3fffc000000000000000 ∧
    convert f80 f64 .rne 0x3fffc000000000000000 = 0x3ff8000000000000 := by decide +kernel

/-- An integer that needs rounding, ties to even: 2^53 + 1 goes down. And -3.7 truncates to -3. -/
theorem integers : ofSigned f64 .rne 64 9007199254740993 = 0x4340000000000000 ∧
    toInteger f64 .rtz 64 0xc00d99999999999a = 2 ^ 64 - 3 := by decide +kernel

/-- A fused multiply and add rounds once: (1 + 2^-52)^2 - (1 + 2^-51) is the 2^-104 that separate rounding would lose. -/
theorem fused : fma f64 .rne 0x3ff0000000000001 0x3ff0000000000001 0xbff0000000000002 = 0x3970000000000000 := by decide +kernel

end Bap.Float
