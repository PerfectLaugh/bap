import Lean
import Bap.IO.Reader

namespace Bap.Proofs.IO

open Bap.IO.Reader

open Lean in
/-- `open_private Mod Ns x y` makes the private constants `Ns.x`, `Ns.y` of module `Mod` nameable here. -/
local elab "open_private " mod:ident ns:ident names:ident* : command => do
  for name in names do
    let target := mkPrivateNameCore mod.getId (ns.getId ++ name.getId)
    let alias := (← getCurrNamespace) ++ name.getId
    modifyEnv (addAlias · alias target)

open_private Bap.IO.Reader Bap.IO.Reader readLoop

/-- The unsigned value of byte `i`, as the reader sees it. -/
abbrev byteAt (data : ByteArray) (i : Nat) : Nat := (data.get! i).toNat

/-- Least-significant-byte-first value of the `count` bytes at `offset`. -/
def littleValue (data : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => littleValue data offset n + byteAt data (offset + n) * 256 ^ n

/-- Most-significant-byte-first value of the `count` bytes at `offset`. -/
def bigValue (data : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => bigValue data offset n * 256 + byteAt data (offset + n)

theorem byteAt_lt (data : ByteArray) (i : Nat) : byteAt data i < 256 :=
  (data.get! i).toNat_lt

/-! ## get8 -/

theorem get8_of_lt {data : ByteArray} {offset : Nat} (h : offset < data.size) :
    get8 data offset = .ok (byteAt data offset) := by
  simp only [get8]
  rw [ite_eq_right (by omega)]

theorem get8_ok_iff {data : ByteArray} {offset value : Nat} :
    get8 data offset = .ok value ↔ offset < data.size ∧ value = byteAt data offset := by
  by_cases h : offset < data.size
  · rw [get8_of_lt h]
    constructor
    · intro e; cases e; exact ⟨h, rfl⟩
    · rintro ⟨_, rfl⟩; rfl
  · simp only [get8]
    rw [ite_eq_left (by omega)]
    constructor
    · intro e; cases e
    · rintro ⟨h', _⟩; exact absurd h' h

theorem get8_isOk_iff {data : ByteArray} {offset : Nat} :
    (get8 data offset).isOk = true ↔ offset < data.size := by
  by_cases h : offset < data.size
  · simp [get8_of_lt h, Except.isOk, Except.toBool, h]
  · simp only [get8]
    rw [ite_eq_left (by omega)]
    simp [Except.isOk, Except.toBool, h]

theorem get8_lt_256 {data : ByteArray} {offset value : Nat}
    (h : get8 data offset = .ok value) : value < 256 := by
  rw [(get8_ok_iff.mp h).2]
  exact byteAt_lt data offset

/-! ## read: bounds and value -/

private theorem readLoop_little (data : ByteArray) (offset count : Nat) :
    ∀ (index result : Nat), offset + index ≤ data.size →
      readLoop data .little offset count index result =
        .ok (result + littleValue data offset index)
  | 0, result, _ => by simp [readLoop, littleValue]
  | index + 1, result, h => by
    have hlt : offset + index < data.size := by omega
    have ih := readLoop_little data offset count index
      (result + byteAt data (offset + index) * 256 ^ index) (by omega)
    simp only [readLoop, get8_of_lt hlt, bind, Except.bind]
    rw [ih]
    simp only [littleValue]
    congr 1
    omega

private theorem readLoop_big (data : ByteArray) (offset count : Nat) :
    ∀ (index result : Nat), offset + index ≤ data.size → index ≤ count →
      readLoop data .big offset count index result =
        .ok (result + bigValue data offset index * 256 ^ (count - index))
  | 0, result, _, _ => by simp [readLoop, bigValue]
  | index + 1, result, h, hc => by
    have hlt : offset + index < data.size := by omega
    have ih := readLoop_big data offset count index
      (result + byteAt data (offset + index) * 256 ^ (count - index - 1)) (by omega) (by omega)
    simp only [readLoop, get8_of_lt hlt, bind, Except.bind]
    rw [ih]
    simp only [bigValue]
    congr 1
    have hpow : 256 ^ (count - index) = 256 ^ (count - index - 1) * 256 := by
      rw [← Nat.pow_succ]; congr 1; omega
    have hsub : count - (index + 1) = count - index - 1 := by omega
    have hdist : (bigValue data offset index * 256 + byteAt data (offset + index)) * 256 ^ (count - index - 1) =
        bigValue data offset index * (256 ^ (count - index - 1) * 256) +
          byteAt data (offset + index) * 256 ^ (count - index - 1) := by
      rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256]
    rw [hpow, hsub, hdist]
    omega

theorem read_little {data : ByteArray} {offset count : Nat} (h : offset + count ≤ data.size) :
    read data .little offset count = .ok (littleValue data offset count) := by
  simp only [Bap.IO.Reader.read]
  rw [ite_eq_right (by omega), readLoop_little data offset count count 0 h, Nat.zero_add]

theorem read_big {data : ByteArray} {offset count : Nat} (h : offset + count ≤ data.size) :
    read data .big offset count = .ok (bigValue data offset count) := by
  simp only [Bap.IO.Reader.read]
  rw [ite_eq_right (by omega), readLoop_big data offset count count 0 h (Nat.le_refl _)]
  simp

/-- Out-of-range reads fail before any byte is inspected; there is no partial result. -/
theorem read_out_of_range {data : ByteArray} {endian : Endian} {offset count : Nat}
    (h : data.size < offset + count) :
    read data endian offset count =
      .error s!"{count}-byte read past end of input at {offset}" := by
  simp only [Bap.IO.Reader.read]
  rw [ite_eq_left h]

theorem read_isOk_iff {data : ByteArray} {endian : Endian} {offset count : Nat} :
    (read data endian offset count).isOk = true ↔ offset + count ≤ data.size := by
  by_cases h : offset + count ≤ data.size
  · cases endian
    · simp [read_little h, Except.isOk, Except.toBool, h]
    · simp [read_big h, Except.isOk, Except.toBool, h]
  · simp [read_out_of_range (endian := endian) (by omega : data.size < offset + count),
      Except.isOk, Except.toBool, h]

theorem read_ok_bounds {data : ByteArray} {endian : Endian} {offset count value : Nat}
    (h : read data endian offset count = .ok value) : offset + count ≤ data.size :=
  (read_isOk_iff (endian := endian)).mp (by simp [h, Except.isOk, Except.toBool])

theorem littleValue_lt (data : ByteArray) (offset : Nat) :
    ∀ count, littleValue data offset count < 256 ^ count
  | 0 => by simp [littleValue]
  | n + 1 => by
    have ih := littleValue_lt data offset n
    have hb := byteAt_lt data (offset + n)
    have hp : 0 < 256 ^ n := Nat.pow_pos (by decide)
    simp only [littleValue, Nat.pow_succ]
    have : byteAt data (offset + n) * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

theorem bigValue_lt (data : ByteArray) (offset : Nat) :
    ∀ count, bigValue data offset count < 256 ^ count
  | 0 => by simp [bigValue]
  | n + 1 => by
    have ih := bigValue_lt data offset n
    have hb := byteAt_lt data (offset + n)
    simp only [bigValue, Nat.pow_succ]
    omega

/-- A successful `count`-byte read fits in `count` bytes, under either byte order. -/
theorem read_lt {data : ByteArray} {endian : Endian} {offset count value : Nat}
    (h : read data endian offset count = .ok value) : value < 256 ^ count := by
  have hb := read_ok_bounds h
  cases endian
  · rw [read_little hb] at h; cases h; exact littleValue_lt ..
  · rw [read_big hb] at h; cases h; exact bigValue_lt ..

/-! ## Algebra of the byte orders -/

theorem littleValue_cons (data : ByteArray) (offset : Nat) :
    ∀ n, littleValue data offset (n + 1) =
      byteAt data offset + 256 * littleValue data (offset + 1) n
  | 0 => by simp [littleValue]
  | n + 1 => by
    have ih := littleValue_cons data offset n
    have hoff : offset + 1 + n = offset + (n + 1) := by omega
    rw [littleValue, ih]
    conv => rhs; rw [littleValue, hoff]
    rw [Nat.mul_add, Nat.pow_succ 256 n, Nat.mul_left_comm 256, Nat.mul_comm 256 (256 ^ n)]
    omega

theorem bigValue_cons (data : ByteArray) (offset : Nat) :
    ∀ n, bigValue data offset (n + 1) =
      byteAt data offset * 256 ^ n + bigValue data (offset + 1) n
  | 0 => by simp [bigValue]
  | n + 1 => by
    have ih := bigValue_cons data offset n
    have hoff : offset + 1 + n = offset + (n + 1) := by omega
    rw [bigValue, ih]
    conv => rhs; rw [bigValue, hoff]
    rw [Nat.add_mul, Nat.pow_succ, Nat.mul_assoc]
    omega

/-- A little-endian read of `m + n` bytes is the low `m` bytes plus the shifted high `n` bytes. -/
theorem littleValue_append (data : ByteArray) (offset m n : Nat) :
    littleValue data offset (m + n) =
      littleValue data offset m + 256 ^ m * littleValue data (offset + m) n := by
  induction n with
  | zero => simp [littleValue]
  | succ n ih =>
    have hoff : offset + (m + n) = offset + m + n := by omega
    rw [← Nat.add_assoc, littleValue, ih, littleValue, hoff, Nat.mul_add, Nat.pow_add,
      Nat.mul_left_comm (256 ^ m), Nat.mul_comm (256 ^ m) (256 ^ n), Nat.mul_comm (256 ^ m)]
    simp only [Nat.mul_assoc, Nat.mul_comm, Nat.add_assoc]

/-- A big-endian read of `m + n` bytes is the shifted high `m` bytes plus the low `n` bytes. -/
theorem bigValue_append (data : ByteArray) (offset m n : Nat) :
    bigValue data offset (m + n) =
      bigValue data offset m * 256 ^ n + bigValue data (offset + m) n := by
  induction n with
  | zero => simp [bigValue]
  | succ n ih =>
    have hoff : offset + (m + n) = offset + m + n := by omega
    rw [← Nat.add_assoc, bigValue, ih, bigValue, hoff, Nat.add_mul, Nat.pow_succ, Nat.mul_assoc]
    omega

/-- Big-endian is little-endian of the mirrored bytes, in any two arrays that mirror each other. -/
theorem littleValue_eq_bigValue_of_mirror {left right : ByteArray} :
    ∀ {n leftOffset rightOffset : Nat},
      (∀ i, i < n → left.get! (leftOffset + i) = right.get! (rightOffset + (n - 1 - i))) →
      littleValue left leftOffset n = bigValue right rightOffset n
  | 0, _, _, _ => by simp [littleValue, bigValue]
  | n + 1, leftOffset, rightOffset, h => by
    have ih := littleValue_eq_bigValue_of_mirror (left := left) (right := right)
      (n := n) (leftOffset := leftOffset + 1) (rightOffset := rightOffset) (by
        intro i hi
        have := h (i + 1) (by omega)
        have e1 : leftOffset + (i + 1) = leftOffset + 1 + i := by omega
        have e2 : n + 1 - 1 - (i + 1) = n - 1 - i := by omega
        rwa [e1, e2] at this)
    have h0 := h 0 (by omega)
    have e3 : n + 1 - 1 - 0 = n := by omega
    rw [Nat.add_zero, e3] at h0
    rw [littleValue_cons, ih, bigValue, byteAt, byteAt, h0]
    omega

/-- Little-endian decoding recovers `value` modulo `256 ^ count` from its base-256 digits. -/
theorem littleValue_of_digits {data : ByteArray} {offset value : Nat} :
    ∀ {count}, (∀ i, i < count → byteAt data (offset + i) = value / 256 ^ i % 256) →
      littleValue data offset count = value % 256 ^ count
  | 0, _ => by simp [littleValue, Nat.mod_one]
  | n + 1, h => by
    rw [littleValue, littleValue_of_digits fun i hi => h i (by omega), h n (by omega),
      Nat.mod_pow_succ, Nat.mul_comm]

/-- Conversely each base-256 digit of a little-endian read is the corresponding byte. -/
theorem littleValue_digit (data : ByteArray) :
    ∀ {i offset count}, i < count →
      littleValue data offset count / 256 ^ i % 256 = byteAt data (offset + i)
  | 0, offset, n + 1, _ => by
    rw [littleValue_cons]
    have := byteAt_lt data offset
    simp only [Nat.pow_zero, Nat.div_one, Nat.add_zero]
    omega
  | i + 1, offset, n + 1, h => by
    have ih := littleValue_digit data (i := i) (offset := offset + 1) (count := n) (by omega)
    have hb := byteAt_lt data offset
    have hoff : offset + 1 + i = offset + (i + 1) := by omega
    rw [hoff] at ih
    rw [littleValue_cons, Nat.pow_succ, Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
    have : (byteAt data offset + 256 * littleValue data (offset + 1) n) / 256 =
        littleValue data (offset + 1) n := by omega
    rw [this, ih]

/-! ## read: frame conditions -/

theorem littleValue_congr {left right : ByteArray} {leftOffset rightOffset : Nat} :
    ∀ {count}, (∀ i, i < count → left.get! (leftOffset + i) = right.get! (rightOffset + i)) →
      littleValue left leftOffset count = littleValue right rightOffset count
  | 0, _ => rfl
  | n + 1, h => by
    rw [littleValue, littleValue, littleValue_congr fun i hi => h i (by omega), byteAt, byteAt,
      h n (by omega)]

theorem bigValue_congr {left right : ByteArray} {leftOffset rightOffset : Nat} :
    ∀ {count}, (∀ i, i < count → left.get! (leftOffset + i) = right.get! (rightOffset + i)) →
      bigValue left leftOffset count = bigValue right rightOffset count
  | 0, _ => rfl
  | n + 1, h => by
    rw [bigValue, bigValue, bigValue_congr fun i hi => h i (by omega), byteAt, byteAt,
      h n (by omega)]

/-- A read depends only on the input size and the bytes it covers. -/
theorem read_congr {left right : ByteArray} {endian : Endian} {leftOffset rightOffset count : Nat}
    (hl : leftOffset + count ≤ left.size) (hr : rightOffset + count ≤ right.size)
    (h : ∀ i, i < count → left.get! (leftOffset + i) = right.get! (rightOffset + i)) :
    read left endian leftOffset count = read right endian rightOffset count := by
  cases endian
  · rw [read_little hl, read_little hr, littleValue_congr h]
  · rw [read_big hl, read_big hr, bigValue_congr h]

/-- Mirrored buffers read the same under opposite byte orders. -/
theorem read_little_eq_read_big_of_mirror {left right : ByteArray} {leftOffset rightOffset count : Nat}
    (hl : leftOffset + count ≤ left.size) (hr : rightOffset + count ≤ right.size)
    (h : ∀ i, i < count → left.get! (leftOffset + i) = right.get! (rightOffset + (count - 1 - i))) :
    read left .little leftOffset count = read right .big rightOffset count := by
  rw [read_little hl, read_big hr, littleValue_eq_bigValue_of_mirror h]

/-! ## Fixed widths and endianness -/

theorem u16_little {data : ByteArray} {offset : Nat} (h : offset + 2 ≤ data.size) :
    u16 data .little offset = .ok (byteAt data offset + byteAt data (offset + 1) * 256) := by
  simp [u16, read_little h, littleValue]

theorem u16_big {data : ByteArray} {offset : Nat} (h : offset + 2 ≤ data.size) :
    u16 data .big offset = .ok (byteAt data offset * 256 + byteAt data (offset + 1)) := by
  simp [u16, read_big h, bigValue]

theorem u32_little {data : ByteArray} {offset : Nat} (h : offset + 4 ≤ data.size) :
    u32 data .little offset = .ok (byteAt data offset + byteAt data (offset + 1) * 256 +
      byteAt data (offset + 2) * 65536 + byteAt data (offset + 3) * 16777216) := by
  simp [u32, read_little h, littleValue]

theorem u32_big {data : ByteArray} {offset : Nat} (h : offset + 4 ≤ data.size) :
    u32 data .big offset = .ok (byteAt data offset * 16777216 + byteAt data (offset + 1) * 65536 +
      byteAt data (offset + 2) * 256 + byteAt data (offset + 3)) := by
  have value : bigValue data offset 4 = byteAt data offset * 16777216 + byteAt data (offset + 1) * 65536 +
      byteAt data (offset + 2) * 256 + byteAt data (offset + 3) := by
    show (((0 * 256 + byteAt data offset) * 256 + byteAt data (offset + 1)) * 256 +
      byteAt data (offset + 2)) * 256 + byteAt data (offset + 3) = _
    omega
  exact (read_big h).trans (congrArg Except.ok value)

/-- A `u32` splits into its `u16` halves: low half first when little-endian. -/
theorem u32_little_split {data : ByteArray} {offset low high : Nat}
    (hl : u16 data .little offset = .ok low) (hh : u16 data .little (offset + 2) = .ok high) :
    u32 data .little offset = .ok (low + 65536 * high) := by
  have b := read_ok_bounds hh
  have hlv := read_little (data := data) (offset := offset) (count := 2) (by omega)
  have hhv := read_little (data := data) (offset := offset + 2) (count := 2) (by omega)
  simp only [u16] at hl hh
  rw [hlv] at hl
  rw [hhv] at hh
  cases hl; cases hh
  simp only [u32]
  rw [read_little (by omega), littleValue_append data offset 2 2]

theorem u32_big_split {data : ByteArray} {offset high low : Nat}
    (hh : u16 data .big offset = .ok high) (hl : u16 data .big (offset + 2) = .ok low) :
    u32 data .big offset = .ok (high * 65536 + low) := by
  have b := read_ok_bounds hl
  have hhv := read_big (data := data) (offset := offset) (count := 2) (by omega)
  have hlv := read_big (data := data) (offset := offset + 2) (count := 2) (by omega)
  simp only [u16] at hl hh
  rw [hhv] at hh
  rw [hlv] at hl
  cases hl; cases hh
  simp only [u32]
  rw [read_big (by omega), bigValue_append data offset 2 2]

theorem u64_little_split {data : ByteArray} {offset low high : Nat}
    (hl : u32 data .little offset = .ok low) (hh : u32 data .little (offset + 4) = .ok high) :
    u64 data .little offset = .ok (low + 4294967296 * high) := by
  have b := read_ok_bounds hh
  have hlv := read_little (data := data) (offset := offset) (count := 4) (by omega)
  have hhv := read_little (data := data) (offset := offset + 4) (count := 4) (by omega)
  simp only [u32] at hl hh
  rw [hlv] at hl
  rw [hhv] at hh
  cases hl; cases hh
  simp only [u64]
  rw [read_little (by omega), littleValue_append data offset 4 4]

theorem u64_big_split {data : ByteArray} {offset high low : Nat}
    (hh : u32 data .big offset = .ok high) (hl : u32 data .big (offset + 4) = .ok low) :
    u64 data .big offset = .ok (high * 4294967296 + low) := by
  have b := read_ok_bounds hl
  have hhv := read_big (data := data) (offset := offset) (count := 4) (by omega)
  have hlv := read_big (data := data) (offset := offset + 4) (count := 4) (by omega)
  simp only [u32] at hl hh
  rw [hhv] at hh
  rw [hlv] at hl
  cases hl; cases hh
  simp only [u64]
  rw [read_big (by omega), bigValue_append data offset 4 4]

/-- A little-endian read of a value's digits returns the value when it fits. -/
theorem read_little_of_digits {data : ByteArray} {offset count value : Nat}
    (hb : offset + count ≤ data.size) (hv : value < 256 ^ count)
    (h : ∀ i, i < count → byteAt data (offset + i) = value / 256 ^ i % 256) :
    read data .little offset count = .ok value := by
  rw [read_little hb, littleValue_of_digits h, Nat.mod_eq_of_lt hv]

/-- Little-endian reads are injective on the bytes they cover. -/
theorem read_little_injective {left right : ByteArray} {leftOffset rightOffset count value : Nat}
    (hl : read left .little leftOffset count = .ok value)
    (hr : read right .little rightOffset count = .ok value) :
    ∀ i, i < count → byteAt left (leftOffset + i) = byteAt right (rightOffset + i) := by
  intro i hi
  rw [read_little (read_ok_bounds hl)] at hl
  rw [read_little (read_ok_bounds hr)] at hr
  cases hl
  have := littleValue_digit left (offset := leftOffset) hi
  have := littleValue_digit right (offset := rightOffset) hi
  simp_all

/-! ## slice -/

theorem slice_of_le {data : ByteArray} {offset size : Nat} (h : offset + size ≤ data.size) :
    slice data offset size = .ok (data.extract offset (offset + size)) := by
  simp only [slice]
  rw [ite_eq_right (by omega)]

theorem slice_isOk_iff {data : ByteArray} {offset size : Nat} :
    (slice data offset size).isOk = true ↔ offset + size ≤ data.size := by
  by_cases h : offset + size ≤ data.size
  · simp [slice_of_le h, Except.isOk, Except.toBool, h]
  · simp only [slice]
    rw [ite_eq_left (by omega)]
    simp [Except.isOk, Except.toBool, h]

theorem slice_ok_size {data out : ByteArray} {offset size : Nat}
    (h : slice data offset size = .ok out) : out.size = size ∧ offset + size ≤ data.size := by
  have hb := (slice_isOk_iff (data := data) (offset := offset) (size := size)).mp
    (by simp [h, Except.isOk, Except.toBool])
  rw [slice_of_le hb] at h
  cases h
  refine ⟨?_, hb⟩
  simp only [ByteArray.size_extract]
  omega

theorem get!_eq_getElem {data : ByteArray} {i : Nat} (h : i < data.size) : data.get! i = data[i] := by
  cases data with
  | mk bytes =>
    show bytes[i]! = bytes[i]
    exact getElem!_pos bytes i h

theorem slice_ok_get! {data out : ByteArray} {offset size i : Nat}
    (h : slice data offset size = .ok out) (hi : i < size) :
    out.get! i = data.get! (offset + i) := by
  have ⟨hs, hb⟩ := slice_ok_size h
  rw [slice_of_le hb] at h
  cases h
  rw [get!_eq_getElem (by omega), get!_eq_getElem (by omega), ByteArray.getElem_extract]

/-- Reading out of a slice agrees with reading the same bytes from the original input. -/
theorem read_slice {data out : ByteArray} {endian : Endian} {offset size inner count : Nat}
    (h : slice data offset size = .ok out) (hc : inner + count ≤ size) :
    read out endian inner count = read data endian (offset + inner) count := by
  have ⟨hs, hb⟩ := slice_ok_size h
  apply read_congr (by omega) (by omega)
  intro i hi
  rw [slice_ok_get! h (by omega)]
  congr 1
  omega

/-! ## cstring -/

/-- Latin-1 decoding of the `n` bytes at `offset`. -/
def latin1 (data : ByteArray) (offset : Nat) : Nat → List Char
  | 0 => []
  | n + 1 => Char.ofNat (byteAt data offset) :: latin1 data (offset + 1) n

theorem latin1_length (data : ByteArray) : ∀ offset n, (latin1 data offset n).length = n
  | _, 0 => rfl
  | offset, n + 1 => by simp [latin1, latin1_length]

/-- `n` non-NUL in-range bytes at `offset`, terminated by a NUL. -/
def TerminatedAt (data : ByteArray) (offset n : Nat) : Prop :=
  offset + n < data.size ∧ byteAt data (offset + n) = 0 ∧ ∀ k, k < n → byteAt data (offset + k) ≠ 0

private theorem loop_of_terminated {data : ByteArray} {offset : Nat} :
    ∀ {n index chars}, TerminatedAt data (offset + index) n →
      cstring.loop data offset index chars =
        .ok (String.ofList (chars.reverse ++ latin1 data (offset + index) n))
  | 0, index, chars, ⟨hb, hz, _⟩ => by
    rw [cstring.loop]
    have hb' : ¬ offset + index ≥ data.size := by omega
    simp only [Nat.add_zero] at hz
    simp [hb', hz, latin1]
  | n + 1, index, chars, ⟨hb, hz, hk⟩ => by
    rw [cstring.loop]
    have hb' : ¬ offset + index ≥ data.size := by omega
    have hne := hk 0 (by omega)
    simp only [Nat.add_zero] at hne
    have ih := loop_of_terminated (data := data) (offset := offset) (n := n) (index := index + 1)
      (chars := Char.ofNat (byteAt data (offset + index)) :: chars)
      ⟨by omega, by
        have e : offset + (index + 1) + n = offset + index + (n + 1) := by omega
        rw [e]; exact hz, by
        intro k hlt
        have e : offset + (index + 1) + k = offset + index + (k + 1) := by omega
        rw [e]; exact hk _ (by omega)⟩
    have e : offset + (index + 1) = offset + index + 1 := by omega
    rw [e] at ih
    simp only [hb', ↓reduceIte]
    simpa [hne, latin1, byteAt] using ih

private theorem loop_ok {data : ByteArray} {offset : Nat} :
    ∀ {fuel index chars s}, data.size - (offset + index) ≤ fuel →
      cstring.loop data offset index chars = .ok s →
      ∃ n, TerminatedAt data (offset + index) n ∧
        s = String.ofList (chars.reverse ++ latin1 data (offset + index) n)
  | 0, index, chars, s, hf, h => by
    rw [cstring.loop] at h
    rw [ite_eq_left (by omega)] at h
    cases h
  | fuel + 1, index, chars, s, hf, h => by
    rw [cstring.loop] at h
    by_cases hb : offset + index ≥ data.size
    · rw [ite_eq_left hb] at h; cases h
    · rw [ite_eq_right hb] at h
      by_cases hz : byteAt data (offset + index) = 0
      · simp only [byteAt] at hz
        simp only [hz, ↓reduceIte] at h
        cases h
        exact ⟨0, ⟨by omega, by simpa using hz, by simp⟩, by simp [latin1]⟩
      · simp only [byteAt] at hz
        simp only [hz, ↓reduceIte] at h
        have ⟨n, ⟨hb', hz', hk⟩, hs⟩ := loop_ok (fuel := fuel) (by omega) h
        have e : offset + (index + 1) = offset + index + 1 := by omega
        rw [e] at hb' hz' hk hs
        refine ⟨n + 1, ⟨by omega, ?_, ?_⟩, ?_⟩
        · have e' : offset + index + (n + 1) = offset + index + 1 + n := by omega
          rw [e']; exact hz'
        · intro k hlt
          cases k with
          | zero => simpa [byteAt] using hz
          | succ k =>
            have e' : offset + index + (k + 1) = offset + index + 1 + k := by omega
            rw [e']; exact hk k (by omega)
        · rw [hs]; simp [latin1, byteAt]

/-- `cstring` succeeds exactly when a NUL follows `offset`, and returns the bytes before the first one. -/
theorem cstring_ok_iff {data : ByteArray} {offset : Nat} {s : String} :
    cstring data offset = .ok s ↔
      ∃ n, TerminatedAt data offset n ∧ s = String.ofList (latin1 data offset n) := by
  constructor
  · intro h
    simp only [cstring] at h
    have := loop_ok (fuel := data.size) (index := 0) (by omega) h
    simpa using this
  · rintro ⟨n, ht, rfl⟩
    simp only [cstring]
    have := loop_of_terminated (index := 0) (chars := []) (n := n) (offset := offset) (data := data) ht
    simpa using this

/-- The length of a decoded string is the distance to the terminating NUL. -/
theorem cstring_length {data : ByteArray} {offset n : Nat} (h : TerminatedAt data offset n) :
    cstring data offset = .ok (String.ofList (latin1 data offset n)) ∧
      (String.ofList (latin1 data offset n)).length = n :=
  ⟨cstring_ok_iff.mpr ⟨n, h, rfl⟩, by simp [latin1_length]⟩

/-- Without a NUL at or after `offset`, `cstring` reports an unterminated string. -/
theorem cstring_unterminated {data : ByteArray} {offset : Nat}
    (h : ∀ i, offset ≤ i → i < data.size → byteAt data i ≠ 0) :
    cstring data offset = .error "unterminated string" := by
  have aux : ∀ fuel index chars, data.size - (offset + index) ≤ fuel →
      cstring.loop data offset index chars = .error "unterminated string" := by
    intro fuel
    induction fuel with
    | zero =>
      intro index chars hf
      rw [cstring.loop, ite_eq_left (by omega)]
    | succ fuel ih =>
      intro index chars hf
      rw [cstring.loop]
      by_cases hb : offset + index ≥ data.size
      · rw [ite_eq_left hb]
      · rw [ite_eq_right hb]
        have hne := h (offset + index) (by omega) (by omega)
        simp only [byteAt] at hne
        simp only [hne, ↓reduceIte]
        exact ih _ _ (by omega)
  exact aux _ 0 [] (Nat.le_refl _)

/-- The terminator position is unique, so `cstring` is deterministic in the first NUL. -/
theorem terminatedAt_unique {data : ByteArray} {offset m n : Nat}
    (hm : TerminatedAt data offset m) (hn : TerminatedAt data offset n) : m = n := by
  have ⟨_, zm, km⟩ := hm
  have ⟨_, zn, kn⟩ := hn
  rcases Nat.lt_trichotomy m n with h | h | h
  · exact absurd zm (kn m h)
  · exact h
  · exact absurd zn (km n h)

end Bap.Proofs.IO
