import Bap.Checkpoint.BinProt

namespace Bap.Proofs.Checkpoint

open Bap.Checkpoint.BinProt

abbrev byteAt (data : ByteArray) (i : Nat) : Nat := (data.get! i).toNat

theorem bind_ok_iff {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {v : β} :
    (x >>= f) = .ok v ↔ ∃ a, x = .ok a ∧ f a = .ok v := by
  cases x with
  | error e => simp [bind, Except.bind]
  | ok a => simp [bind, Except.bind]

private theorem get!_eq_getElem {data : ByteArray} {i : Nat} (h : i < data.size) : data.get! i = data[i] := by
  cases data with
  | mk bytes =>
    show bytes[i]! = bytes[i]
    exact getElem!_pos bytes i h

/-! ## Primitive decoders: soundness -/

/-- `byte` succeeds exactly in range, returns that byte and advances one position. -/
theorem byte_of_lt {reader : Reader} (h : reader.offset < reader.data.size) :
    byte reader = .ok (byteAt reader.data reader.offset, ⟨reader.data, reader.offset + 1⟩) := by
  have hg : IO.Reader.get8 reader.data reader.offset = .ok (byteAt reader.data reader.offset) := by
    simp only [IO.Reader.get8]
    rw [ite_eq_right (by omega)]
  simp only [byte, hg]
  rfl

theorem byte_of_ge {reader : Reader} (h : reader.data.size ≤ reader.offset) :
    byte reader = .error s!"read past end of input at {reader.offset}" := by
  have hg : IO.Reader.get8 reader.data reader.offset = .error s!"read past end of input at {reader.offset}" := by
    simp only [IO.Reader.get8]
    rw [ite_eq_left h]
  simp only [byte, hg]
  rfl

theorem bytes_of_le {reader : Reader} {size : Nat} (h : reader.offset + size ≤ reader.data.size) :
    bytes reader size =
      .ok (reader.data.extract reader.offset (reader.offset + size), ⟨reader.data, reader.offset + size⟩) := by
  have hg : IO.Reader.slice reader.data reader.offset size =
      .ok (reader.data.extract reader.offset (reader.offset + size)) := by
    simp only [IO.Reader.slice]
    rw [ite_eq_right (by omega)]
  simp only [bytes, hg]
  rfl

theorem bytes_of_gt {reader : Reader} {size : Nat} (h : reader.data.size < reader.offset + size) :
    bytes reader size =
      .error s!"slice past end of input at {reader.offset} with size {size}" := by
  have hg : IO.Reader.slice reader.data reader.offset size =
      .error s!"slice past end of input at {reader.offset} with size {size}" := by
    simp only [IO.Reader.slice]
    rw [ite_eq_left h]
  simp only [bytes, hg]
  rfl

/-- Success keeps the same input, moves forward, and ends inside the input. -/
def Sound (decode : Reader → Except String (α × Reader)) : Prop :=
  ∀ reader value next, decode reader = .ok (value, next) →
    next.data = reader.data ∧ reader.offset ≤ next.offset ∧ next.offset ≤ reader.data.size

theorem byte_sound : Sound byte := by
  intro r v n h
  by_cases hb : r.offset < r.data.size
  · rw [byte_of_lt hb] at h
    cases h
    exact ⟨rfl, by simp, by simp; omega⟩
  · rw [byte_of_ge (by omega)] at h
    cases h

theorem bytes_sound (size : Nat) : Sound (bytes · size) := by
  intro r v n h
  simp only at h
  by_cases hb : r.offset + size ≤ r.data.size
  · rw [bytes_of_le hb] at h
    cases h
    exact ⟨rfl, by simp, by simpa using hb⟩
  · rw [bytes_of_gt (by omega)] at h
    cases h

theorem Sound.trans {r1 r2 r3 : Reader}
    (h1 : r2.data = r1.data ∧ r1.offset ≤ r2.offset ∧ r2.offset ≤ r1.data.size)
    (h2 : r3.data = r2.data ∧ r2.offset ≤ r3.offset ∧ r3.offset ≤ r2.data.size) :
    r3.data = r1.data ∧ r1.offset ≤ r3.offset ∧ r3.offset ≤ r1.data.size := by
  have ⟨a, b, c⟩ := h1
  have ⟨d, e, f⟩ := h2
  rw [a] at f
  exact ⟨d.trans a, by omega, f⟩

/-! ## Little-endian values -/

/-- Least-significant-byte-first value of the `n` bytes at `offset`. -/
def littleValue (data : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => littleValue data offset n + byteAt data (offset + n) * 256 ^ n

theorem littleValue_lt (data : ByteArray) (offset : Nat) :
    ∀ n, littleValue data offset n < 256 ^ n
  | 0 => by simp [littleValue]
  | n + 1 => by
    have ih := littleValue_lt data offset n
    have hb : byteAt data (offset + n) < 256 := (data.get! _).toNat_lt
    simp only [littleValue, Nat.pow_succ]
    have : byteAt data (offset + n) * 256 ^ n ≤ 255 * 256 ^ n := Nat.mul_le_mul_right _ (by omega)
    omega

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

private theorem getElem!_eq_get! {data : ByteArray} {i : Nat} (h : i < data.size) : data[i]! = data.get! i := by
  rw [get!_eq_getElem h]
  exact getElem!_pos data i h

/-- The value of the little-endian prefix of `data`, in the fold the decoders use. -/
def foldedValue (data : ByteArray) (n : Nat) : Nat :=
  (List.range n).foldl (init := 0) fun value index => value + data[index]!.toNat * 256 ^ index

theorem foldedValue_succ (data : ByteArray) (n : Nat) :
    foldedValue data (n + 1) = foldedValue data n + data[n]!.toNat * 256 ^ n := by
  simp [foldedValue, List.range_succ, List.foldl_append]

theorem foldedValue_extract {data : ByteArray} {offset n : Nat} (h : offset + n ≤ data.size) :
    ∀ k, k ≤ n → foldedValue (data.extract offset (offset + n)) k = littleValue data offset k
  | 0, _ => rfl
  | k + 1, hk => by
    rw [foldedValue_succ, foldedValue_extract h k (by omega), littleValue]
    have hsize : k < (data.extract offset (offset + n)).size := by
      simp only [ByteArray.size_extract]; omega
    rw [getElem!_eq_get! hsize, get!_eq_getElem hsize, ByteArray.getElem_extract,
      ← get!_eq_getElem (by omega)]

/-- `packedNat` is the little-endian value of the whole array. -/
theorem packedNat_eq_littleValue (data : ByteArray) :
    packedNat data = littleValue data 0 data.size := by
  have h := foldedValue_extract (data := data) (offset := 0) (n := data.size) (by omega) data.size (Nat.le_refl _)
  simp only [Nat.zero_add, ByteArray.extract_zero_size] at h
  exact h

theorem packedNat_lt (data : ByteArray) : packedNat data < 256 ^ data.size := by
  rw [packedNat_eq_littleValue]
  exact littleValue_lt ..

/-! ## int -/

theorem int_small {data : ByteArray} {offset : Nat} (hb : offset < data.size)
    (ht : byteAt data offset < 128) :
    int ⟨data, offset⟩ = .ok (byteAt data offset, ⟨data, offset + 1⟩) := by
  simp only [int, byte_of_lt (reader := ⟨data, offset⟩) hb, bind, Except.bind]
  split
  · omega
  · omega
  · omega
  · omega
  · simp only [ht, ↓reduceIte]

theorem int_two {data : ByteArray} {offset : Nat} (hb : offset + 3 ≤ data.size)
    (ht : byteAt data offset = 0xfe) :
    int ⟨data, offset⟩ = .ok (littleValue data (offset + 1) 2, ⟨data, offset + 3⟩) := by
  have hk := foldedValue_extract (data := data) (offset := offset + 1) (n := 2) (by omega) 2 (by omega)
  have hv : ∀ x : ByteArray, foldedValue x 2 = x[0]!.toNat + x[1]!.toNat * 256 := by
    intro x
    simp [foldedValue, List.range_succ]
  rw [hv] at hk
  simp only [int, byte_of_lt (reader := ⟨data, offset⟩) (show offset < data.size by omega), ht, bind, Except.bind,
    bytes_of_le (reader := ⟨data, offset + 1⟩) (size := 2) (by simpa using (by omega : offset + 1 + 2 ≤ data.size))]
  rw [hk]

theorem int_four {data : ByteArray} {offset : Nat} (hb : offset + 5 ≤ data.size)
    (ht : byteAt data offset = 0xfd) :
    int ⟨data, offset⟩ = .ok (littleValue data (offset + 1) 4, ⟨data, offset + 5⟩) := by
  have hk := foldedValue_extract (data := data) (offset := offset + 1) (n := 4) (by omega) 4 (by omega)
  simp only [int, byte_of_lt (reader := ⟨data, offset⟩) (show offset < data.size by omega), ht, bind, Except.bind,
    bytes_of_le (reader := ⟨data, offset + 1⟩) (size := 4) (by simpa using (by omega : offset + 1 + 4 ≤ data.size))]
  rw [← hk]
  rfl

theorem int_eight {data : ByteArray} {offset : Nat} (hb : offset + 9 ≤ data.size)
    (ht : byteAt data offset = 0xfc) :
    int ⟨data, offset⟩ = .ok (littleValue data (offset + 1) 8, ⟨data, offset + 9⟩) := by
  have hk := foldedValue_extract (data := data) (offset := offset + 1) (n := 8) (by omega) 8 (by omega)
  simp only [int, byte_of_lt (reader := ⟨data, offset⟩) (show offset < data.size by omega), ht, bind, Except.bind,
    bytes_of_le (reader := ⟨data, offset + 1⟩) (size := 8) (by simpa using (by omega : offset + 1 + 8 ≤ data.size))]
  rw [← hk]
  rfl

/-- The whole behaviour of `int`: every accepted input is a short or tagged little-endian integer. -/
theorem int_ok_iff {data : ByteArray} {offset value : Nat} {next : Reader} :
    int ⟨data, offset⟩ = .ok (value, next) ↔
      offset < data.size ∧ next.data = data ∧
      ((byteAt data offset < 128 ∧ value = byteAt data offset ∧ next.offset = offset + 1) ∨
       (byteAt data offset = 0xfe ∧ offset + 3 ≤ data.size ∧ value = littleValue data (offset + 1) 2 ∧
          next.offset = offset + 3) ∨
       (byteAt data offset = 0xfd ∧ offset + 5 ≤ data.size ∧ value = littleValue data (offset + 1) 4 ∧
          next.offset = offset + 5) ∨
       (byteAt data offset = 0xfc ∧ offset + 9 ≤ data.size ∧ value = littleValue data (offset + 1) 8 ∧
          next.offset = offset + 9)) := by
  cases next with
  | mk ndata noffset =>
  constructor
  · intro h
    by_cases hb : offset < data.size
    · refine ⟨hb, ?_⟩
      by_cases ht : byteAt data offset < 128
      · rw [int_small hb ht] at h
        cases h
        exact ⟨rfl, .inl ⟨ht, rfl, rfl⟩⟩
      by_cases h254 : byteAt data offset = 0xfe
      · by_cases hw : offset + 3 ≤ data.size
        · rw [int_two hw h254] at h
          cases h
          exact ⟨rfl, .inr (.inl ⟨h254, hw, rfl, rfl⟩)⟩
        · simp only [int, byte_of_lt (reader := ⟨data, offset⟩) hb, h254, bind, Except.bind,
            bytes_of_gt (reader := ⟨data, offset + 1⟩) (size := 2) (by simp; omega)] at h
          cases h
      by_cases h253 : byteAt data offset = 0xfd
      · by_cases hw : offset + 5 ≤ data.size
        · rw [int_four hw h253] at h
          cases h
          exact ⟨rfl, .inr (.inr (.inl ⟨h253, hw, rfl, rfl⟩))⟩
        · simp only [int, byte_of_lt (reader := ⟨data, offset⟩) hb, h253, bind, Except.bind,
            bytes_of_gt (reader := ⟨data, offset + 1⟩) (size := 4) (by simp; omega)] at h
          cases h
      by_cases h252 : byteAt data offset = 0xfc
      · by_cases hw : offset + 9 ≤ data.size
        · rw [int_eight hw h252] at h
          cases h
          exact ⟨rfl, .inr (.inr (.inr ⟨h252, hw, rfl, rfl⟩))⟩
        · simp only [int, byte_of_lt (reader := ⟨data, offset⟩) hb, h252, bind, Except.bind,
            bytes_of_gt (reader := ⟨data, offset + 1⟩) (size := 8) (by simp; omega)] at h
          cases h
      · exfalso
        simp only [int, byte_of_lt (reader := ⟨data, offset⟩) hb, bind, Except.bind] at h
        split at h
        · omega
        · omega
        · omega
        · cases h
        · rw [ite_eq_right ht] at h
          cases h
    · simp only [int, byte_of_ge (reader := ⟨data, offset⟩) (by simpa using (by omega : data.size ≤ offset)),
        bind, Except.bind] at h
      cases h
  · rintro ⟨hb, hd, hcases⟩
    simp only at hd
    subst hd
    rcases hcases with ⟨ht, rfl, ho⟩ | ⟨ht, hw, rfl, ho⟩ | ⟨ht, hw, rfl, ho⟩ | ⟨ht, hw, rfl, ho⟩
    · simp only at ho; subst ho; exact int_small hb ht
    · simp only at ho; subst ho; exact int_two hw ht
    · simp only at ho; subst ho; exact int_four hw ht
    · simp only at ho; subst ho; exact int_eight hw ht

/-- Accepted integers always fit in 64 bits. -/
theorem int_lt {reader next : Reader} {value : Nat} (h : int reader = .ok (value, next)) :
    value < 2 ^ 64 := by
  cases reader
  have ⟨_, _, hc⟩ := int_ok_iff.mp h
  rcases hc with ⟨_, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩ | ⟨_, _, rfl, _⟩
  · omega
  · have := littleValue_lt ‹ByteArray› (‹Nat› + 1) 2; omega
  · have := littleValue_lt ‹ByteArray› (‹Nat› + 1) 4; omega
  · have := littleValue_lt ‹ByteArray› (‹Nat› + 1) 8; omega

theorem int_sound : Sound int := by
  intro r v n h
  cases r
  have ⟨hb, hd, hc⟩ := int_ok_iff.mp h
  refine ⟨hd, ?_⟩
  rcases hc with ⟨_, _, ho⟩ | ⟨_, hw, _, ho⟩ | ⟨_, hw, _, ho⟩ | ⟨_, hw, _, ho⟩ <;>
    (simp only; omega)

/-- `0xff`-tagged (negative) integers and reserved tags are always rejected. -/
theorem int_rejects_tag {data : ByteArray} {offset : Nat} (ht : 128 ≤ byteAt data offset)
    (h254 : byteAt data offset ≠ 0xfe) (h253 : byteAt data offset ≠ 0xfd) (h252 : byteAt data offset ≠ 0xfc) :
    (int ⟨data, offset⟩).isOk = false := by
  cases hi : int ⟨data, offset⟩ with
  | error e => rfl
  | ok v =>
    have ⟨_, _, hc⟩ := int_ok_iff.mp hi
    rcases hc with ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ | ⟨h, _⟩ <;> omega

/-! ## Composite decoders: soundness -/

theorem bool_ok_iff {reader next : Reader} {value : Bool} :
    bool reader = .ok (value, next) ↔
      reader.offset < reader.data.size ∧ next = ⟨reader.data, reader.offset + 1⟩ ∧
        byteAt reader.data reader.offset = (if value then 1 else 0) := by
  by_cases hb : reader.offset < reader.data.size
  · simp only [Bap.Checkpoint.BinProt.bool, byte_of_lt hb, bind, Except.bind]
    split
    · rename_i ht
      rw [ht]; cases value <;> simp [hb, eq_comm]
    · rename_i ht
      rw [ht]; cases value <;> simp [hb, eq_comm]
    · rename_i h0 h1
      constructor
      · intro h; cases h
      · rintro ⟨_, _, ht⟩
        cases value
        · exact absurd (by simpa using ht) h0
        · exact absurd (by simpa using ht) h1
  · simp only [Bap.Checkpoint.BinProt.bool, byte_of_ge (by omega : reader.data.size ≤ reader.offset), bind, Except.bind]
    constructor
    · intro h; cases h
    · rintro ⟨h, _⟩; exact absurd h hb

theorem bool_sound : Sound bool := by
  intro r v n h
  have ⟨hb, hn, _⟩ := bool_ok_iff.mp h
  subst hn
  exact ⟨rfl, by simp, by simp; omega⟩

theorem option_rejects_tag {α : Type} {decode : Reader → Except String (α × Reader)} {reader : Reader}
    (hb : reader.offset < reader.data.size) (ht : 1 < byteAt reader.data reader.offset) :
    (option reader decode).isOk = false := by
  simp only [option, byte_of_lt hb, bind, Except.bind]
  split
  · omega
  · omega
  · rfl

/-- Decoders fail on an exhausted input, whatever the claimed payload. -/
theorem decoders_reject_exhausted {reader : Reader} (h : reader.data.size ≤ reader.offset) :
    (byte reader).isOk = false ∧ (int reader).isOk = false ∧ (string reader).isOk = false ∧
      (Bap.Checkpoint.BinProt.bool reader).isOk = false := by
  simp only [Bap.Checkpoint.BinProt.bool, int, string, byte_of_ge h, bind, Except.bind]
  simp [Except.isOk, Except.toBool]

theorem string_sound : Sound string := by
  intro r v n h
  simp only [string, bind_ok_iff] at h
  rcases h with ⟨⟨size, r1⟩, h1, h2⟩
  exact Sound.trans (int_sound _ _ _ h1) (bytes_sound size _ _ _ h2)

theorem word_sound : Sound word := string_sound

theorem option_sound {α : Type} {decode : Reader → Except String (α × Reader)} (hd : Sound decode) :
    Sound (option · decode) := by
  intro r v n h
  simp only [option, bind_ok_iff] at h
  rcases h with ⟨⟨tag, r1⟩, h1, h2⟩
  have s1 := byte_sound _ _ _ h1
  dsimp only at h2
  split at h2
  · cases h2; exact s1
  · simp only [bind_ok_iff] at h2
    rcases h2 with ⟨⟨x, r2⟩, h3, h4⟩
    cases h4
    exact Sound.trans s1 (hd _ _ _ h3)
  · cases h2

theorem list_loop_sound {α : Type} {decode : Reader → Except String (α × Reader)} (hd : Sound decode) :
    ∀ {remaining : Nat} {reader : Reader} {acc xs : List α} {next : Reader},
      reader.offset ≤ reader.data.size →
      list.loop decode remaining reader acc = .ok (xs, next) →
      (next.data = reader.data ∧ reader.offset ≤ next.offset ∧ next.offset ≤ reader.data.size) ∧
        ∃ ys, xs = acc.reverse ++ ys ∧ ys.length = remaining
  | 0, reader, acc, xs, next, hb, h => by
    simp only [list.loop] at h
    cases h
    exact ⟨⟨rfl, Nat.le_refl _, hb⟩, [], by simp, rfl⟩
  | n + 1, reader, acc, xs, next, hb, h => by
    simp only [list.loop, bind_ok_iff] at h
    rcases h with ⟨⟨x, r1⟩, h1, h2⟩
    have s1 := hd _ _ _ h1
    have hb1 : r1.offset ≤ r1.data.size := by rw [s1.1]; exact s1.2.2
    have ⟨s2, ys, hxs, hlen⟩ := list_loop_sound hd hb1 h2
    refine ⟨Sound.trans s1 s2, x :: ys, ?_, by simp [hlen]⟩
    simpa using hxs

theorem list_sound {α : Type} {decode : Reader → Except String (α × Reader)} (hd : Sound decode) :
    Sound (list · decode) := by
  intro r v n h
  simp only [list, bind_ok_iff] at h
  rcases h with ⟨⟨count, r1⟩, h1, h2⟩
  have s1 := int_sound _ _ _ h1
  have hb1 : r1.offset ≤ r1.data.size := by rw [s1.1]; exact s1.2.2
  exact Sound.trans s1 (list_loop_sound hd hb1 h2).1

/-- A decoded list has exactly as many elements as its count prefix announces. -/
theorem list_length {α : Type} {decode : Reader → Except String (α × Reader)} (hd : Sound decode)
    {reader next : Reader} {xs : List α} (h : list reader decode = .ok (xs, next)) :
    ∃ r1, int reader = .ok (xs.length, r1) := by
  simp only [list, bind_ok_iff] at h
  rcases h with ⟨⟨count, r1⟩, h1, h2⟩
  have s1 := int_sound _ _ _ h1
  have hb1 : r1.offset ≤ r1.data.size := by rw [s1.1]; exact s1.2.2
  have ⟨_, ys, hxs, hlen⟩ := list_loop_sound hd hb1 h2
  subst hxs
  simp only [hlen]
  exact ⟨r1, h1⟩

theorem valuePair_sound : Sound valuePair := by
  intro r v n h
  simp only [valuePair, bind_ok_iff] at h
  rcases h with ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, x, _, y, _, h3⟩
  cases h3
  exact Sound.trans (word_sound _ _ _ h1) (word_sound _ _ _ h2)

theorem descriptor_sound : Sound descriptor := by
  intro r v n h
  simp only [descriptor, bind_ok_iff] at h
  rcases h with ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, ⟨c, r3⟩, h3, h4⟩
  cases h4
  exact Sound.trans (string_sound _ _ _ h1) (Sound.trans (int_sound _ _ _ h2) (int_sound _ _ _ h3))

/-- A decoded area is allocated exactly when it carries a width; unallocated areas have no fill. -/
theorem area_shape {reader next : Reader} {value : Area} (h : area reader = .ok (value, next)) :
    (value.allocated = true ↔ value.width.isSome = true) ∧
      (value.allocated = false → value.fill = none) := by
  simp only [area, bind_ok_iff] at h
  rcases h with ⟨⟨a, r1⟩, _, ⟨b, r2⟩, _, ⟨c, r3⟩, _, ⟨d, r4⟩, _, ⟨kind, r5⟩, _, h⟩
  dsimp only at h
  split at h
  · cases h; simp
  · simp only [bind_ok_iff] at h
    rcases h with ⟨⟨w, r6⟩, _, ⟨f, r7⟩, _, h⟩
    cases h; simp
  · cases h

theorem area_sound : Sound area := by
  intro r v n h
  simp only [area, bind_ok_iff] at h
  rcases h with ⟨⟨a, r1⟩, h1, ⟨b, r2⟩, h2, ⟨c, r3⟩, h3, ⟨d, r4⟩, h4, ⟨kind, r5⟩, h5, h⟩
  have s := Sound.trans (word_sound _ _ _ h1) (Sound.trans (word_sound _ _ _ h2)
    (Sound.trans (bool_sound _ _ _ h3) (Sound.trans (bool_sound _ _ _ h4) (byte_sound _ _ _ h5))))
  dsimp only at h
  split at h
  · cases h; exact s
  · simp only [bind_ok_iff] at h
    rcases h with ⟨⟨w, r6⟩, h6, ⟨f, r7⟩, h7, h⟩
    cases h
    exact Sound.trans s (Sound.trans (int_sound _ _ _ h6) (option_sound word_sound _ _ _ h7))
  · cases h

/-- A decoded prefix always describes one memory, and records where the value table starts. -/
theorem memoryPrefix_ok {reader next : Reader} {value : MemoryPrefix}
    (h : memoryPrefix reader = .ok (value, next)) :
    value.memories = 1 ∧ value.valuesOffset = next.offset ∧
      next.data = reader.data ∧ reader.offset ≤ next.offset ∧ next.offset ≤ reader.data.size := by
  simp only [memoryPrefix, bind_ok_iff] at h
  rcases h with ⟨⟨a, r1⟩, h1, ⟨m, r2⟩, h2, h⟩
  have hm : m = 1 := by
    by_cases hm : m = 1
    · exact hm
    · simp [hm, bind, Except.bind] at h
  subst hm
  simp only [bne_self_eq_false, ↓reduceIte, Bool.false_eq_true, bind_ok_iff] at h
  rcases h with ⟨⟨d, r3⟩, h3, ⟨l, r4⟩, h4, ⟨v, r5⟩, h5, h6⟩
  cases h6
  have s := Sound.trans (descriptor_sound _ _ _ h1) (Sound.trans (int_sound _ _ _ h2)
    (Sound.trans (descriptor_sound _ _ _ h3) (Sound.trans (list_sound area_sound _ _ _ h4)
      (int_sound _ _ _ h5))))
  exact ⟨rfl, rfl, s⟩

/-! ## Encoders and roundtrips

The production module only decodes, so these encoders state the wire format the decoders accept. -/

/-- `bytes` occur in `data` starting at `position`. -/
def Occurs (data : ByteArray) : Nat → List UInt8 → Prop
  | _, [] => True
  | position, b :: rest => position < data.size ∧ data.get! position = b ∧ Occurs data (position + 1) rest

theorem occurs_append {data : ByteArray} :
    ∀ {left right : List UInt8} {position : Nat},
      Occurs data position (left ++ right) ↔
        Occurs data position left ∧ Occurs data (position + left.length) right
  | [], _, _ => by simp [Occurs]
  | b :: rest, right, position => by
    have e : position + (b :: rest).length = position + 1 + rest.length := by simp; omega
    simp only [List.cons_append, Occurs, occurs_append (left := rest), e, and_assoc]

theorem occurs_bound {data : ByteArray} :
    ∀ {bytes : List UInt8} {position : Nat}, bytes ≠ [] → Occurs data position bytes →
      position + bytes.length ≤ data.size
  | [], _, h, _ => absurd rfl h
  | [_], _, _, h => by simp; exact h.1
  | b :: c :: rest, position, _, h => by
    have ih := occurs_bound (bytes := c :: rest) (by simp) h.2.2
    simp only [List.length_cons] at ih ⊢
    omega

theorem occurs_get {data : ByteArray} :
    ∀ {bytes : List UInt8} {position i : Nat} (h : i < bytes.length), Occurs data position bytes →
      data.get! (position + i) = bytes[i]
  | b :: _, _, 0, _, h => by simpa using h.2.1
  | _ :: rest, position, i + 1, hi, h => by
    have e : position + (i + 1) = position + 1 + i := by omega
    rw [e, occurs_get (bytes := rest) (by simpa using hi) h.2.2]
    rfl

/-- Least-significant-byte-first digits of `value`. -/
def leBytes (value : Nat) : Nat → List UInt8
  | 0 => []
  | n + 1 => UInt8.ofNat value :: leBytes (value / 256) n

theorem leBytes_length : ∀ value n, (leBytes value n).length = n
  | _, 0 => rfl
  | value, n + 1 => by simp [leBytes, leBytes_length]

theorem littleValue_leBytes {data : ByteArray} :
    ∀ {n value position}, Occurs data position (leBytes value n) →
      littleValue data position n = value % 256 ^ n
  | 0, _, _, _ => by simp [littleValue, Nat.mod_one]
  | n + 1, value, position, ⟨_, hb, ht⟩ => by
    have hu : (UInt8.ofNat value).toNat = value % 256 := UInt8.toNat_ofNat'
    have hp : 256 ^ (n + 1) = 256 * 256 ^ n := by rw [Nat.pow_succ, Nat.mul_comm]
    rw [littleValue_cons, littleValue_leBytes ht, byteAt, hb, hu, hp, Nat.mod_mul]

/-- The canonical (shortest) wire encoding of a natural number. -/
def encodeInt (value : Nat) : List UInt8 :=
  if value < 128 then [UInt8.ofNat value]
  else if value < 2 ^ 16 then 0xfe :: leBytes value 2
  else if value < 2 ^ 32 then 0xfd :: leBytes value 4
  else 0xfc :: leBytes value 8

theorem encodeInt_ne_nil (value : Nat) : encodeInt value ≠ [] := by
  unfold encodeInt
  repeat' split
  all_goals simp

/-- An encoder and decoder agree on values satisfying `valid`, at any position of any input. -/
def Codec {α : Type} (encode : α → List UInt8) (decode : Reader → Except String (α × Reader))
    (valid : α → Prop) : Prop :=
  ∀ x, valid x → ∀ data position, Occurs data position (encode x) →
    decode ⟨data, position⟩ = .ok (x, ⟨data, position + (encode x).length⟩)

/-- `int` inverts `encodeInt` for every 64-bit value. -/
theorem int_codec : Codec encodeInt int (· < 2 ^ 64) := by
  intro value hv data position h
  have hb := occurs_bound (encodeInt_ne_nil value) h
  unfold encodeInt at h hb ⊢
  by_cases h1 : value < 128
  · simp only [h1, ↓reduceIte, Occurs, List.length_cons, List.length_nil] at h hb ⊢
    have hv' : byteAt data position = value := by
      rw [byteAt, h.2.1, UInt8.toNat_ofNat', Nat.mod_eq_of_lt (by omega)]
    rw [int_small (by omega) (by omega), hv']
  by_cases h2 : value < 2 ^ 16
  · simp only [h1, h2, ↓reduceIte, Occurs, List.length_cons, leBytes_length] at h hb ⊢
    rw [int_two (by omega) (by rw [byteAt, h.2.1]; rfl), littleValue_leBytes h.2.2,
      Nat.mod_eq_of_lt (by omega)]
  by_cases h3 : value < 2 ^ 32
  · simp only [h1, h2, h3, ↓reduceIte, Occurs, List.length_cons, leBytes_length] at h hb ⊢
    rw [int_four (by omega) (by rw [byteAt, h.2.1]; rfl), littleValue_leBytes h.2.2,
      Nat.mod_eq_of_lt (by omega)]
  · simp only [h1, h2, h3, ↓reduceIte, Occurs, List.length_cons, leBytes_length] at h hb ⊢
    rw [int_eight (by omega) (by rw [byteAt, h.2.1]; rfl), littleValue_leBytes h.2.2,
      Nat.mod_eq_of_lt (by omega)]

theorem extract_of_occurs {data value : ByteArray} {position : Nat}
    (h : Occurs data position value.data.toList) (hb : position + value.size ≤ data.size) :
    data.extract position (position + value.size) = value := by
  have hs : value.data.size = value.size := rfl
  have hd : data.data.size = data.size := rfl
  have e : (data.extract position (position + value.size)).data = value.data := by
    apply Array.ext
    · simp only [ByteArray.data_extract, Array.size_extract]; omega
    · intro i h1 h2
      have hi : i < value.data.toList.length := by simpa using h2
      have := occurs_get hi h
      rw [get!_eq_getElem (by omega)] at this
      simpa [ByteArray.getElem_eq_getElem_data] using this
  exact congrArg ByteArray.mk e

/-- Length-prefixed bytes. -/
def encodeString (value : ByteArray) : List UInt8 :=
  encodeInt value.size ++ value.data.toList

theorem encodeString_length (value : ByteArray) :
    (encodeString value).length = (encodeInt value.size).length + value.size := by
  rw [encodeString, List.length_append, Array.length_toList]
  rfl

theorem encodeString_ne_nil (value : ByteArray) : encodeString value ≠ [] := fun e =>
  encodeInt_ne_nil _ (List.append_eq_nil_iff.mp e).1

/-- `string` inverts `encodeString`. -/
theorem string_codec : Codec encodeString string (fun value => value.size < 2 ^ 64) := by
  intro value hv data position h
  have hb := occurs_bound (encodeString_ne_nil value) h
  rw [encodeString_length] at hb ⊢
  have ⟨h1, h2⟩ := occurs_append.mp h
  simp only [string, int_codec _ hv _ _ h1, bind, Except.bind,
    bytes_of_le (reader := ⟨data, position + (encodeInt value.size).length⟩) (size := value.size)
      (by simpa using (by omega : position + (encodeInt value.size).length + value.size ≤ data.size))]
  rw [extract_of_occurs h2 (by omega), Nat.add_assoc]

theorem word_codec : Codec encodeString word (fun value => value.size < 2 ^ 64) := string_codec

/-- `bool` inverts the one-byte boolean encoding. -/
theorem bool_codec : Codec (fun value : Bool => [if value then (1 : UInt8) else 0]) bool (fun _ => True) := by
  intro value _ data position h
  simp only [Occurs] at h
  refine bool_ok_iff.mpr ⟨h.1, by simp, ?_⟩
  rw [byteAt, h.2.1]
  cases value <;> rfl

def encodeOption {α : Type} (encode : α → List UInt8) : Option α → List UInt8
  | none => [0]
  | some x => 1 :: encode x

/-- `option` inverts `encodeOption`, given a codec for the payload. -/
theorem option_codec {α : Type} {encode : α → List UInt8} {decode : Reader → Except String (α × Reader)}
    {valid : α → Prop} (hc : Codec encode decode valid) :
    Codec (encodeOption encode) (option · decode) (fun value => ∀ x, value = some x → valid x) := by
  intro value hv data position h
  cases value with
  | none =>
    simp only [encodeOption, Occurs] at h
    simp only [option, byte_of_lt (reader := ⟨data, position⟩) h.1, bind, Except.bind, byteAt, h.2.1]
    rfl
  | some x =>
    simp only [encodeOption, Occurs] at h
    have hy : (data.get! position).toNat = 1 := by rw [h.2.1]; rfl
    simp only [option, byte_of_lt (reader := ⟨data, position⟩) h.1, bind, Except.bind, hy]
    rw [hc x (hv x rfl) _ _ h.2.2]
    simp only [encodeOption, List.length_cons, Nat.add_assoc, Nat.add_comm 1]

def encodeList {α : Type} (encode : α → List UInt8) (values : List α) : List UInt8 :=
  encodeInt values.length ++ values.flatMap encode

theorem list_loop_codec {α : Type} {encode : α → List UInt8} {decode : Reader → Except String (α × Reader)}
    {valid : α → Prop} (hc : Codec encode decode valid) {data : ByteArray} :
    ∀ (values : List α) {position : Nat} (acc : List α), (∀ x ∈ values, valid x) →
      Occurs data position (values.flatMap encode) →
      list.loop decode values.length ⟨data, position⟩ acc =
        .ok (acc.reverse ++ values, ⟨data, position + (values.flatMap encode).length⟩)
  | [], position, acc, _, _ => by simp [list.loop]
  | x :: rest, position, acc, hv, h => by
    rw [List.flatMap_cons] at h
    have ⟨h1, h2⟩ := occurs_append.mp h
    simp only [List.length_cons, list.loop, hc x (hv x (by simp)) _ _ h1, bind, Except.bind]
    rw [list_loop_codec hc rest (x :: acc) (fun y hy => hv y (by simp [hy])) h2]
    simp [List.flatMap_cons, Nat.add_assoc]

/-- `list` inverts `encodeList`, given a codec for the elements. -/
theorem list_codec {α : Type} {encode : α → List UInt8} {decode : Reader → Except String (α × Reader)}
    {valid : α → Prop} (hc : Codec encode decode valid) :
    Codec (encodeList encode) (list · decode)
      (fun values => values.length < 2 ^ 64 ∧ ∀ x ∈ values, valid x) := by
  intro values hv data position h
  have ⟨h1, h2⟩ := occurs_append.mp h
  simp only [list, int_codec _ hv.1 _ _ h1, bind, Except.bind]
  rw [list_loop_codec hc values [] hv.2 h2]
  simp [encodeList, Nat.add_assoc]

def encodeDescriptor (value : Descriptor) : List UInt8 :=
  encodeString value.name ++ encodeInt value.addr ++ encodeInt value.size

/-- `descriptor` inverts `encodeDescriptor`. -/
theorem descriptor_codec : Codec encodeDescriptor descriptor
    (fun value => value.name.size < 2 ^ 64 ∧ value.addr < 2 ^ 64 ∧ value.size < 2 ^ 64) := by
  rintro ⟨name, addr, size⟩ ⟨h1, h2, h3⟩ data position h
  have ⟨hl, hs⟩ := occurs_append.mp h
  have ⟨hn, ha⟩ := occurs_append.mp hl
  dsimp only at h1 h2 h3 hn ha hs
  simp only [List.length_append, ← Nat.add_assoc] at hs
  simp only [descriptor, string_codec _ h1 _ _ hn, int_codec _ h2 _ _ ha, int_codec _ h3 _ _ hs,
    bind, Except.bind]
  simp only [encodeDescriptor, List.length_append, Nat.add_assoc]

/-! ## Packed words -/

/-- The byte array of a list. -/
abbrev ofList (values : List UInt8) : ByteArray := ⟨values.toArray⟩

theorem occurs_ofList : ∀ (values : List UInt8) (rest : List UInt8),
    Occurs (ofList ((rest ++ values))) rest.length values
  | [], _ => trivial
  | b :: tail, rest => by
    have hsize : (ofList (rest ++ b :: tail)).size = rest.length + (tail.length + 1) := by
      simp [ByteArray.size]
    have hlt : rest.length < (ofList (rest ++ b :: tail)).size := by omega
    refine ⟨hlt, ?_, ?_⟩
    · rw [get!_eq_getElem hlt]
      simp [ByteArray.getElem_eq_getElem_data]
    · have := occurs_ofList tail (rest ++ [b])
      simpa using this

/-- Packed words store their value above the 16-bit width field. -/
theorem packedNat_leBytes (value n : Nat) :
    packedNat (ofList (leBytes value n)) = value % 256 ^ n := by
  rw [packedNat_eq_littleValue]
  have hs : (ofList (leBytes value n)).size = n := by simp [ByteArray.size, leBytes_length]
  rw [hs]
  have := occurs_ofList (leBytes value n) []
  exact littleValue_leBytes (by simpa using this)

/-- A word holding `value` of bit width `width`, in `n ≥ 1` bytes. -/
def packWord (value width n : Nat) : ByteArray :=
  ofList (leBytes (value * 65536 + width * 2) n)

theorem wordNat_packWord {value width n : Nat} (hn : 0 < n) (hw : width * 2 < 65536)
    (hfit : value * 65536 + width * 2 < 256 ^ n) :
    wordNat (packWord value width n) = .ok value := by
  have hs : (packWord value width n).size = n := by simp [packWord, ByteArray.size, leBytes_length]
  have hne : ¬ (packWord value width n).size = 0 := by omega
  have hq : (value * 65536 + width * 2) / 65536 = value := by omega
  rw [wordNat, ite_eq_right hne, packWord, packedNat_leBytes, Nat.mod_eq_of_lt hfit, hq]

theorem wordWidth_packWord {value width n : Nat} (hw : width * 2 < 65536)
    (hfit : value * 65536 + width * 2 < 256 ^ n) :
    wordWidth (packWord value width n) = width := by
  simp only [wordWidth, packWord, packedNat_leBytes, Nat.mod_eq_of_lt hfit]
  omega

theorem wordNat_empty : wordNat ByteArray.empty = .error "empty bin_prot word" := rfl

/-- `valuePair` inverts two consecutive encoded words. -/
theorem valuePair_roundtrip {left right : ByteArray} {address value : Nat} {data : ByteArray} {position : Nat}
    (hl : left.size < 2 ^ 64) (hr : right.size < 2 ^ 64)
    (ha : wordNat left = .ok address) (hv : wordNat right = .ok value)
    (h : Occurs data position (encodeString left ++ encodeString right)) :
    valuePair ⟨data, position⟩ =
      .ok ((address, value), ⟨data, position + (encodeString left ++ encodeString right).length⟩) := by
  have ⟨h1, h2⟩ := occurs_append.mp h
  simp only [valuePair, word_codec _ hl _ _ h1, word_codec _ hr _ _ h2, ha, hv, bind, Except.bind,
    List.length_append, Nat.add_assoc]

/-! ## Areas and the memory prefix -/

/-- Wire form of an area; only areas of the shape `area` can produce have an encoding. -/
def encodeArea (value : Area) : List UInt8 :=
  encodeString value.lower ++ encodeString value.upper ++
    [if value.readonly then 1 else 0] ++ [if value.executable then 1 else 0] ++
    (match value.width with
     | some width => 1 :: encodeInt width ++ encodeOption encodeString value.fill
     | none => [0])

/-- The areas `encodeArea` represents: allocated exactly when a width is present, fill only then. -/
def ValidArea (value : Area) : Prop :=
  value.lower.size < 2 ^ 64 ∧ value.upper.size < 2 ^ 64 ∧
    (match value.width with
     | some width => value.allocated = true ∧ width < 2 ^ 64 ∧ ∀ fill, value.fill = some fill → fill.size < 2 ^ 64
     | none => value.allocated = false ∧ value.fill = none)

/-- `area` inverts `encodeArea` on every well-shaped area. -/
theorem area_codec : Codec encodeArea area ValidArea := by
  rintro ⟨lower, upper, readonly, executable, allocated, width, fill⟩ ⟨h1, h2, h3⟩ data position h
  dsimp only at h1 h2 h3
  simp only [encodeArea] at h ⊢
  have ⟨hl4, ht⟩ := occurs_append.mp h
  have ⟨hl3, he⟩ := occurs_append.mp hl4
  have ⟨hl2, hr⟩ := occurs_append.mp hl3
  have ⟨hlo, hup⟩ := occurs_append.mp hl2
  simp only [List.length_append, List.length_cons, List.length_nil, ← Nat.add_assoc] at hr he ht
  have hb1 := bool_codec readonly trivial _ _ hr
  have hb2 := bool_codec executable trivial _ _ he
  simp only [List.length_cons, List.length_nil] at hb1 hb2
  cases width with
  | none =>
    obtain ⟨rfl, rfl⟩ := h3
    simp only [Occurs] at ht
    have hy : (data.get! (position + (encodeString lower).length + (encodeString upper).length + 1 + 1)).toNat = 0 := by
      rw [ht.2.1]; rfl
    simp only [area, word_codec _ h1 _ _ hlo, word_codec _ h2 _ _ hup, hb1, hb2, bind, Except.bind]
    simp only [Nat.zero_add, byte_of_lt (reader := ⟨data, _⟩) ht.1, hy]
    simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_assoc, Nat.zero_add]
  | some width =>
    obtain ⟨rfl, hw, hf⟩ := h3
    simp only [List.cons_append, Occurs] at ht
    have ⟨hti, hto⟩ := occurs_append.mp ht.2.2
    have hopt : option ⟨data, _⟩ string = .ok (fill, ⟨data, _⟩) :=
      option_codec string_codec fill (fun x hx => hf x hx) _ _ hto
    have hy : (data.get! (position + (encodeString lower).length + (encodeString upper).length + 1 + 1)).toNat = 1 := by
      rw [ht.2.1]; rfl
    simp only [area, word_codec _ h1 _ _ hlo, word_codec _ h2 _ _ hup, hb1, hb2, bind, Except.bind]
    simp only [Nat.zero_add, byte_of_lt (reader := ⟨data, _⟩) ht.1, hy]
    rw [int_codec _ hw _ _ hti]
    have hw' : word = string := rfl
    simp only [hw']
    rw [hopt]
    simp only [List.cons_append, List.length_append, List.length_cons, List.length_nil]
    congr 3
    omega

def encodeMemoryPrefix (current descriptor : Descriptor) (layers : List Area) (values : Nat) : List UInt8 :=
  encodeDescriptor current ++ encodeInt 1 ++ encodeDescriptor descriptor ++ encodeList encodeArea layers ++
    encodeInt values

/-- `memoryPrefix` recovers every field, and `valuesOffset` is the end of the encoded prefix. -/
theorem memoryPrefix_roundtrip {current desc : Descriptor} {layers : List Area} {values : Nat}
    (hc : current.name.size < 2 ^ 64 ∧ current.addr < 2 ^ 64 ∧ current.size < 2 ^ 64)
    (hd : desc.name.size < 2 ^ 64 ∧ desc.addr < 2 ^ 64 ∧ desc.size < 2 ^ 64)
    (hl : layers.length < 2 ^ 64 ∧ ∀ area ∈ layers, ValidArea area)
    (hv : values < 2 ^ 64) {data : ByteArray} {position : Nat}
    (h : Occurs data position (encodeMemoryPrefix current desc layers values)) :
    let stop := position + (encodeMemoryPrefix current desc layers values).length
    memoryPrefix ⟨data, position⟩ = .ok (⟨current, 1, desc, layers, values, stop⟩, ⟨data, stop⟩) := by
  have ⟨h4, h5⟩ := occurs_append.mp h
  have ⟨h3, h45⟩ := occurs_append.mp h4
  have ⟨h2, hde⟩ := occurs_append.mp h3
  have ⟨hcu, hon⟩ := occurs_append.mp h2
  simp only [List.length_append, ← Nat.add_assoc] at hde h45 h5
  simp only [memoryPrefix, descriptor_codec _ hc _ _ hcu, int_codec 1 (by decide) _ _ hon, bind, Except.bind]
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, descriptor_codec _ hd _ _ hde]
  have hlist : list ⟨data, _⟩ area = .ok (layers, ⟨data, _⟩) := list_codec area_codec layers hl _ _ h45
  rw [hlist]
  simp only
  rw [int_codec _ hv _ _ h5]
  simp only [encodeMemoryPrefix, List.length_append, Nat.add_assoc]

end Bap.Proofs.Checkpoint
