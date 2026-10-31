import Lean.Elab.Command
import Bap.Crypto.KeyWrap

namespace Bap.Proofs.Crypto

open Lean Elab Command in
/-- Bind short names to private declarations of an imported module (`open private` lives in Batteries). -/
local elab "open_private_decls " mod:ident ns:ident ids:ident* : command => do
  let decls := ids.toList.map fun id =>
    OpenDecl.explicit id.getId (mkPrivateNameCore mod.getId (ns.getId ++ id.getId))
  modifyScope fun scope => { scope with openDecls := decls ++ scope.openDecls }

open Bap.Crypto
open Bap.Crypto.AES (decryptBlock decryptBlock.loop)
open_private_decls Bap.Crypto.AES Bap.Crypto.AES bytes byteArray xorByte xtime multiply multiplyLoop sbox inverseSbox
  substitute addRoundKey inverseShiftRows inverseMixColumns roundConstant rotateWord expandKey expandKey.loop

/-! ### GF(2^8): `xtime` and `multiply` are the field operations -/

theorem xtime_lt (a : Nat) : xtime a < 256 := by
  unfold xtime; exact Nat.mod_lt _ (by decide)

private theorem xtime_split : ∀ a : Fin 256,
    xtime a.val = (a.val % 128 * 2) ^^^ (if a.val / 128 = 1 then 0x1b else 0) := by
  decide +kernel

private theorem xor_mul_two (x y : Nat) : (x ^^^ y) * 2 = x * 2 ^^^ y * 2 := by
  have := @Nat.shiftLeft_xor_distrib 1 x y
  simpa [Nat.shiftLeft_eq] using this

theorem xtime_xor {a b : Nat} (ha : a < 256) (hb : b < 256) :
    xtime (a ^^^ b) = xtime a ^^^ xtime b := by
  have hab : a ^^^ b < 256 := Nat.xor_lt_two_pow (n := 8) ha hb
  have sa := xtime_split ⟨a, ha⟩
  have sb := xtime_split ⟨b, hb⟩
  have sab := xtime_split ⟨a ^^^ b, hab⟩
  simp only at sa sb sab
  have hmod : (a ^^^ b) % 128 = (a % 128) ^^^ (b % 128) := Nat.xor_mod_two_pow (n := 7)
  have hdiv : (a ^^^ b) / 128 = (a / 128) ^^^ (b / 128) := Nat.xor_div_two_pow (n := 7)
  have ha' : a / 128 = 0 ∨ a / 128 = 1 := by omega
  have hb' : b / 128 = 0 ∨ b / 128 = 1 := by omega
  rw [sab, sa, sb, hmod, hdiv, xor_mul_two]
  rcases ha' with h | h <;> rcases hb' with h' | h' <;> simp [h, h'] <;> try ac_rfl
  generalize a % 128 * 2 = x
  generalize b % 128 * 2 = y
  have : x ^^^ 27 ^^^ (y ^^^ 27) = x ^^^ y ^^^ (27 ^^^ 27) := by ac_rfl
  simp [this]

/-- `multiply` as a loop over the eight bits of the right operand. -/
def mulFrom : Nat → Nat → Nat → Nat → Nat
  | 0, r, _, _ => r
  | n + 1, r, a, b => mulFrom n (if b % 2 = 1 then r ^^^ a else r) (xtime a) (b / 2)

private theorem multiplyLoop_eq_mulFrom (n r a b : Nat) : multiplyLoop n r a b = mulFrom n r a b := by
  induction n generalizing r a b with
  | zero => rfl
  | succ n ih => simp only [multiplyLoop, mulFrom, ih]

theorem multiply_eq_mulFrom (a b : Nat) : multiply a b = mulFrom 8 0 a b := multiplyLoop_eq_mulFrom ..

private theorem mulFrom_acc (n r a b : Nat) : mulFrom n r a b = r ^^^ mulFrom n 0 a b := by
  induction n generalizing r a b with
  | zero => simp [mulFrom]
  | succ n ih =>
    simp only [mulFrom]
    split
    · rw [ih, ih (0 ^^^ a)]; simp [Nat.xor_assoc]
    · rw [ih]

private theorem mulFrom_lt (n : Nat) {r a : Nat} (b : Nat) (hr : r < 256) (ha : a < 256) :
    mulFrom n r a b < 256 := by
  induction n generalizing r a b with
  | zero => simpa [mulFrom]
  | succ n ih =>
    simp only [mulFrom]
    apply ih _ _ (xtime_lt a)
    split
    · exact Nat.xor_lt_two_pow (n := 8) hr ha
    · exact hr

theorem multiply_lt {a : Nat} (b : Nat) (ha : a < 256) : multiply a b < 256 :=
  mulFrom_lt 8 b (by decide) ha

private theorem mulFrom_left_xor (n : Nat) {a a' : Nat} (b : Nat) (ha : a < 256) (ha' : a' < 256) :
    mulFrom n 0 (a ^^^ a') b = mulFrom n 0 a b ^^^ mulFrom n 0 a' b := by
  induction n generalizing a a' b with
  | zero => simp [mulFrom]
  | succ n ih =>
    simp only [mulFrom]
    rw [xtime_xor ha ha']
    split
    · rw [mulFrom_acc n (0 ^^^ (a ^^^ a')), mulFrom_acc n (0 ^^^ a), mulFrom_acc n (0 ^^^ a'),
        ih _ (xtime_lt a) (xtime_lt a')]
      simp only [Nat.zero_xor]; ac_rfl
    · exact ih _ (xtime_lt a) (xtime_lt a')

private theorem mulFrom_right_xor (n a b c : Nat) :
    mulFrom n 0 a (b ^^^ c) = mulFrom n 0 a b ^^^ mulFrom n 0 a c := by
  induction n generalizing a b c with
  | zero => simp [mulFrom]
  | succ n ih =>
    simp only [mulFrom, Nat.xor_div_two]
    by_cases hb : b % 2 = 1 <;> by_cases hc : c % 2 = 1 <;> simp only [Nat.xor_mod_two_eq_one, hb, hc]
    all_goals simp only [iff_true, not_true_eq_false, iff_false, not_false_eq_true,
      ite_true, ite_false, Nat.zero_xor]
    · rw [ih, mulFrom_acc n a, mulFrom_acc n a]
      generalize mulFrom n 0 (xtime a) (b / 2) = x
      generalize mulFrom n 0 (xtime a) (c / 2) = y
      have : a ^^^ x ^^^ (a ^^^ y) = (a ^^^ a) ^^^ (x ^^^ y) := by ac_rfl
      rw [this, Nat.xor_self, Nat.zero_xor]
    · rw [mulFrom_acc n a, ih, mulFrom_acc n a]; ac_rfl
    · rw [mulFrom_acc n a, ih, mulFrom_acc n a]; ac_rfl
    · exact ih ..

theorem multiply_left_xor {a a' : Nat} (b : Nat) (ha : a < 256) (ha' : a' < 256) :
    multiply (a ^^^ a') b = multiply a b ^^^ multiply a' b :=
  mulFrom_left_xor 8 b ha ha'

theorem multiply_right_xor (a b c : Nat) :
    multiply a (b ^^^ c) = multiply a b ^^^ multiply a c :=
  mulFrom_right_xor 8 a b c

private theorem bits_table : ∀ x : Fin 256, x.val =
    (if x.val % 2 = 1 then 1 else 0) ^^^ (if x.val / 2 % 2 = 1 then 2 else 0) ^^^
    (if x.val / 4 % 2 = 1 then 4 else 0) ^^^ (if x.val / 8 % 2 = 1 then 8 else 0) ^^^
    (if x.val / 16 % 2 = 1 then 16 else 0) ^^^ (if x.val / 32 % 2 = 1 then 32 else 0) ^^^
    (if x.val / 64 % 2 = 1 then 64 else 0) ^^^ (if x.val / 128 % 2 = 1 then 128 else 0) := by
  decide +kernel

/-- Bytes are the span of the eight basis vectors under xor. -/
theorem byte_induction {P : Nat → Prop} (zero : P 0)
    (basis : ∀ i : Fin 8, P (2 ^ i.val))
    (xor : ∀ x y, x < 256 → y < 256 → P x → P y → P (x ^^^ y)) {x : Nat} (hx : x < 256) : P x := by
  have closed : ∀ x y, (x < 256 ∧ P x) → (y < 256 ∧ P y) → (x ^^^ y < 256 ∧ P (x ^^^ y)) :=
    fun x y hx hy => ⟨Nat.xor_lt_two_pow (n := 8) hx.1 hy.1, xor x y hx.1 hy.1 hx.2 hy.2⟩
  have bit : ∀ (i : Fin 8) (c : Prop) [Decidable c], (if c then 2 ^ i.val else 0) < 256 ∧
      P (if c then 2 ^ i.val else 0) := by
    intro i c _
    split
    · exact ⟨Nat.pow_lt_pow_right (a := 2) (by decide) i.isLt, basis i⟩
    · exact ⟨by decide, zero⟩
  have key := bits_table ⟨x, hx⟩
  simp only at key
  rw [key]
  exact (closed _ _ (closed _ _ (closed _ _ (closed _ _ (closed _ _ (closed _ _ (closed _ _
    (bit ⟨0, by decide⟩ _) (bit ⟨1, by decide⟩ _)) (bit ⟨2, by decide⟩ _)) (bit ⟨3, by decide⟩ _))
    (bit ⟨4, by decide⟩ _)) (bit ⟨5, by decide⟩ _)) (bit ⟨6, by decide⟩ _)) (bit ⟨7, by decide⟩ _)).2

theorem multiply_zero_left : ∀ b : Fin 256, multiply 0 b.val = 0 := by decide +kernel
theorem multiply_zero_right : ∀ a : Fin 256, multiply a.val 0 = 0 := by decide +kernel
theorem multiply_one_right : ∀ a : Fin 256, multiply a.val 1 = a.val := by decide +kernel

private theorem multiply_comm_basis :
    ∀ i j : Fin 8, multiply (2 ^ i.val) (2 ^ j.val) = multiply (2 ^ j.val) (2 ^ i.val) := by
  decide +kernel

private theorem pow_two_lt (i : Fin 8) : 2 ^ i.val < 256 :=
  Nat.pow_lt_pow_right (a := 2) (by decide) i.isLt

theorem multiply_comm {a b : Nat} (ha : a < 256) (hb : b < 256) : multiply a b = multiply b a := by
  refine byte_induction (P := fun a => ∀ b, b < 256 → multiply a b = multiply b a) ?_ ?_ ?_ ha b hb
  · intro b hb; rw [multiply_zero_left ⟨b, hb⟩, multiply_zero_right ⟨b, hb⟩]
  · intro i b hb
    refine byte_induction (P := fun b => multiply (2 ^ i.val) b = multiply b (2 ^ i.val)) ?_ ?_ ?_ hb
    · rw [multiply_zero_left ⟨_, pow_two_lt i⟩, multiply_zero_right ⟨_, pow_two_lt i⟩]
    · exact multiply_comm_basis i
    · intro x y hx hy ix iy
      rw [multiply_right_xor, multiply_left_xor _ hx hy, ix, iy]
  · intro x y hx hy ix iy b hb
    rw [multiply_left_xor _ hx hy, multiply_right_xor, ix b hb, iy b hb]

theorem multiply_one_left {a : Nat} (ha : a < 256) : multiply 1 a = a := by
  rw [multiply_comm (by decide) ha]; exact multiply_one_right ⟨a, ha⟩

private theorem multiply_assoc_basis : ∀ i j k : Fin 8,
    multiply (multiply (2 ^ i.val) (2 ^ j.val)) (2 ^ k.val) =
      multiply (2 ^ i.val) (multiply (2 ^ j.val) (2 ^ k.val)) := by
  decide +kernel

theorem multiply_assoc {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    multiply (multiply a b) c = multiply a (multiply b c) := by
  refine byte_induction
    (P := fun c => multiply (multiply a b) c = multiply a (multiply b c)) ?_ ?_ ?_ hc
  · rw [multiply_zero_right ⟨_, multiply_lt b ha⟩, multiply_zero_right ⟨_, hb⟩, multiply_zero_right ⟨_, ha⟩]
  · intro k
    have hk := pow_two_lt k
    refine byte_induction
      (P := fun b => multiply (multiply a b) (2 ^ k.val) = multiply a (multiply b (2 ^ k.val)))
      ?_ ?_ ?_ hb
    · rw [multiply_zero_right ⟨_, ha⟩, multiply_zero_left ⟨_, hk⟩, multiply_zero_right ⟨_, ha⟩]
    · intro j
      have hj := pow_two_lt j
      refine byte_induction
        (P := fun a => multiply (multiply a (2 ^ j.val)) (2 ^ k.val) =
          multiply a (multiply (2 ^ j.val) (2 ^ k.val))) ?_ ?_ ?_ ha
      · rw [multiply_zero_left ⟨_, hj⟩, multiply_zero_left ⟨_, hk⟩,
          multiply_zero_left ⟨_, multiply_lt _ hj⟩]
      · exact fun i => multiply_assoc_basis i j k
      · intro x y hx hy ix iy
        rw [multiply_left_xor _ hx hy, multiply_left_xor _ (multiply_lt _ hx) (multiply_lt _ hy), ix, iy,
          multiply_left_xor _ hx hy]
    · intro x y hx hy ix iy
      rw [multiply_right_xor, multiply_left_xor _ (multiply_lt _ ha) (multiply_lt _ ha), ix, iy,
        multiply_left_xor _ hx hy, multiply_right_xor]
  · intro x y _ _ ix iy
    simp only [multiply_right_xor, ix, iy]

/-- `a ^ 254` by square-and-multiply, the field inverse of a non-zero byte. -/
def gfInverse (a : Nat) : Nat :=
  let a2 := multiply a a
  let a4 := multiply a2 a2
  let a8 := multiply a4 a4
  let a16 := multiply a8 a8
  let a32 := multiply a16 a16
  let a64 := multiply a32 a32
  let a128 := multiply a64 a64
  multiply a2 (multiply a4 (multiply a8 (multiply a16 (multiply a32 (multiply a64 a128)))))

theorem multiply_gfInverse : ∀ a : Fin 256, a.val ≠ 0 → multiply a.val (gfInverse a.val) = 1 := by
  decide +kernel

theorem gfInverse_lt : ∀ a : Fin 256, gfInverse a.val < 256 := by
  decide +kernel

/-- GF(2^8) has no zero divisors. -/
theorem multiply_eq_zero {a b : Nat} (ha : a < 256) (hb : b < 256) (h : multiply a b = 0) :
    a = 0 ∨ b = 0 := by
  by_cases ha0 : a = 0
  · exact .inl ha0
  · refine .inr ?_
    have hi := gfInverse_lt ⟨a, ha⟩
    have unit := multiply_gfInverse ⟨a, ha⟩ ha0
    simp only at unit hi
    have := multiply_assoc hi ha hb
    rw [multiply_comm hi ha, unit, multiply_one_left hb, h] at this
    rw [this]; exact multiply_zero_right ⟨_, hi⟩

/-! ### S-box -/

/-- The spelled-out table is what a search of the S-box finds. -/
private theorem inverseSbox_eq_search : inverseSbox = (List.range 256).map fun value =>
    match (List.range 256).find? fun index => sbox[index]!.toNat = value with
    | some index => UInt8.ofNat index
    | none => 0 := by
  decide +kernel

private theorem sbox_inverse_table :
    ∀ b : Fin 256, inverseSbox[(sbox[b.val]!).toNat]! = UInt8.ofNat b.val := by
  decide +kernel

private theorem inverse_sbox_table :
    ∀ b : Fin 256, sbox[(inverseSbox[b.val]!).toNat]! = UInt8.ofNat b.val := by
  decide +kernel

/-- The computed inverse S-box is a left inverse of the S-box on all 256 bytes. -/
theorem inverseSbox_sbox (b : UInt8) : inverseSbox[(sbox[b.toNat]!).toNat]! = b := by
  have := sbox_inverse_table ⟨b.toNat, b.toNat_lt⟩
  simpa using this

/-- ... and a right inverse, so the S-box is a permutation of the bytes. -/
theorem sbox_inverseSbox (b : UInt8) : sbox[(inverseSbox[b.toNat]!).toNat]! = b := by
  have := inverse_sbox_table ⟨b.toNat, b.toNat_lt⟩
  simpa using this

theorem sbox_injective {a b : UInt8} (h : sbox[a.toNat]! = sbox[b.toNat]!) : a = b := by
  rw [← inverseSbox_sbox a, h, inverseSbox_sbox]

theorem substitute_inverse_sbox (s : List UInt8) :
    substitute inverseSbox (substitute sbox s) = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [substitute, List.map_cons] at ih ⊢; rw [ih, inverseSbox_sbox]

theorem substitute_sbox_inverse (s : List UInt8) :
    substitute sbox (substitute inverseSbox s) = s := by
  induction s with
  | nil => rfl
  | cons a s ih => simp only [substitute, List.map_cons] at ih ⊢; rw [ih, sbox_inverseSbox]

theorem length_substitute (table s : List UInt8) : (substitute table s).length = s.length := by
  simp [substitute]

/-! ### AddRoundKey -/

theorem xorByte_cancel (a k : UInt8) : xorByte (xorByte a k) k = a := by
  have hlt : a.toNat ^^^ k.toNat < 2 ^ 8 := Nat.xor_lt_two_pow a.toNat_lt k.toNat_lt
  simp only [xorByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact UInt8.ofNat_toNat

theorem length_addRoundKey (s k : List UInt8) :
    (addRoundKey s k).length = min s.length k.length := by
  simp [addRoundKey]

/-- AddRoundKey is an involution as long as the round key covers the state. -/
theorem addRoundKey_cancel {s k : List UInt8} (h : s.length ≤ k.length) :
    addRoundKey (addRoundKey s k) k = s := by
  induction s generalizing k with
  | nil => rfl
  | cons a s ih =>
    cases k with
    | nil => simp at h
    | cons x k =>
      have := ih (k := k) (by simpa using h)
      simp only [addRoundKey, List.zip_cons_cons, List.map_cons] at this ⊢
      rw [xorByte_cancel, this]

/-! ### ShiftRows and MixColumns: the forward transforms are FIPS-197's, proved inverse -/

/-- FIPS-197 ShiftRows; the production code implements only its inverse. -/
def shiftRows (state : List UInt8) : List UInt8 :=
  (List.range 16).map fun index =>
    let row := index % 4
    let column := index / 4
    state[row + 4 * ((column + row) % 4)]!

/-- A list of the given length is a literal of that length. -/
private theorem eq_literal16 {s : List UInt8} (h : s.length = 16) :
    ∃ a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15,
      s = [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15] := by
  match s, h with
  | [a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15], _ =>
    exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩

theorem length_shiftRows (s : List UInt8) : (shiftRows s).length = 16 := by
  simp [shiftRows]

theorem length_inverseShiftRows (s : List UInt8) : (inverseShiftRows s).length = 16 := by
  simp [inverseShiftRows]

theorem inverseShiftRows_shiftRows {s : List UInt8} (h : s.length = 16) :
    inverseShiftRows (shiftRows s) = s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := eq_literal16 h
  rfl

theorem shiftRows_inverseShiftRows {s : List UInt8} (h : s.length = 16) :
    shiftRows (inverseShiftRows s) = s := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := eq_literal16 h
  rfl

/-- One row of a MixColumns matrix applied to a column. -/
def dot (a0 a1 a2 a3 c0 c1 c2 c3 : Nat) : Nat :=
  multiply a0 c0 ^^^ multiply a1 c1 ^^^ multiply a2 c2 ^^^ multiply a3 c3

private theorem dot_lt {a0 a1 a2 a3 : Nat} (c0 c1 c2 c3 : Nat)
    (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256) (h3 : a3 < 256) :
    dot a0 a1 a2 a3 c0 c1 c2 c3 < 256 :=
  Nat.xor_lt_two_pow (n := 8) (Nat.xor_lt_two_pow (n := 8)
    (Nat.xor_lt_two_pow (n := 8) (multiply_lt _ h0) (multiply_lt _ h1)) (multiply_lt _ h2)) (multiply_lt _ h3)

/-- Composing rows: the coefficient of each input is the matrix product over GF(2^8). -/
theorem dot_dot {a0 a1 a2 a3 : Nat} {c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33 k0 k1 k2 k3
      e0 e1 e2 e3 : Nat}
    (h0 : a0 < 256) (h1 : a1 < 256) (h2 : a2 < 256) (h3 : a3 < 256)
    (hc : c00 < 256 ∧ c01 < 256 ∧ c02 < 256 ∧ c03 < 256 ∧ c10 < 256 ∧ c11 < 256 ∧ c12 < 256 ∧ c13 < 256 ∧
      c20 < 256 ∧ c21 < 256 ∧ c22 < 256 ∧ c23 < 256 ∧ c30 < 256 ∧ c31 < 256 ∧ c32 < 256 ∧ c33 < 256)
    (hk : k0 < 256 ∧ k1 < 256 ∧ k2 < 256 ∧ k3 < 256)
    (he0 : dot c00 c10 c20 c30 k0 k1 k2 k3 = e0) (he1 : dot c01 c11 c21 c31 k0 k1 k2 k3 = e1)
    (he2 : dot c02 c12 c22 c32 k0 k1 k2 k3 = e2) (he3 : dot c03 c13 c23 c33 k0 k1 k2 k3 = e3) :
    dot (dot a0 a1 a2 a3 c00 c01 c02 c03) (dot a0 a1 a2 a3 c10 c11 c12 c13)
        (dot a0 a1 a2 a3 c20 c21 c22 c23) (dot a0 a1 a2 a3 c30 c31 c32 c33) k0 k1 k2 k3 =
      dot a0 a1 a2 a3 e0 e1 e2 e3 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := hc
  obtain ⟨_, _, _, _⟩ := hk
  have row : ∀ c0 c1 c2 c3 k, c0 < 256 → c1 < 256 → c2 < 256 → c3 < 256 → k < 256 →
      multiply (dot a0 a1 a2 a3 c0 c1 c2 c3) k =
        multiply a0 (multiply c0 k) ^^^ multiply a1 (multiply c1 k) ^^^
          multiply a2 (multiply c2 k) ^^^ multiply a3 (multiply c3 k) := by
    intro c0 c1 c2 c3 k _ _ _ _ _
    have l0 := multiply_lt c0 h0
    have l1 := multiply_lt c1 h1
    have l2 := multiply_lt c2 h2
    have l3 := multiply_lt c3 h3
    have l01 : multiply a0 c0 ^^^ multiply a1 c1 < 256 := Nat.xor_lt_two_pow (n := 8) l0 l1
    have l012 : multiply a0 c0 ^^^ multiply a1 c1 ^^^ multiply a2 c2 < 256 :=
      Nat.xor_lt_two_pow (n := 8) l01 l2
    simp only [dot]
    rw [multiply_left_xor _ l012 l3, multiply_left_xor _ l01 l2, multiply_left_xor _ l0 l1,
      multiply_assoc h0 ‹_› ‹_›, multiply_assoc h1 ‹_› ‹_›, multiply_assoc h2 ‹_› ‹_›, multiply_assoc h3 ‹_› ‹_›]
  rw [← he0, ← he1, ← he2, ← he3]
  simp only [dot] at row ⊢
  rw [row _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›, row _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›,
    row _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›, row _ _ _ _ _ ‹_› ‹_› ‹_› ‹_› ‹_›]
  simp only [multiply_right_xor]
  ac_rfl

private theorem dot_unit0 {a b c d : Nat} (h : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    dot a b c d 1 0 0 0 = a := by
  simp [dot, multiply_one_right ⟨a, h⟩, multiply_zero_right ⟨b, hb⟩, multiply_zero_right ⟨c, hc⟩,
    multiply_zero_right ⟨d, hd⟩]

private theorem dot_unit1 {a b c d : Nat} (h : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    dot a b c d 0 1 0 0 = b := by
  simp [dot, multiply_zero_right ⟨a, h⟩, multiply_one_right ⟨b, hb⟩, multiply_zero_right ⟨c, hc⟩,
    multiply_zero_right ⟨d, hd⟩]

private theorem dot_unit2 {a b c d : Nat} (h : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    dot a b c d 0 0 1 0 = c := by
  simp [dot, multiply_zero_right ⟨a, h⟩, multiply_zero_right ⟨b, hb⟩, multiply_one_right ⟨c, hc⟩,
    multiply_zero_right ⟨d, hd⟩]

private theorem dot_unit3 {a b c d : Nat} (h : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256) :
    dot a b c d 0 0 0 1 = d := by
  simp [dot, multiply_zero_right ⟨a, h⟩, multiply_zero_right ⟨b, hb⟩, multiply_zero_right ⟨c, hc⟩,
    multiply_one_right ⟨d, hd⟩]

/-- A column transform with the given coefficient matrix, as the production code writes it. -/
def col (c00 c01 c02 c03 c10 c11 c12 c13 c20 c21 c22 c23 c30 c31 c32 c33 : Nat) (a b c d : UInt8) : List UInt8 :=
  [UInt8.ofNat (dot a.toNat b.toNat c.toNat d.toNat c00 c01 c02 c03),
   UInt8.ofNat (dot a.toNat b.toNat c.toNat d.toNat c10 c11 c12 c13),
   UInt8.ofNat (dot a.toNat b.toNat c.toNat d.toNat c20 c21 c22 c23),
   UInt8.ofNat (dot a.toNat b.toNat c.toNat d.toNat c30 c31 c32 c33)]

/-- FIPS-197 MixColumn on one column. -/
abbrev mixCol := col 2 3 1 1 1 2 3 1 1 1 2 3 3 1 1 2
/-- FIPS-197 InvMixColumn on one column. -/
abbrev invCol := col 14 11 13 9 9 14 11 13 13 9 14 11 11 13 9 14

/-- FIPS-197 MixColumns; the production code implements only its inverse. -/
def mixColumns (state : List UInt8) : List UInt8 :=
  (List.range 4).flatMap fun column =>
    let offset := column * 4
    mixCol state[offset]! state[offset + 1]! state[offset + 2]! state[offset + 3]!

private theorem toNat_ofNat_dot {a0 a1 a2 a3 : UInt8} (c0 c1 c2 c3 : Nat) :
    (UInt8.ofNat (dot a0.toNat a1.toNat a2.toNat a3.toNat c0 c1 c2 c3)).toNat =
      dot a0.toNat a1.toNat a2.toNat a3.toNat c0 c1 c2 c3 :=
  UInt8.toNat_ofNat_of_lt' (dot_lt _ _ _ _ a0.toNat_lt a1.toNat_lt a2.toNat_lt a3.toNat_lt)

/-- InvMixColumn undoes MixColumn: the two matrices multiply to the identity over GF(2^8). -/
theorem invCol_mixCol (a b c d : UInt8) :
    (match mixCol a b c d with
      | [w, x, y, z] => invCol w x y z
      | _ => []) = [a, b, c, d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [col, toNat_ofNat_dot]
  rw [dot_dot ha hb hc hd (by decide) (by decide) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_unit0 ha hb hc hd, dot_unit1 ha hb hc hd, dot_unit2 ha hb hc hd, dot_unit3 ha hb hc hd]
  simp

/-- MixColumn undoes InvMixColumn. -/
theorem mixCol_invCol (a b c d : UInt8) :
    (match invCol a b c d with
      | [w, x, y, z] => mixCol w x y z
      | _ => []) = [a, b, c, d] := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hc := c.toNat_lt
  have hd := d.toNat_lt
  simp only [col, toNat_ofNat_dot]
  rw [dot_dot ha hb hc hd (by decide) (by decide) (e0 := 1) (e1 := 0) (e2 := 0) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 1) (e2 := 0) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 0) (e2 := 1) (e3 := 0)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_dot ha hb hc hd (by decide) (by decide) (e0 := 0) (e1 := 0) (e2 := 0) (e3 := 1)
      (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel),
    dot_unit0 ha hb hc hd, dot_unit1 ha hb hc hd, dot_unit2 ha hb hc hd, dot_unit3 ha hb hc hd]
  simp

private theorem append_congr {a b c d : List UInt8} (h : a = b) (h' : c = d) : a ++ c = b ++ d := by
  rw [h, h']

theorem length_inverseMixColumns (s : List UInt8) : (inverseMixColumns s).length = 16 := rfl
theorem length_mixColumns (s : List UInt8) : (mixColumns s).length = 16 := rfl

theorem inverseMixColumns_mixColumns {s : List UInt8} (h : s.length = 16) :
    inverseMixColumns (mixColumns s) = s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, rfl⟩ := eq_literal16 h
  have c1 := invCol_mixCol a0 a1 a2 a3
  have c2 := invCol_mixCol a4 a5 a6 a7
  have c3 := invCol_mixCol a8 a9 a10 a11
  have c4 := invCol_mixCol a12 a13 a14 a15
  simp only [col] at c1 c2 c3 c4
  exact append_congr c1 (append_congr c2 (append_congr c3 (append_congr c4 rfl)))

theorem mixColumns_inverseMixColumns {s : List UInt8} (h : s.length = 16) :
    mixColumns (inverseMixColumns s) = s := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, rfl⟩ := eq_literal16 h
  have c1 := mixCol_invCol a0 a1 a2 a3
  have c2 := mixCol_invCol a4 a5 a6 a7
  have c3 := mixCol_invCol a8 a9 a10 a11
  have c4 := mixCol_invCol a12 a13 a14 a15
  simp only [col] at c1 c2 c3 c4
  exact append_congr c1 (append_congr c2 (append_congr c3 (append_congr c4 rfl)))

/-! ### Key expansion -/

/-- Key sizes FIPS-197 defines. -/
def ValidKeyLength (n : Nat) : Prop := n = 16 ∨ n = 24 ∨ n = 32

instance (n : Nat) : Decidable (ValidKeyLength n) := by unfold ValidKeyLength; infer_instance

theorem length_rotateWord (w : List UInt8) : (rotateWord w).length = w.length := by
  cases w <;> simp [rotateWord]

private theorem getBang_mem {l : List (List UInt8)} {i : Nat} (h : i < l.length) : l[i]! ∈ l := by
  rw [getElem!_pos l i h]; exact List.getElem_mem h

private theorem expandLoop_spec (nk wordCount index : Nat) (words : List (List UInt8))
    (hidx : nk ≤ index) (hnk : 0 < nk) (hlen : words.length = index)
    (hwords : ∀ w ∈ words, w.length = 4) :
    let out := expandKey.loop nk wordCount index words
    (∀ w ∈ out, w.length = 4) ∧ out.length = max index wordCount := by
  induction hm : wordCount - index generalizing index words with
  | zero =>
    rw [expandKey.loop, ite_eq_left (by omega)]
    exact ⟨hwords, by omega⟩
  | succ m ih =>
    rw [expandKey.loop, ite_eq_right (by omega)]
    simp only
    have hprev := hwords _ (getBang_mem (l := words) (i := index - 1) (by omega))
    have hsrc := hwords _ (getBang_mem (l := words) (i := index - nk) (by omega))
    have hmax : max index wordCount = max (index + 1) wordCount := by omega
    rw [hmax]
    refine ih (index + 1) (words ++ [_]) (by omega) (by simp [hlen]) ?_ (by omega)
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hwords w hw
    · have hsub := length_substitute sbox (rotateWord words[index - 1]!)
      rw [length_rotateWord, hprev] at hsub
      rw [List.mem_singleton.mp hw, length_addRoundKey, hsrc]
      split
      · split
        · next heq => rw [heq] at hsub; simp only [List.length_cons] at hsub ⊢; omega
        · next heq => rw [heq] at hsub; simp at hsub
      · split
        · rw [length_substitute, hprev]; rfl
        · rw [hprev]; rfl

private theorem length_flatten_words (words : List (List UInt8)) (h : ∀ w ∈ words, w.length = 4) :
    words.flatten.length = 4 * words.length := by
  induction words with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    rw [h w (by simp), ih fun x hx => h x (by simp [hx])]
    omega

theorem expandKey_invalid {key : List UInt8} (h : ¬ ValidKeyLength key.length) :
    expandKey key = .error "AES key must contain 16, 24, or 32 bytes" := by
  rw [expandKey, ite_eq_left]
  simp only [ValidKeyLength, not_or] at h
  simp [h]

/-- A valid key expands to exactly one 16-byte round key per round, plus the initial one. -/
theorem expandKey_valid {key : List UInt8} (h : ValidKeyLength key.length) :
    ∃ expanded, expandKey key = .ok (key.length / 4 + 6, expanded) ∧
      expanded.length = 16 * (key.length / 4 + 6 + 1) := by
  rw [expandKey, ite_eq_right (by rcases h with h | h | h <;> simp [h])]
  refine ⟨_, rfl, ?_⟩
  have hnk : 0 < key.length / 4 := by rcases h with h | h | h <;> omega
  have hmul : key.length / 4 * 4 = key.length := by rcases h with h | h | h <;> omega
  have spec := expandLoop_spec (key.length / 4) (4 * (key.length / 4 + 6 + 1)) (key.length / 4)
    ((List.range (key.length / 4)).map fun index => key.extract (index * 4) (index * 4 + 4))
    (Nat.le_refl _) hnk (by simp) (by
      intro w hw
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
      have hi' := List.mem_range.mp hi
      have : i * 4 + 4 ≤ key.length := by
        rw [← hmul]; exact (Nat.succ_mul i 4).symm ▸ Nat.mul_le_mul_right 4 hi'
      simp
      omega)
  simp only at spec
  rw [length_flatten_words _ spec.1, spec.2]
  omega

theorem length_roundKey {expanded : List UInt8} {rounds r : Nat}
    (h : expanded.length = 16 * (rounds + 1)) (hr : r ≤ rounds) :
    (expanded.extract (r * 16) (r * 16 + 16)).length = 16 := by
  simp
  omega

/-! ### Bytes and lists -/

private theorem length_data (bs : ByteArray) : bs.data.toList.length = bs.size := rfl

private theorem toList_loop (bs : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
  induction hm : bs.size - i generalizing i r with
  | zero =>
    rw [ByteArray.toList.loop, ite_eq_right (by omega)]
    rw [List.drop_eq_nil_of_le (by rw [length_data]; omega), List.append_nil]
  | succ m ih =>
    have hi : i < bs.size := by omega
    rw [ByteArray.toList.loop, ite_eq_left hi, ih (i + 1) _ (by omega)]
    have hi' : i < bs.data.toList.length := by rw [length_data]; exact hi
    rw [List.drop_eq_getElem_cons hi']
    have : bs.get! i = bs.data.toList[i] := by
      cases bs with
      | mk data => simp only [ByteArray.get!]; simp [getElem!_pos, show i < data.size from hi]
    simp [this]

theorem toList_eq (bs : ByteArray) : bs.toList = bs.data.toList := by
  simp [ByteArray.toList, toList_loop]

theorem length_toList (bs : ByteArray) : bs.toList.length = bs.size := by
  rw [toList_eq, length_data]

theorem toList_mk (l : List UInt8) : (ByteArray.mk l.toArray).toList = l := by
  simp [toList_eq]

theorem size_mk (l : List UInt8) : (ByteArray.mk l.toArray).size = l.length := by
  rw [← length_data]

theorem mk_toList (bs : ByteArray) : ByteArray.mk bs.toList.toArray = bs := by
  cases bs; simp [toList_eq]

/-! ### Decryption: rejection, output shape, and the forward cipher it inverts -/

theorem decryptBlock_bad_block {input : ByteArray} (key : ByteArray) (h : input.size ≠ 16) :
    decryptBlock key input = .error "AES block must contain 16 bytes" := by
  rw [decryptBlock, ite_eq_left (by simpa using h)]

theorem decryptBlock_bad_key {key input : ByteArray} (hs : input.size = 16)
    (h : ¬ ValidKeyLength key.size) :
    decryptBlock key input = .error "AES key must contain 16, 24, or 32 bytes" := by
  rw [decryptBlock, ite_eq_right (by simp [hs])]
  have : expandKey (bytes key) = _ := expandKey_invalid (key := bytes key) (by
    simpa [bytes, length_toList] using h)
  rw [this]; rfl

private theorem decryptBlock_eq {key input : ByteArray} {rounds : Nat} {expanded : List UInt8}
    (hs : input.size = 16) (hk : expandKey key.toList = .ok (rounds, expanded)) :
    decryptBlock key input = .ok (ByteArray.mk (addRoundKey
      (substitute inverseSbox (inverseShiftRows (decryptBlock.loop expanded (rounds - 1)
        (addRoundKey input.toList (expanded.extract (rounds * 16) (rounds * 16 + 16))))))
      (expanded.extract 0 16)).toArray) := by
  rw [decryptBlock, ite_eq_right (by simp [hs])]
  simp only [bytes, hk]
  rfl

private theorem length_decryptLoop (expanded : List UInt8) (r : Nat) {s : List UInt8} (h : s.length = 16) :
    (decryptBlock.loop expanded r s).length = 16 := by
  induction r generalizing s with
  | zero => rw [decryptBlock.loop]; simpa
  | succ r ih =>
    rw [decryptBlock.loop, ite_eq_right (by simp)]
    exact ih rfl

/-- One round of the forward cipher, repeated `r` times: FIPS-197 Cipher without the last round. -/
def encryptLoop (expanded : List UInt8) : Nat → List UInt8 → List UInt8
  | 0, s => s
  | r + 1, s =>
    addRoundKey (mixColumns (shiftRows (substitute sbox (encryptLoop expanded r s))))
      (expanded.extract ((r + 1) * 16) ((r + 1) * 16 + 16))

/-- FIPS-197 Cipher, the forward direction the production code does not implement. -/
def encryptBlock (key input : ByteArray) : Except String ByteArray := do
  if input.size != 16 then
    .error "AES block must contain 16 bytes"
  else
    let (rounds, expanded) ← expandKey key.toList
    let middle := encryptLoop expanded (rounds - 1) (addRoundKey input.toList (expanded.extract 0 16))
    .ok (ByteArray.mk (addRoundKey (shiftRows (substitute sbox middle))
      (expanded.extract (rounds * 16) (rounds * 16 + 16))).toArray)

private theorem encryptBlock_eq {key input : ByteArray} {rounds : Nat} {expanded : List UInt8}
    (hs : input.size = 16) (hk : expandKey key.toList = .ok (rounds, expanded)) :
    encryptBlock key input = .ok (ByteArray.mk (addRoundKey (shiftRows (substitute sbox
      (encryptLoop expanded (rounds - 1) (addRoundKey input.toList (expanded.extract 0 16)))))
      (expanded.extract (rounds * 16) (rounds * 16 + 16))).toArray) := by
  simp only [encryptBlock, hs, hk]
  rfl

private theorem decrypt_encrypt_loop {expanded : List UInt8} {rounds : Nat}
    (hE : expanded.length = 16 * (rounds + 1)) {s : List UInt8} (hs : s.length = 16)
    (r : Nat) (hr : r ≤ rounds) :
    (encryptLoop expanded r s).length = 16 ∧
      decryptBlock.loop expanded r (shiftRows (substitute sbox (encryptLoop expanded r s))) =
        shiftRows (substitute sbox s) := by
  induction r with
  | zero =>
    refine ⟨hs, ?_⟩
    rw [decryptBlock.loop]; rfl
  | succ r ih =>
    obtain ⟨hlen, hloop⟩ := ih (by omega)
    have hk := length_roundKey (r := r + 1) hE hr
    have hnext : (encryptLoop expanded (r + 1) s).length = 16 := by
      simp only [encryptLoop, length_addRoundKey, length_mixColumns, hk]; rfl
    refine ⟨hnext, ?_⟩
    rw [decryptBlock.loop, ite_eq_right (by simp)]
    simp only [Nat.add_sub_cancel]
    rw [inverseShiftRows_shiftRows (by rw [length_substitute, hnext]), substitute_inverse_sbox]
    conv => lhs; arg 3; arg 1; arg 1; simp only [encryptLoop]
    rw [addRoundKey_cancel (by rw [length_mixColumns, hk]; omega), inverseMixColumns_mixColumns (length_shiftRows _)]
    exact hloop

private theorem encrypt_decrypt_loop {expanded : List UInt8} {rounds : Nat}
    (hE : expanded.length = 16 * (rounds + 1)) (r : Nat) (hr : r ≤ rounds) {y : List UInt8}
    (hy : y.length = 16) :
    encryptLoop expanded r (substitute inverseSbox (inverseShiftRows (decryptBlock.loop expanded r y))) =
      substitute inverseSbox (inverseShiftRows y) := by
  induction r generalizing y with
  | zero => rw [decryptBlock.loop]; rfl
  | succ r ih =>
    have hk := length_roundKey (r := r + 1) hE hr
    rw [decryptBlock.loop, ite_eq_right (by simp)]
    simp only [Nat.add_sub_cancel, encryptLoop]
    rw [ih (by omega) (length_inverseMixColumns _), substitute_sbox_inverse,
      shiftRows_inverseShiftRows (length_inverseMixColumns _),
      mixColumns_inverseMixColumns (by
        rw [length_addRoundKey, length_substitute, length_inverseShiftRows, hk]; rfl),
      addRoundKey_cancel (by rw [length_substitute, length_inverseShiftRows, hk]; omega)]

/-- Decryption inverts the forward cipher, for every valid key and block. -/
theorem decryptBlock_encryptBlock {key plain : ByteArray} (hk : ValidKeyLength key.size)
    (hp : plain.size = 16) :
    ∃ cipher, encryptBlock key plain = .ok cipher ∧ cipher.size = 16 ∧
      decryptBlock key cipher = .ok plain := by
  obtain ⟨E, hexp, hlen⟩ := expandKey_valid (key := key.toList) (by rwa [length_toList])
  have hpos : (key.toList.length / 4 + 6 - 1) ≤ key.toList.length / 4 + 6 := by omega
  have hsucc : key.toList.length / 4 + 6 - 1 + 1 = key.toList.length / 4 + 6 := by omega
  generalize hR : key.toList.length / 4 + 6 = rounds at *
  have h0 := length_roundKey (r := 0) hlen (by omega)
  have hN := length_roundKey (r := rounds) hlen (Nat.le_refl _)
  have hx0 : (addRoundKey plain.toList (E.extract 0 16)).length = 16 := by
    rw [length_addRoundKey, length_toList, hp, h0]; rfl
  obtain ⟨hmid, hloop⟩ := decrypt_encrypt_loop hlen hx0 (rounds - 1) hpos
  refine ⟨_, encryptBlock_eq hp hexp, ?_, ?_⟩
  · rw [size_mk, length_addRoundKey, length_shiftRows, hN]; rfl
  · rw [decryptBlock_eq (by rw [size_mk, length_addRoundKey, length_shiftRows, hN]; rfl) hexp, toList_mk,
      addRoundKey_cancel (by rw [length_shiftRows, hN]; omega), hloop,
      inverseShiftRows_shiftRows (by rw [length_substitute, hx0]), substitute_inverse_sbox,
      addRoundKey_cancel (by rw [length_toList, hp, h0]; omega), mk_toList]

/-- `decryptBlock` succeeds exactly on valid key and block sizes. -/
theorem decryptBlock_ok_iff (key input : ByteArray) :
    (∃ plain, decryptBlock key input = .ok plain) ↔ ValidKeyLength key.size ∧ input.size = 16 := by
  constructor
  · rintro ⟨plain, h⟩
    by_cases hs : input.size = 16
    · refine ⟨?_, hs⟩
      by_cases hk : ValidKeyLength key.size
      · exact hk
      · rw [decryptBlock_bad_key hs hk] at h; cases h
    · rw [decryptBlock_bad_block key hs] at h; cases h
  · rintro ⟨hk, hs⟩
    obtain ⟨E, hexp, _⟩ := expandKey_valid (key := key.toList) (by rwa [length_toList])
    exact ⟨_, decryptBlock_eq hs hexp⟩

/-- Successful decryption produces a block: the round keys always cover the state. -/
theorem decryptBlock_ok_size {key input plain : ByteArray} (h : decryptBlock key input = .ok plain) :
    plain.size = 16 := by
  obtain ⟨hk, hs⟩ := (decryptBlock_ok_iff key input).mp ⟨plain, h⟩
  obtain ⟨E, hexp, hlen⟩ := expandKey_valid (key := key.toList) (by rwa [length_toList])
  rw [decryptBlock_eq hs hexp] at h
  cases h
  have h0 := length_roundKey (r := 0) hlen (by omega)
  rw [size_mk, length_addRoundKey, length_substitute, length_inverseShiftRows, h0]; rfl

/-- The forward cipher inverts decryption. -/
theorem encryptBlock_decryptBlock {key cipher plain : ByteArray}
    (h : decryptBlock key cipher = .ok plain) : encryptBlock key plain = .ok cipher := by
  obtain ⟨hk, hs⟩ := (decryptBlock_ok_iff key cipher).mp ⟨plain, h⟩
  have hp := decryptBlock_ok_size h
  obtain ⟨E, hexp, hlen⟩ := expandKey_valid (key := key.toList) (by rwa [length_toList])
  have hpos : (key.toList.length / 4 + 6 - 1) ≤ key.toList.length / 4 + 6 := by omega
  generalize key.toList.length / 4 + 6 = rounds at *
  have h0 := length_roundKey (r := 0) hlen (by omega)
  have hN := length_roundKey (r := rounds) hlen (Nat.le_refl _)
  rw [decryptBlock_eq hs hexp] at h
  cases h
  have hinit : (addRoundKey cipher.toList (E.extract (rounds * 16) (rounds * 16 + 16))).length = 16 := by
    rw [length_addRoundKey, length_toList, hs, hN]; rfl
  rw [encryptBlock_eq (by
      rw [size_mk, length_addRoundKey, length_substitute, length_inverseShiftRows, h0]; rfl) hexp,
    toList_mk,
    addRoundKey_cancel (by rw [length_substitute, length_inverseShiftRows, h0]; omega),
    encrypt_decrypt_loop hlen _ hpos hinit, substitute_sbox_inverse,
    shiftRows_inverseShiftRows hinit,
    addRoundKey_cancel (by rw [length_toList, hs, hN]; omega), mk_toList]

/-- For each key, AES decryption is injective on blocks: it really is a permutation. -/
theorem decryptBlock_injective {key c c' plain : ByteArray}
    (h : decryptBlock key c = .ok plain) (h' : decryptBlock key c' = .ok plain) : c = c' := by
  have e := encryptBlock_decryptBlock h
  rw [encryptBlock_decryptBlock h'] at e
  cases e; rfl

/-- ... and surjective onto blocks, for each valid key. -/
theorem decryptBlock_surjective {key plain : ByteArray} (hk : ValidKeyLength key.size)
    (hp : plain.size = 16) : ∃ cipher, decryptBlock key cipher = .ok plain :=
  let ⟨c, _, _, h⟩ := decryptBlock_encryptBlock hk hp
  ⟨c, h⟩

/-! ### Published vectors, checked by the kernel -/

private def fipsPlain : List UInt8 :=
  [0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]

theorem fips197_aes128_decrypt :
    (decryptBlock (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
      (ByteArray.mk #[0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a])).toOption =
    some (ByteArray.mk fipsPlain.toArray) := by
  decide +kernel

theorem fips197_aes192_decrypt :
    (decryptBlock (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
      (ByteArray.mk #[0xdd,0xa9,0x7c,0xa4,0x86,0x4c,0xdf,0xe0,0x6e,0xaf,0x70,0xa0,0xec,0x0d,0x71,0x91])).toOption =
    some (ByteArray.mk fipsPlain.toArray) := by
  decide +kernel

theorem fips197_aes256_decrypt :
    (decryptBlock (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
      (ByteArray.mk #[0x8e,0xa2,0xb7,0xca,0x51,0x67,0x45,0xbf,0xea,0xfc,0x49,0x90,0x4b,0x49,0x60,0x89])).toOption =
    some (ByteArray.mk fipsPlain.toArray) := by
  decide +kernel

/-- The forward cipher defined here is FIPS-197's: it reproduces the published ciphertext. -/
theorem fips197_aes128_encrypt :
    (encryptBlock (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]) (ByteArray.mk fipsPlain.toArray)).toOption =
    some (ByteArray.mk #[0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a]) := by
  decide +kernel

theorem fips197_aes256_encrypt :
    (encryptBlock (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
      (ByteArray.mk fipsPlain.toArray)).toOption =
    some (ByteArray.mk #[0x8e,0xa2,0xb7,0xca,0x51,0x67,0x45,0xbf,0xea,0xfc,0x49,0x90,0x4b,0x49,0x60,0x89]) := by
  decide +kernel

section Fips197Spec

/-! ### A FIPS-197 specification, independent of the production tables and control flow

Nothing in `namespace Spec` refers to the production code or to the GF(2^8) lemmas above. Section and figure
numbers are those of FIPS-197 as published in 2001. The trusted part is reading these definitions against the
standard: everything after them is proved. The note at the end of this section says what is not covered. -/

namespace Spec

/-! Section 4: a byte is the polynomial whose coefficient of `x^i` is bit `i`; addition is xor. -/

/-- The product of two polynomials over GF(2) (section 4.2); only bytes are ever multiplied, so `b` has
degree at most 7. -/
def polyMul (a b : Nat) : Nat :=
  (List.range 8).foldl (fun acc i => if b.testBit i then acc ^^^ (a <<< i) else acc) 0

/-- The remainder modulo `m(x) = x^8 + x^4 + x^3 + x + 1` (`0x11b`) by long division, from `x^14` down. -/
def polyMod (p : Nat) : Nat :=
  (List.range 7).foldr (fun i rem => if rem.testBit (i + 8) then rem ^^^ (0x11b <<< i) else rem) p

/-- Multiplication in GF(2^8), section 4.2. -/
def gfMul (a b : Nat) : Nat := polyMod (polyMul a b)

/-- `a^n` in GF(2^8). -/
def gfPow (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => gfMul a (gfPow a n)

/-- The multiplicative inverse (section 4.2), by search; `{00}` has none and maps to itself (section 5.1.1). -/
def gfInv (a : Nat) : Nat := ((List.range 256).find? fun b => gfMul a b == 1).getD 0

/-- The affine transformation of section 5.1.1, with `c = {63}`. -/
def affine (b : Nat) : Nat :=
  (List.range 8).foldl (fun acc i =>
    let bit := b.testBit i ^^ b.testBit ((i + 4) % 8) ^^ b.testBit ((i + 5) % 8) ^^
      b.testBit ((i + 6) % 8) ^^ b.testBit ((i + 7) % 8) ^^ (0x63 : Nat).testBit i
    acc + if bit then 2 ^ i else 0) 0

/-- The S-box, section 5.1.1: the inverse in GF(2^8), then the affine transformation. -/
def sboxByte (a : Nat) : Nat := affine (gfInv a)

/-- The inverse S-box, section 5.3.2: the byte the S-box sends to `b`. -/
def invSboxByte (b : Nat) : Nat := ((List.range 256).find? fun a => decide (sboxByte a = b)).getD 0

/-- Section 3.4: the state `s[r,c]`. -/
abbrev State := Fin 4 → Fin 4 → UInt8

/-- Section 3.4: `s[r,c] = in[r + 4c]`. -/
def stateOf (input : List UInt8) : State := fun r c => input[r.val + 4 * c.val]!

/-- Section 3.4: `out[r + 4c] = s[r,c]`. -/
def blockOf (s : State) : List UInt8 :=
  [s 0 0, s 1 0, s 2 0, s 3 0, s 0 1, s 1 1, s 2 1, s 3 1, s 0 2, s 1 2, s 2 2, s 3 2, s 0 3, s 1 3, s 2 3, s 3 3]

/-- SubBytes, section 5.1.1. -/
def subBytes (s : State) : State := fun r c => UInt8.ofNat (sboxByte (s r c).toNat)

/-- InvSubBytes, section 5.3.2. -/
def invSubBytes (s : State) : State := fun r c => UInt8.ofNat (invSboxByte (s r c).toNat)

/-- ShiftRows, section 5.1.2: `s'[r,c] = s[r, (c + r) mod 4]`; `Fin 4` arithmetic is modulo 4. -/
def shiftRows (s : State) : State := fun r c => s r (c + r)

/-- InvShiftRows, section 5.3.1: `s'[r, (c + r) mod 4] = s[r,c]`. -/
def invShiftRows (s : State) : State := fun r c => s r (c - r)

/-- `s'[r,c] = ⊕ i, M[r,i] • s[i,c]`, the matrix product over GF(2^8) applied to each column. -/
def mulMatrix (m : Fin 4 → Fin 4 → Nat) (s : State) : State := fun r c =>
  UInt8.ofNat (gfMul (m r 0) (s 0 c).toNat ^^^ gfMul (m r 1) (s 1 c).toNat ^^^
    gfMul (m r 2) (s 2 c).toNat ^^^ gfMul (m r 3) (s 3 c).toNat)

/-- Reads a 4x4 matrix written row by row. -/
def matrix (rows : List (List Nat)) : Fin 4 → Fin 4 → Nat := fun r c => rows[r.val]![c.val]!

/-- MixColumns, section 5.1.3. -/
def mixColumns : State → State :=
  mulMatrix (matrix
    [[0x02, 0x03, 0x01, 0x01],
     [0x01, 0x02, 0x03, 0x01],
     [0x01, 0x01, 0x02, 0x03],
     [0x03, 0x01, 0x01, 0x02]])

/-- InvMixColumns, section 5.3.3. -/
def invMixColumns : State → State :=
  mulMatrix (matrix
    [[0x0e, 0x0b, 0x0d, 0x09],
     [0x09, 0x0e, 0x0b, 0x0d],
     [0x0d, 0x09, 0x0e, 0x0b],
     [0x0b, 0x0d, 0x09, 0x0e]])

/-- A key-schedule word `[a0, a1, a2, a3]`. -/
abbrev Word := Fin 4 → UInt8

def xorWord (a b : Word) : Word := fun i => a i ^^^ b i

/-- RotWord, section 5.2: `[a0, a1, a2, a3]` to `[a1, a2, a3, a0]`. -/
def rotWord (a : Word) : Word := fun i => a (i + 1)

/-- SubWord, section 5.2. -/
def subWord (a : Word) : Word := fun i => UInt8.ofNat (sboxByte (a i).toNat)

/-- `Rcon[i] = [x^(i-1), {00}, {00}, {00}]`, section 5.2. -/
def rcon (i : Nat) : Word := fun j => if j = 0 then UInt8.ofNat (gfPow 2 (i - 1)) else 0

/-- `word(key[4i], key[4i+1], key[4i+2], key[4i+3])`. -/
def keyWord (key : List UInt8) (i : Nat) : Word := fun j => key[4 * i + j.val]!

/-- KeyExpansion, section 5.2, Figure 11: the words `w[0], ..., w[n-1]`. -/
def keyExpansion (key : List UInt8) (nk : Nat) : Nat → List Word
  | 0 => []
  | i + 1 =>
    let w := keyExpansion key nk i
    w ++ [if i < nk then keyWord key i
      else
        let temp := w[i - 1]!
        let temp :=
          if i % nk = 0 then xorWord (subWord (rotWord temp)) (rcon (i / nk))
          else if nk > 6 ∧ i % nk = 4 then subWord temp
          else temp
        xorWord w[i - nk]! temp]

/-- AddRoundKey, section 5.1.4: column `c` is xored with `w[round * Nb + c]`. -/
def addRoundKey (w : List Word) (round : Nat) (s : State) : State :=
  fun r c => s r c ^^^ w[round * 4 + c.val]! r

/-- The rounds `1, ..., n` of Cipher (section 5.1, Figure 5), ascending. -/
def cipherRounds (w : List Word) : Nat → State → State
  | 0, s => s
  | n + 1, s => addRoundKey w (n + 1) (mixColumns (shiftRows (subBytes (cipherRounds w n s))))

/-- The rounds `n, ..., 1` of InvCipher (section 5.3, Figure 12), descending. -/
def invCipherRounds (w : List Word) : Nat → State → State
  | 0, s => s
  | n + 1, s => invCipherRounds w n (invMixColumns (addRoundKey w (n + 1) (invSubBytes (invShiftRows s))))

/-- `Nk`. -/
def Nk (key : ByteArray) : Nat := key.size / 4

/-- `Nr = Nk + 6`, section 5. -/
def Nr (key : ByteArray) : Nat := Nk key + 6

/-- The whole schedule: `w[0], ..., w[Nb * (Nr + 1) - 1]`. -/
def schedule (key : ByteArray) : List Word := keyExpansion key.toList (Nk key) (4 * (Nr key + 1))

end Spec

/-- Cipher, FIPS-197 section 5.1, Figure 5. -/
def specCipher (key input : ByteArray) : ByteArray :=
  let w := Spec.schedule key
  let nr := Spec.Nr key
  let state := Spec.stateOf input.toList
  let state := Spec.addRoundKey w 0 state
  let state := Spec.cipherRounds w (nr - 1) state
  let state := Spec.subBytes state
  let state := Spec.shiftRows state
  let state := Spec.addRoundKey w nr state
  ByteArray.mk (Spec.blockOf state).toArray

/-- InvCipher, FIPS-197 section 5.3, Figure 12. -/
def specInvCipher (key input : ByteArray) : ByteArray :=
  let w := Spec.schedule key
  let nr := Spec.Nr key
  let state := Spec.stateOf input.toList
  let state := Spec.addRoundKey w nr state
  let state := Spec.invCipherRounds w (nr - 1) state
  let state := Spec.invShiftRows state
  let state := Spec.invSubBytes state
  let state := Spec.addRoundKey w 0 state
  ByteArray.mk (Spec.blockOf state).toArray

/-! The field: the polynomial product is bilinear, so eight basis vectors settle it against `multiply`. -/

namespace Spec

private theorem polyMod_xor (p q : Nat) : polyMod (p ^^^ q) = polyMod p ^^^ polyMod q := by
  simp only [polyMod]
  generalize List.range 7 = l
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, ih, Nat.testBit_xor]
    generalize l.foldr _ p = x
    generalize l.foldr _ q = y
    cases hx : x.testBit (i + 8) <;> cases hy : y.testBit (i + 8) <;> simp <;> ac_nf
    simp

private theorem polyMul_left_foldl (a a' b r r' : Nat) (l : List Nat) :
    l.foldl (fun acc i => if b.testBit i then acc ^^^ ((a ^^^ a') <<< i) else acc) (r ^^^ r') =
      l.foldl (fun acc i => if b.testBit i then acc ^^^ (a <<< i) else acc) r ^^^
        l.foldl (fun acc i => if b.testBit i then acc ^^^ (a' <<< i) else acc) r' := by
  induction l generalizing r r' with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    split
    · rw [Nat.shiftLeft_xor_distrib]; ac_rfl
    · rfl

private theorem polyMul_right_foldl (a b b' r r' : Nat) (l : List Nat) :
    l.foldl (fun acc i => if (b ^^^ b').testBit i then acc ^^^ (a <<< i) else acc) (r ^^^ r') =
      l.foldl (fun acc i => if b.testBit i then acc ^^^ (a <<< i) else acc) r ^^^
        l.foldl (fun acc i => if b'.testBit i then acc ^^^ (a <<< i) else acc) r' := by
  induction l generalizing r r' with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    congr 1
    simp only [Nat.testBit_xor]
    cases b.testBit i <;> cases b'.testBit i <;> simp
    · ac_rfl
    · ac_rfl
    · generalize a <<< i = x
      have : r ^^^ x ^^^ (r' ^^^ x) = r ^^^ r' ^^^ (x ^^^ x) := by ac_rfl
      simp [this]

theorem gfMul_left_xor (a a' b : Nat) : gfMul (a ^^^ a') b = gfMul a b ^^^ gfMul a' b := by
  simp only [gfMul, polyMul]
  rw [← polyMod_xor, ← polyMul_left_foldl, Nat.xor_self]

theorem gfMul_right_xor (a b b' : Nat) : gfMul a (b ^^^ b') = gfMul a b ^^^ gfMul a b' := by
  simp only [gfMul, polyMul]
  rw [← polyMod_xor, ← polyMul_right_foldl, Nat.xor_self]

end Spec

private theorem gfMul_basis :
    ∀ i j : Fin 8, Spec.gfMul (2 ^ i.val) (2 ^ j.val) = multiply (2 ^ i.val) (2 ^ j.val) := by
  decide +kernel

/-- The specification's polynomial product is the multiplication proved a field operation above. -/
theorem gfMul_eq_multiply {a b : Nat} (ha : a < 256) (hb : b < 256) : Spec.gfMul a b = multiply a b := by
  have zero_l : ∀ b, Spec.gfMul 0 b = 0 := fun b => by
    have := Spec.gfMul_left_xor 0 0 b
    simpa using this
  have zero_r : ∀ a, Spec.gfMul a 0 = 0 := fun a => by
    have := Spec.gfMul_right_xor a 0 0
    simpa using this
  refine byte_induction (P := fun a => Spec.gfMul a b = multiply a b) ?_ ?_ ?_ ha
  · rw [zero_l, multiply_zero_left ⟨b, hb⟩]
  · intro i
    refine byte_induction (P := fun b => Spec.gfMul (2 ^ i.val) b = multiply (2 ^ i.val) b) ?_ ?_ ?_ hb
    · rw [zero_r, multiply_zero_right ⟨_, pow_two_lt i⟩]
    · exact gfMul_basis i
    · intro x y _ _ ix iy
      rw [Spec.gfMul_right_xor, multiply_right_xor, ix, iy]
  · intro x y hx hy ix iy
    rw [Spec.gfMul_left_xor, multiply_left_xor _ hx hy, ix, iy]

/-- The inverse of the affine transformation (bits `i+2`, `i+5`, `i+7`, with `c = {05}`); used only to
compute the witness of `sbox_table`, so that table costs one product per byte instead of a search. -/
private def affineInv (b : Nat) : Nat :=
  (List.range 8).foldl (fun acc i =>
    let bit := b.testBit ((i + 2) % 8) ^^ b.testBit ((i + 5) % 8) ^^ b.testBit ((i + 7) % 8) ^^
      (0x05 : Nat).testBit i
    acc + if bit then 2 ^ i else 0) 0

/-- The S-box table is the affine image of a byte whose product with the index is one. -/
private theorem sbox_table : ∀ a : Fin 256,
    let t := affineInv (sbox[a.val]!).toNat
    t < 256 ∧ Spec.affine t = (sbox[a.val]!).toNat ∧ (a.val = 0 ∧ t = 0 ∨ multiply a.val t = 1) := by
  decide +kernel

theorem gfInv_zero : Spec.gfInv 0 = 0 := by decide +kernel

/-- Inverses are unique, so the search of `gfInv` finds the witness. -/
private theorem gfInv_eq {a t : Nat} (ha : a < 256) (ht : t < 256) (h : multiply a t = 1) :
    Spec.gfInv a = t := by
  have hmem : t ∈ List.range 256 := List.mem_range.mpr ht
  have hp : (Spec.gfMul a t == 1) = true := by rw [gfMul_eq_multiply ha ht, h]; rfl
  have hsome := List.find?_isSome (p := fun b => Spec.gfMul a b == 1) (xs := List.range 256) |>.mpr ⟨t, hmem, hp⟩
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp hsome
  have hb1 := List.find?_some hb
  have hbm := List.mem_range.mp (List.mem_of_find?_eq_some hb)
  simp only [beq_iff_eq] at hb1
  rw [gfMul_eq_multiply ha hbm] at hb1
  have e1 := multiply_assoc ht ha hbm
  have e2 := multiply_comm ht ha
  rw [e2, h, multiply_one_left hbm, hb1] at e1
  rw [Spec.gfInv, hb]
  have := multiply_one_right ⟨t, ht⟩
  simp only at this
  simp only [Option.getD_some]
  omega

/-- The S-box of section 5.1.1 is the production table, on every byte. -/
theorem sboxByte_eq_sbox {a : Nat} (ha : a < 256) : Spec.sboxByte a = (sbox[a]!).toNat := by
  obtain ⟨hlt, haff, hinv⟩ := sbox_table ⟨a, ha⟩
  simp only at hlt haff hinv
  rw [Spec.sboxByte, ← haff]
  rcases hinv with ⟨rfl, ht⟩ | h
  · rw [gfInv_zero, ht]
  · rw [gfInv_eq ha hlt h]

/-- `a • inv(a) = 1` for the inverse the specification searches for. -/
theorem gfMul_gfInv {a : Nat} (ha : a < 256) (h : a ≠ 0) : Spec.gfMul a (Spec.gfInv a) = 1 := by
  have hi := gfInverse_lt ⟨a, ha⟩
  have hu := multiply_gfInverse ⟨a, ha⟩ h
  simp only at hi hu
  rw [gfInv_eq ha hi hu, gfMul_eq_multiply ha hi, hu]

/-- InvSubBytes' inverse S-box is the production `inverseSbox`. -/
theorem invSboxByte_eq {b : UInt8} : UInt8.ofNat (Spec.invSboxByte b.toNat) = inverseSbox[b.toNat]! := by
  have hb := b.toNat_lt
  have hl : inverseSbox.length = 256 := by decide +kernel
  rw [getElem!_pos inverseSbox b.toNat (by rw [hl]; exact hb)]
  simp only [inverseSbox_eq_search, List.getElem_map, List.getElem_range, Spec.invSboxByte]
  have hcong : (List.range 256).find? (fun a => decide (Spec.sboxByte a = b.toNat)) =
      (List.range 256).find? (fun index => decide ((sbox[index]!).toNat = b.toNat)) := by
    have gen : ∀ l : List Nat, (∀ a ∈ l, a < 256) → l.find? (fun a => decide (Spec.sboxByte a = b.toNat)) =
        l.find? (fun index => decide ((sbox[index]!).toNat = b.toNat)) := by
      intro l
      induction l with
      | nil => intro _; rfl
      | cons a l ih =>
        intro h
        simp only [List.find?_cons, sboxByte_eq_sbox (h a (by simp)), ih fun x hx => h x (by simp [hx])]
    exact gen _ fun a ha => List.mem_range.mp ha
  rw [hcong]
  cases (List.range 256).find? _ <;> rfl

theorem sboxByte_lt {a : Nat} (ha : a < 256) : Spec.sboxByte a < 256 := by
  rw [sboxByte_eq_sbox ha]; exact UInt8.toNat_lt _

/-- InvSubBytes undoes SubBytes, and conversely, on the specification's own definitions. -/
theorem invSboxByte_sboxByte (b : UInt8) :
    UInt8.ofNat (Spec.invSboxByte (UInt8.ofNat (Spec.sboxByte b.toNat)).toNat) = b := by
  rw [invSboxByte_eq, sboxByte_eq_sbox b.toNat_lt]
  simpa using inverseSbox_sbox b

theorem sboxByte_invSboxByte (b : UInt8) :
    UInt8.ofNat (Spec.sboxByte (UInt8.ofNat (Spec.invSboxByte b.toNat)).toNat) = b := by
  rw [invSboxByte_eq, sboxByte_eq_sbox (UInt8.toNat_lt _)]
  simpa using sbox_inverseSbox b

theorem gfMul_lt {a b : Nat} (ha : a < 256) (hb : b < 256) : Spec.gfMul a b < 256 := by
  rw [gfMul_eq_multiply ha hb]; exact multiply_lt b ha

theorem gfMul_comm {a b : Nat} (ha : a < 256) (hb : b < 256) : Spec.gfMul a b = Spec.gfMul b a := by
  rw [gfMul_eq_multiply ha hb, gfMul_eq_multiply hb ha, multiply_comm ha hb]

theorem gfMul_assoc {a b c : Nat} (ha : a < 256) (hb : b < 256) (hc : c < 256) :
    Spec.gfMul (Spec.gfMul a b) c = Spec.gfMul a (Spec.gfMul b c) := by
  rw [gfMul_eq_multiply ha hb, gfMul_eq_multiply (multiply_lt b ha) hc, gfMul_eq_multiply hb hc,
    gfMul_eq_multiply ha (multiply_lt c hb), multiply_assoc ha hb hc]

/-! Examples printed in the standard, checked on the specification and not on production: section 4.2's
product, `x^8 = x^4 + x^3 + x + 1`, and the S-box entry of section 5.1.1. -/

theorem fips197_gfMul_example : Spec.gfMul 0x57 0x83 = 0xc1 := by decide +kernel
theorem fips197_reduction : Spec.gfMul 0x02 0x80 = 0x1b := by decide +kernel
theorem fips197_sbox_example : Spec.sboxByte 0x53 = 0xed := by decide +kernel

/-! The state, the round transformations and the key schedule, against the production list code. -/

open Spec (blockOf stateOf keyExpansion Word keyWord xorWord subWord rotWord rcon gfPow gfMul)

/-- A word, as the four bytes the production code holds. -/
def wordList (w : Word) : List UInt8 := [w 0, w 1, w 2, w 3]

private theorem xorByte_eq (a b : UInt8) : xorByte a b = a ^^^ b := by
  rw [xorByte, ← UInt8.toNat_xor, UInt8.ofNat_toNat]

private theorem sbox_eq (b : UInt8) : sbox[b.toNat]! = UInt8.ofNat (Spec.sboxByte b.toNat) := by
  rw [sboxByte_eq_sbox b.toNat_lt, UInt8.ofNat_toNat]

theorem blockOf_stateOf {l : List UInt8} (h : l.length = 16) : blockOf (stateOf l) = l := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := eq_literal16 h
  rfl

theorem length_blockOf (s : Spec.State) : (blockOf s).length = 16 := rfl

theorem addRoundKey_blockOf (s k : Spec.State) :
    addRoundKey (blockOf s) (blockOf k) = blockOf fun r c => s r c ^^^ k r c := by
  simp [addRoundKey, blockOf, xorByte_eq]

theorem inverseShiftRows_blockOf (s : Spec.State) :
    inverseShiftRows (blockOf s) = blockOf (Spec.invShiftRows s) := rfl

theorem shiftRows_blockOf (s : Spec.State) : shiftRows (blockOf s) = blockOf (Spec.shiftRows s) := rfl

theorem substitute_inverseSbox_blockOf (s : Spec.State) :
    substitute inverseSbox (blockOf s) = blockOf (Spec.invSubBytes s) := by
  simp [substitute, blockOf, Spec.invSubBytes, invSboxByte_eq]

theorem substitute_sbox_blockOf (s : Spec.State) :
    substitute sbox (blockOf s) = blockOf (Spec.subBytes s) := by
  simp only [substitute, blockOf, List.map_cons, List.map_nil, sbox_eq]
  rfl

private theorem mulMatrix_eq {m : Fin 4 → Fin 4 → Nat} (hm : ∀ r c, m r c < 256) (s : Spec.State) :
    Spec.mulMatrix m s = fun r c => UInt8.ofNat (multiply (s 0 c).toNat (m r 0) ^^^ multiply (s 1 c).toNat (m r 1) ^^^
      multiply (s 2 c).toNat (m r 2) ^^^ multiply (s 3 c).toNat (m r 3)) := by
  funext r c
  simp only [Spec.mulMatrix]
  rw [gfMul_eq_multiply (hm _ _) (UInt8.toNat_lt _), gfMul_eq_multiply (hm _ _) (UInt8.toNat_lt _),
    gfMul_eq_multiply (hm _ _) (UInt8.toNat_lt _), gfMul_eq_multiply (hm _ _) (UInt8.toNat_lt _),
    multiply_comm (hm _ _) (UInt8.toNat_lt _), multiply_comm (hm _ _) (UInt8.toNat_lt _),
    multiply_comm (hm _ _) (UInt8.toNat_lt _), multiply_comm (hm _ _) (UInt8.toNat_lt _)]

theorem inverseMixColumns_blockOf (s : Spec.State) :
    inverseMixColumns (blockOf s) = blockOf (Spec.invMixColumns s) := by
  rw [Spec.invMixColumns, mulMatrix_eq (by decide)]
  rfl

theorem mixColumns_blockOf (s : Spec.State) : mixColumns (blockOf s) = blockOf (Spec.mixColumns s) := by
  rw [Spec.mixColumns, mulMatrix_eq (by decide)]
  rfl

/-! The key schedule. -/

private theorem multiply_two : ∀ v : Fin 256, multiply v.val 2 = xtime v.val := by decide +kernel

private theorem gfMul_two {v : Nat} (hv : v < 256) : gfMul 2 v = xtime v := by
  rw [gfMul_eq_multiply (by decide) hv, multiply_comm (by decide) hv]
  exact multiply_two ⟨v, hv⟩

private theorem gfPow_two_lt (n : Nat) : gfPow 2 n < 256 := by
  cases n with
  | zero => decide
  | succ n =>
    have ih := gfPow_two_lt n
    simp only [gfPow]
    rw [gfMul_two ih]
    exact xtime_lt _

/-- `Rcon` as powers of `x` is the production's repeated `xtime`. -/
theorem roundConstant_eq (j : Nat) : roundConstant j = UInt8.ofNat (gfPow 2 (j - 1)) := by
  simp only [roundConstant]
  generalize j - 1 = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih]
    simp only [List.foldl_cons, List.foldl_nil, gfPow]
    rw [gfMul_two (gfPow_two_lt n), UInt8.toNat_ofNat_of_lt' (gfPow_two_lt n)]

theorem length_keyExpansion (key : List UInt8) (nk n : Nat) : (keyExpansion key nk n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [keyExpansion, ih]

private theorem getBang_map_wordList {ws : List Word} {i : Nat} (h : i < ws.length) :
    (ws.map wordList)[i]! = wordList ws[i]! := by
  rw [getElem!_pos (ws.map wordList) i (by simpa using h), getElem!_pos ws i h]
  simp

private theorem expand_step (w : List Word) (nk i : Nat) (hlo : nk ≤ i) (hnk : 0 < nk) (hlen : w.length = i) :
    addRoundKey (w.map wordList)[i - nk]!
        (if i % nk = 0 then
          match substitute sbox (rotateWord (w.map wordList)[i - 1]!) with
          | first :: rest => xorByte first (roundConstant (i / nk)) :: rest
          | [] => []
        else if (decide (nk > 6) && decide (i % nk = 4)) = true then substitute sbox (w.map wordList)[i - 1]!
        else (w.map wordList)[i - 1]!) =
      wordList (xorWord w[i - nk]!
        (if i % nk = 0 then xorWord (subWord (rotWord w[i - 1]!)) (rcon (i / nk))
        else if nk > 6 ∧ i % nk = 4 then subWord w[i - 1]!
        else w[i - 1]!)) := by
  rw [getBang_map_wordList (by omega), getBang_map_wordList (by omega)]
  generalize w[i - nk]! = src
  generalize w[i - 1]! = p
  by_cases h0 : i % nk = 0
  · simp only [h0, ite_true, rotateWord, wordList, substitute, List.map_cons, List.map_nil, sbox_eq]
    simp [addRoundKey, xorByte_eq, roundConstant_eq, xorWord, subWord, rotWord, rcon]
  · by_cases h4 : nk > 6 ∧ i % nk = 4
    · simp only [h4, wordList, substitute, List.map_cons, List.map_nil, sbox_eq]
      simp [addRoundKey, xorByte_eq, xorWord, subWord]
    · have h4' : ¬ (decide (nk > 6) && decide (i % nk = 4)) = true := by simpa using h4
      simp only [h0, h4, h4', ite_false]
      simp [wordList, addRoundKey, xorByte_eq, xorWord]

private theorem expandLoop_eq (key : List UInt8) (nk wc i : Nat) (hnk : 0 < nk) (hi : nk ≤ i) :
    expandKey.loop nk wc i ((keyExpansion key nk i).map wordList) =
      (keyExpansion key nk (max i wc)).map wordList := by
  induction hm : wc - i generalizing i with
  | zero =>
    rw [expandKey.loop, ite_eq_left (by omega), show max i wc = i by omega]
  | succ m ih =>
    rw [expandKey.loop, ite_eq_right (by omega)]
    simp only
    rw [show max i wc = max (i + 1) wc by omega, ← ih (i + 1) (by omega) (by omega)]
    have hlo : ¬ i < nk := by omega
    simp only [keyExpansion, List.map_append, List.map_cons, List.map_nil, hlo, ite_false]
    exact congrArg (fun x => expandKey.loop nk wc (i + 1) ((keyExpansion key nk i).map wordList ++ [x]))
      (expand_step _ nk i hi hnk (length_keyExpansion ..))

private theorem extract4 (l : List UInt8) (n : Nat) (h : n + 4 ≤ l.length) :
    l.extract n (n + 4) = [l[n]!, l[n + 1]!, l[n + 2]!, l[n + 3]!] := by
  induction n generalizing l with
  | zero =>
    match l, h with
    | a :: b :: c :: d :: _, _ => rfl
  | succ n ih =>
    match l, h with
    | a :: t, h =>
      have := ih t (by simpa [Nat.add_right_comm] using h)
      simp only [List.extract_eq_take_drop] at this ⊢
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

private theorem keyExpansion_prefix (key : List UInt8) (nk n : Nat) (hn : n ≤ nk) :
    keyExpansion key nk n = (List.range n).map (keyWord key) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, ← ih (by omega)]
    simp [keyExpansion, show n < nk by omega]

private theorem init_words {key : List UInt8} {nk : Nat} (hk : key.length = nk * 4) :
    ((List.range nk).map fun i => key.extract (i * 4) (i * 4 + 4)) = (keyExpansion key nk nk).map wordList := by
  rw [keyExpansion_prefix key nk nk (Nat.le_refl _), List.map_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have : i * 4 + 4 ≤ key.length := by rw [hk]; exact (Nat.succ_mul i 4).symm ▸ Nat.mul_le_mul_right 4 hi'
  rw [extract4 _ _ this]
  simp only [Function.comp, wordList, keyWord, Nat.mul_comm 4 i]
  rfl

/-- Production's key expansion is the words of section 5.2, flattened. -/
theorem expandKey_eq {key : ByteArray} (hk : ValidKeyLength key.size) :
    expandKey key.toList = .ok (Spec.Nr key, ((Spec.schedule key).map wordList).flatten) := by
  have hlen := length_toList key
  rw [expandKey, ite_eq_right (by rw [hlen]; rcases hk with h | h | h <;> simp [h])]
  simp only [hlen]
  have hnk : 0 < key.size / 4 := by rcases hk with h | h | h <;> omega
  have hmul : key.toList.length = key.size / 4 * 4 := by rcases hk with h | h | h <;> omega
  rw [init_words hmul, expandLoop_eq _ _ _ _ hnk (Nat.le_refl _),
    show max (key.size / 4) (4 * (key.size / 4 + 6 + 1)) = 4 * (key.size / 4 + 6 + 1) by omega]
  rfl

private theorem take_drop_flatten (ws : List Word) (k : Nat) (h : k + 4 ≤ ws.length) :
    (((ws.map wordList).flatten).drop (k * 4)).take 16 =
      wordList ws[k]! ++ wordList ws[k + 1]! ++ wordList ws[k + 2]! ++ wordList ws[k + 3]! := by
  induction k generalizing ws with
  | zero =>
    match ws, h with
    | a :: b :: c :: d :: _, _ => rfl
  | succ k ih =>
    match ws, h with
    | a :: t, h =>
      rw [Nat.succ_mul]
      exact ih t (by simpa [Nat.add_right_comm] using h)

/-- A round key of the flattened schedule is the state of section 5.1.4's four words, by column. -/
theorem roundKey_eq {ws : List Word} {r rounds : Nat} (hlen : ws.length = 4 * (rounds + 1)) (hr : r ≤ rounds) :
    ((ws.map wordList).flatten).extract (r * 16) (r * 16 + 16) =
      blockOf fun i c => ws[r * 4 + c.val]! i := by
  have hk : r * 4 + 4 ≤ ws.length := by rw [hlen]; omega
  have := take_drop_flatten ws (r * 4) hk
  rw [List.extract_eq_take_drop, show r * 16 + 16 - r * 16 = 16 by omega, show r * 16 = r * 4 * 4 by omega, this]
  rfl

theorem addRoundKey_roundKey {ws : List Word} {r rounds : Nat} (hlen : ws.length = 4 * (rounds + 1))
    (hr : r ≤ rounds) (s : Spec.State) :
    addRoundKey (blockOf s) (((ws.map wordList).flatten).extract (r * 16) (r * 16 + 16)) =
      blockOf (Spec.addRoundKey ws r s) := by
  rw [roundKey_eq hlen hr, addRoundKey_blockOf]
  rfl

/-! The composition: `decryptBlock` is InvCipher and `encryptBlock` is Cipher. -/

private theorem length_schedule (key : ByteArray) : (Spec.schedule key).length = 4 * (Spec.Nr key + 1) :=
  length_keyExpansion ..

private theorem decryptLoop_eq {ws : List Word} {rounds : Nat} (hlen : ws.length = 4 * (rounds + 1))
    (r : Nat) (hr : r ≤ rounds) (s : Spec.State) :
    decryptBlock.loop ((ws.map wordList).flatten) r (blockOf s) = blockOf (Spec.invCipherRounds ws r s) := by
  induction r generalizing s with
  | zero => rw [decryptBlock.loop]; rfl
  | succ r ih =>
    rw [decryptBlock.loop, ite_eq_right (by simp)]
    simp only [Nat.add_sub_cancel]
    rw [inverseShiftRows_blockOf, substitute_inverseSbox_blockOf, addRoundKey_roundKey hlen hr,
      inverseMixColumns_blockOf, ih (by omega)]
    rfl

private theorem encryptLoop_eq {ws : List Word} {rounds : Nat} (hlen : ws.length = 4 * (rounds + 1))
    (r : Nat) (hr : r ≤ rounds) (s : Spec.State) :
    encryptLoop ((ws.map wordList).flatten) r (blockOf s) = blockOf (Spec.cipherRounds ws r s) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [encryptLoop, Spec.cipherRounds]
    rw [ih (by omega), substitute_sbox_blockOf, shiftRows_blockOf, mixColumns_blockOf,
      addRoundKey_roundKey hlen hr]

/-- **`decryptBlock` is FIPS-197 InvCipher**, for every 16, 24 or 32 byte key and every 16 byte block. -/
theorem decryptBlock_eq_specInvCipher {key input : ByteArray} (hk : ValidKeyLength key.size)
    (hs : input.size = 16) : decryptBlock key input = .ok (specInvCipher key input) := by
  have hlen := length_schedule key
  have hin : input.toList.length = 16 := by rw [length_toList, hs]
  rw [decryptBlock_eq hs (expandKey_eq hk)]
  conv => lhs; rw [← blockOf_stateOf hin]
  rw [addRoundKey_roundKey hlen (Nat.le_refl _), decryptLoop_eq hlen _ (by omega), inverseShiftRows_blockOf,
    substitute_inverseSbox_blockOf, addRoundKey_roundKey (r := 0) hlen (Nat.zero_le _)]
  rfl

/-- **`encryptBlock` is FIPS-197 Cipher**, for every 16, 24 or 32 byte key and every 16 byte block. -/
theorem encryptBlock_eq_specCipher {key input : ByteArray} (hk : ValidKeyLength key.size)
    (hs : input.size = 16) : encryptBlock key input = .ok (specCipher key input) := by
  have hlen := length_schedule key
  have hin : input.toList.length = 16 := by rw [length_toList, hs]
  rw [encryptBlock_eq hs (expandKey_eq hk)]
  conv => lhs; rw [← blockOf_stateOf hin]
  rw [addRoundKey_roundKey (r := 0) hlen (Nat.zero_le _), encryptLoop_eq hlen _ (by omega),
    substitute_sbox_blockOf, shiftRows_blockOf, addRoundKey_roundKey hlen (Nat.le_refl _)]
  rfl

theorem size_specCipher (key input : ByteArray) : (specCipher key input).size = 16 := rfl
theorem size_specInvCipher (key input : ByteArray) : (specInvCipher key input).size = 16 := rfl

/-- InvCipher undoes Cipher (FIPS-197 section 5.3), on the specification's own terms. -/
theorem specInvCipher_specCipher {key plain : ByteArray} (hk : ValidKeyLength key.size) (hp : plain.size = 16) :
    specInvCipher key (specCipher key plain) = plain := by
  obtain ⟨c, he, _, hd⟩ := decryptBlock_encryptBlock hk hp
  rw [encryptBlock_eq_specCipher hk hp] at he
  cases he
  rw [decryptBlock_eq_specInvCipher hk (size_specCipher ..)] at hd
  exact Except.ok.inj hd

/-- Cipher undoes InvCipher. -/
theorem specCipher_specInvCipher {key cipher : ByteArray} (hk : ValidKeyLength key.size)
    (hc : cipher.size = 16) : specCipher key (specInvCipher key cipher) = cipher := by
  have hd := decryptBlock_eq_specInvCipher hk hc
  have he := encryptBlock_decryptBlock hd
  rw [encryptBlock_eq_specCipher hk (size_specInvCipher ..)] at he
  exact Except.ok.inj he

/-- `Nr = Nk + 6` gives the round counts of section 5, Figure 4. -/
theorem Nr_values (key : ByteArray) :
    (key.size = 16 → Spec.Nr key = 10) ∧ (key.size = 24 → Spec.Nr key = 12) ∧ (key.size = 32 → Spec.Nr key = 14) := by
  simp only [Spec.Nr, Spec.Nk]
  omega

private theorem specInvCipher_of_decrypt {key c p : ByteArray} (hk : ValidKeyLength key.size) (hc : c.size = 16)
    (h : (decryptBlock key c).toOption = some p) : specInvCipher key c = p := by
  rw [decryptBlock_eq_specInvCipher hk hc] at h
  simpa [Except.toOption] using h

private theorem specCipher_of_encrypt {key p c : ByteArray} (hk : ValidKeyLength key.size) (hp : p.size = 16)
    (h : (encryptBlock key p).toOption = some c) : specCipher key p = c := by
  rw [encryptBlock_eq_specCipher hk hp] at h
  simpa [Except.toOption] using h

/-! The specification itself reproduces Appendix C, without being evaluated: these follow from the general
theorems and the kernel-checked vectors above. -/

theorem fips197_aes128_specInvCipher :
    specInvCipher (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15])
      (ByteArray.mk #[0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a]) =
    ByteArray.mk fipsPlain.toArray :=
  specInvCipher_of_decrypt (by decide) rfl fips197_aes128_decrypt

theorem fips197_aes192_specInvCipher :
    specInvCipher (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23])
      (ByteArray.mk #[0xdd,0xa9,0x7c,0xa4,0x86,0x4c,0xdf,0xe0,0x6e,0xaf,0x70,0xa0,0xec,0x0d,0x71,0x91]) =
    ByteArray.mk fipsPlain.toArray :=
  specInvCipher_of_decrypt (by decide) rfl fips197_aes192_decrypt

theorem fips197_aes256_specInvCipher :
    specInvCipher (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31])
      (ByteArray.mk #[0x8e,0xa2,0xb7,0xca,0x51,0x67,0x45,0xbf,0xea,0xfc,0x49,0x90,0x4b,0x49,0x60,0x89]) =
    ByteArray.mk fipsPlain.toArray :=
  specInvCipher_of_decrypt (by decide) rfl fips197_aes256_decrypt

theorem fips197_aes128_specCipher :
    specCipher (ByteArray.mk #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15]) (ByteArray.mk fipsPlain.toArray) =
    ByteArray.mk #[0x69,0xc4,0xe0,0xd8,0x6a,0x7b,0x04,0x30,0xd8,0xcd,0xb7,0x80,0x70,0xb4,0xc5,0x5a] :=
  specCipher_of_encrypt (by decide) rfl fips197_aes128_encrypt

/-! What the theorems above do and do not establish.

* They are functional correctness of the Lean definitions: `decryptBlock` computes the same function as
  `specInvCipher` on every 16, 24 or 32 byte key and every 16 byte block. The other inputs are rejected
  (`decryptBlock_ok_iff`), and the specification says nothing about them.
* `Spec` is Lean, not the standard. That it says what FIPS-197 says is checked only by reading it; the
  correspondence is helped by the printed examples and Appendix C vectors above, but not proved. So are the
  modelling choices: `Nb = 4` is fixed, bytes are `UInt8` and field elements the `Nat` below 256, words are
  functions on `Fin 4`, the schedule is a list built in order, and `Rcon` is read at `i / Nk`.
* No statement about timing, cache behaviour or any other side channel. Production's table lookups and list
  indexing depend on secret bytes, and it is not constant-time. Nothing is said about key erasure either.
* No statement about AES as a cipher (its security), or about any mode of operation.
* The trusted base includes the Lean kernel, and for the running program the compiler and runtime: the proofs
  are about the definitions, not the generated code.
* The forward cipher `encryptBlock` lives in this file, not in production: production has no encryption to
  verify. RFC 3394 wrap is the same, see `wrap_eq_specWrap` below. -/

end Fips197Spec

/-! ### RFC 3394 key unwrap -/

open KeyWrap (unwrap unwrap.round unwrap.round.item)
open_private_decls Bap.Crypto.KeyWrap Bap.Crypto.KeyWrap defaultIv tBytes xorT replaceAt
open_private_decls Bap.Crypto.KeyWrap Bap.Crypto KeyWrap.xorByte

theorem length_tBytes (t : Nat) : (tBytes t).length = 8 := by simp [tBytes]

theorem length_xorT (a : List UInt8) (t : Nat) : (xorT a t).length = min a.length 8 := by
  simp [xorT, length_tBytes]

private theorem keyWrapXor_cancel (a k : UInt8) : KeyWrap.xorByte (KeyWrap.xorByte a k) k = a := by
  have hlt : a.toNat ^^^ k.toNat < 2 ^ 8 := Nat.xor_lt_two_pow a.toNat_lt k.toNat_lt
  simp only [KeyWrap.xorByte, UInt8.toNat_ofNat', Nat.mod_eq_of_lt hlt, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  exact UInt8.ofNat_toNat

/-- XORing the same 64-bit counter twice cancels out. -/
theorem xorT_cancel {a : List UInt8} (t : Nat) (h : a.length ≤ 8) : xorT (xorT a t) t = a := by
  have gen : ∀ (a k : List UInt8), a.length ≤ k.length →
      (((a.zip k).map fun p => KeyWrap.xorByte p.1 p.2).zip k).map (fun p => KeyWrap.xorByte p.1 p.2) = a := by
    intro a
    induction a with
    | nil => intro k _; rfl
    | cons x a ih =>
      intro k hk
      cases k with
      | nil => simp at hk
      | cons y k =>
        simp only [List.zip_cons_cons, List.map_cons]
        rw [keyWrapXor_cancel, ih k (by simpa using hk)]
  exact gen a (tBytes t) (by rwa [length_tBytes])

theorem length_replaceAt (r : List (List UInt8)) (i : Nat) (v : List UInt8) :
    (replaceAt r i v).length = r.length := by
  simp [replaceAt]

private theorem bang_eq (l : List (List UInt8)) {i : Nat} (h : i < l.length) : l[i]! = l[i] :=
  getElem!_pos l i h

private theorem getElem_replaceAt (r : List (List UInt8)) (i : Nat) (v : List UInt8) (j : Nat)
    (hj : j < r.length) : (replaceAt r i v)[j]! = if j = i then v else r[j]! := by
  have : j < (replaceAt r i v).length := by rwa [length_replaceAt]
  rw [bang_eq _ this]
  simp [replaceAt]

theorem getBang_replaceAt_self {r : List (List UInt8)} {i : Nat} (v : List UInt8) (hi : i < r.length) :
    (replaceAt r i v)[i]! = v := by
  rw [getElem_replaceAt _ _ _ _ hi]; simp

/-- Restoring the overwritten slot restores the register file. -/
theorem replaceAt_restore {r : List (List UInt8)} {i : Nat} (v : List UInt8) (hi : i < r.length) :
    replaceAt (replaceAt r i v) i r[i]! = r := by
  have hlen : (replaceAt (replaceAt r i v) i r[i]!).length = r.length := by
    simp only [length_replaceAt]
  apply List.ext_getElem hlen
  intro j h1 h2
  have e := getElem_replaceAt (replaceAt r i v) i r[i]! j (by rwa [length_replaceAt])
  rw [bang_eq _ h1] at e
  rw [e]
  split
  · next h => subst h; rw [bang_eq _ h2]
  · next h => rw [getElem_replaceAt _ _ _ _ h2, ite_eq_right h, bang_eq _ h2]

/-- Well-formed unwrap state: an 8-byte integrity register and `n` 8-byte registers. -/
def GoodState (n : Nat) (s : List UInt8 × List (List UInt8)) : Prop :=
  s.1.length = 8 ∧ s.2.length = n ∧ ∀ x ∈ s.2, x.length = 8

private theorem good_getBang {n i : Nat} {s : List UInt8 × List (List UInt8)} (h : GoodState n s)
    (hi : i < n) : s.2[i]!.length = 8 := by
  have hi' : i < s.2.length := by rw [h.2.1]; exact hi
  rw [bang_eq _ hi']; exact h.2.2 _ (List.getElem_mem hi')

private theorem good_step {n i : Nat} {r : List (List UInt8)} (bytes : List UInt8)
    (hbytes : bytes.length = 16) (hr : r.length = n) (hg : ∀ x ∈ r, x.length = 8) :
    GoodState n (bytes.take 8, replaceAt r i (bytes.drop 8)) := by
  refine ⟨by simp [hbytes], by rw [length_replaceAt, hr], ?_⟩
  intro x hx
  simp only [replaceAt, List.mem_map, List.mem_range] at hx
  obtain ⟨j, hj, rfl⟩ := hx
  split
  · simp [hbytes]
  · rw [bang_eq _ (by simpa [length_replaceAt] using hj)]; exact hg _ (List.getElem_mem _)

/-- A decrypted block is 16 bytes, so `item` preserves the shape of the state. -/
theorem item_good {key : ByteArray} {n j : Nat} (i : Nat) {s s' : List UInt8 × List (List UInt8)}
    (hs : GoodState n s) (h : unwrap.round.item key n j i s.1 s.2 = .ok s') : GoodState n s' := by
  induction i generalizing s with
  | zero =>
    rw [unwrap.round.item] at h
    generalize hd : decryptBlock _ _ = res at h
    cases res with
    | error e => cases h
    | ok d =>
      simp only [bind, Except.bind, ↓reduceIte] at h
      cases h
      exact good_step d.toList (by rw [length_toList, decryptBlock_ok_size hd]) hs.2.1 hs.2.2
  | succ i ih =>
    rw [unwrap.round.item] at h
    generalize hd : decryptBlock _ _ = res at h
    cases res with
    | error e => cases h
    | ok d =>
      simp only [bind, Except.bind] at h
      rw [ite_eq_right (by simp)] at h
      exact ih (s := (_, _)) (good_step d.toList (by rw [length_toList, decryptBlock_ok_size hd])
        hs.2.1 hs.2.2) h

theorem round_good {key : ByteArray} {n : Nat} (remaining j : Nat) {s s' : List UInt8 × List (List UInt8)}
    (hs : GoodState n s) (h : unwrap.round key n remaining j s.1 s.2 = .ok s') : GoodState n s' := by
  induction remaining generalizing j s with
  | zero =>
    rw [unwrap.round] at h
    simp at h; subst h; exact hs
  | succ remaining ih =>
    rw [unwrap.round, ite_eq_right (by simp)] at h
    cases hi : unwrap.round.item key n j (n - 1) s.1 s.2 with
    | error e => simp [hi, bind, Except.bind] at h
    | ok next =>
      have hnext := item_good _ hs hi
      simp only [hi, bind, Except.bind] at h
      split at h
      · cases h; exact hnext
      · simpa using ih (j - 1) hnext (by simpa using h)

/-- Register parsing: split a list into `m` chunks of eight. -/
def chunks (m : Nat) (l : List UInt8) : List (List UInt8) :=
  (List.range m).map fun i => (l.drop (i * 8)).take 8

private theorem chunks_succ (m : Nat) (l : List UInt8) :
    chunks (m + 1) l = l.take 8 :: chunks m (l.drop 8) := by
  simp only [chunks, List.range_succ_eq_map, List.map_cons, List.map_map]
  simp only [Nat.zero_mul, List.drop_zero, List.cons.injEq, true_and]
  apply List.map_congr_left
  intro i _
  simp only [Function.comp, List.drop_drop]
  congr 2
  omega

private theorem flatten_chunks (m : Nat) {l : List UInt8} (h : l.length = m * 8) :
    (chunks m l).flatten = l := by
  induction m generalizing l with
  | zero => simp at h; subst h; rfl
  | succ m ih =>
    rw [chunks_succ, List.flatten_cons, ih (by simp [h]; omega), List.take_append_drop]

private theorem good_chunks (m : Nat) {l : List UInt8} (h : l.length = m * 8) :
    (chunks m l).length = m ∧ ∀ x ∈ chunks m l, x.length = 8 := by
  refine ⟨by simp [chunks], ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
  have hi' := List.mem_range.mp hi
  have : (i + 1) * 8 ≤ m * 8 := Nat.mul_le_mul_right 8 hi'
  simp [h]
  omega

private theorem chunks_flatten (r : List (List UInt8)) (h : ∀ x ∈ r, x.length = 8) :
    chunks r.length r.flatten = r := by
  induction r with
  | nil => rfl
  | cons x r ih =>
    have hx := h x (by simp)
    rw [List.length_cons, chunks_succ, List.flatten_cons,
      List.take_left' hx, List.drop_left' hx, ih fun y hy => h y (by simp [hy])]

/-! The forward direction (RFC 3394 section 2.2.1), which the production code does not implement. -/

def wrapItem (key : ByteArray) (n j i : Nat) (s : List UInt8 × List (List UInt8)) :
    Except String (List UInt8 × List (List UInt8)) := do
  let cipher ← encryptBlock key (ByteArray.mk (s.1 ++ s.2[i]!).toArray)
  .ok (xorT (cipher.toList.take 8) (n * j + i + 1), replaceAt s.2 i (cipher.toList.drop 8))

def wrapPass (key : ByteArray) (n j : Nat) :
    Nat → List UInt8 × List (List UInt8) → Except String (List UInt8 × List (List UInt8))
  | 0, s => .ok s
  | i + 1, s => do wrapItem key n j i (← wrapPass key n j i s)

def wrapRounds (key : ByteArray) (n : Nat) :
    Nat → List UInt8 × List (List UInt8) → Except String (List UInt8 × List (List UInt8))
  | 0, s => .ok s
  | j + 1, s => do wrapPass key n j n (← wrapRounds key n j s)

/-- RFC 3394 wrap under an arbitrary initial value. -/
def wrapWithIv (key : ByteArray) (iv : List UInt8) (plain : ByteArray) : Except String ByteArray := do
  let n := plain.size / 8
  let (a, r) ← wrapRounds key n 6 (iv, chunks n plain.toList)
  .ok (ByteArray.mk (a ++ r.flatten).toArray)

/-- RFC 3394 wrap with the default initial value. -/
def wrap (key plain : ByteArray) : Except String ByteArray := wrapWithIv key defaultIv plain

private theorem unwrap_step {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (j : Nat) {i : Nat}
    (hi : i < n) {s : List UInt8 × List (List UInt8)} (hs : GoodState n s) :
    ∃ s', wrapItem key n j i s = .ok s' ∧ GoodState n s' ∧
      unwrap.round.item key n j i s'.1 s'.2 =
        if i = 0 then .ok s else unwrap.round.item key n j (i - 1) s.1 s.2 := by
  have hreg := good_getBang hs hi
  have hsize : (ByteArray.mk (s.1 ++ s.2[i]!).toArray).size = 16 := by
    rw [size_mk, List.length_append, hs.1, hreg]
  obtain ⟨c, he, hc, hd⟩ := decryptBlock_encryptBlock hk hsize
  have hclen : c.toList.length = 16 := by rw [length_toList, hc]
  have hilt : i < s.2.length := by rw [hs.2.1]; exact hi
  refine ⟨_, by simp only [wrapItem, he]; rfl, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp [length_xorT, hclen]
    · simp only [length_replaceAt]; exact hs.2.1
    · exact (good_step (i := i) c.toList hclen hs.2.1 hs.2.2).2.2
  · rw [unwrap.round.item]
    simp only
    rw [xorT_cancel _ (by simp [hclen]), getBang_replaceAt_self _ hilt, List.take_append_drop, mk_toList, hd]
    simp only [bind, Except.bind, toList_mk]
    rw [List.take_left' hs.1, List.drop_left' hs.1, replaceAt_restore _ hilt]

private theorem unwrap_pass {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (j : Nat)
    (k : Nat) (hk' : k ≤ n) {s : List UInt8 × List (List UInt8)} (hs : GoodState n s) :
    ∃ s', wrapPass key n j k s = .ok s' ∧ GoodState n s' ∧ (k = 0 → s' = s) ∧
      ∀ i, k = i + 1 → unwrap.round.item key n j i s'.1 s'.2 = .ok s := by
  induction k with
  | zero => exact ⟨s, rfl, hs, fun _ => rfl, fun _ h => by cases h⟩
  | succ k ih =>
    obtain ⟨s1, h1, g1, z1, u1⟩ := ih (by omega)
    obtain ⟨s2, h2, g2, u2⟩ := unwrap_step hk j (i := k) (by omega) g1
    refine ⟨s2, ?_, g2, by simp, ?_⟩
    · simp only [wrapPass, h1, bind, Except.bind]; exact h2
    · intro i hi
      have : i = k := by omega
      subst this
      rw [u2]
      cases i with
      | zero => simp [z1 rfl]
      | succ i => simpa using u1 i rfl

private theorem unwrap_rounds {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (hn : 0 < n)
    (m : Nat) {s : List UInt8 × List (List UInt8)} (hs : GoodState n s) :
    ∃ s', wrapRounds key n (m + 1) s = .ok s' ∧ GoodState n s' ∧
      unwrap.round key n (m + 1) m s'.1 s'.2 = .ok s := by
  have pass : ∀ j {s : List UInt8 × List (List UInt8)}, GoodState n s →
      ∃ s', wrapPass key n j n s = .ok s' ∧ GoodState n s' ∧
        unwrap.round.item key n j (n - 1) s'.1 s'.2 = .ok s := by
    intro j s hs
    obtain ⟨s', h, g, _, u⟩ := unwrap_pass hk j n (Nat.le_refl _) hs
    exact ⟨s', h, g, u _ (by omega)⟩
  induction m with
  | zero =>
    obtain ⟨s', h, g, u⟩ := pass 0 hs
    refine ⟨s', ?_, g, ?_⟩
    · simp only [wrapRounds, bind, Except.bind]; exact h
    · rw [unwrap.round, ite_eq_right (by simp), u]; rfl
  | succ m ih =>
    obtain ⟨s1, h1, g1, u1⟩ := ih
    obtain ⟨s2, h2, g2, u2⟩ := pass (m + 1) g1
    refine ⟨s2, ?_, g2, ?_⟩
    · rw [wrapRounds, h1]; exact h2
    · rw [unwrap.round, ite_eq_right (by simp), u2]
      simpa [bind, Except.bind] using u1

private theorem wrap_parse {key iv : ByteArray} {plain : ByteArray} (hk : ValidKeyLength key.size)
    (hiv : iv.toList.length = 8) (hp : plain.size % 8 = 0) (hp16 : 16 ≤ plain.size) :
    ∃ cipher, wrapWithIv key iv.toList plain = .ok cipher ∧ cipher.size = plain.size + 8 ∧
      (cipher.size / 8 - 1 = plain.size / 8) ∧
      unwrap.round key (plain.size / 8) 6 5 (cipher.toList.take 8)
        ((List.range (plain.size / 8)).map fun index => (cipher.toList.drop (8 + index * 8)).take 8) =
          .ok (iv.toList, chunks (plain.size / 8) plain.toList) := by
  have hlen : plain.toList.length = plain.size / 8 * 8 := by rw [length_toList]; omega
  obtain ⟨hc1, hc2⟩ := good_chunks (plain.size / 8) hlen
  obtain ⟨⟨a, r⟩, hw, hg, hu⟩ := unwrap_rounds hk (n := plain.size / 8) (by omega) 5
    (s := (iv.toList, chunks (plain.size / 8) plain.toList)) ⟨hiv, hc1, hc2⟩
  have hflat : r.flatten.length = plain.size := by
    have := chunks_flatten r hg.2.2
    have h2 : ∀ (rr : List (List UInt8)), (∀ x ∈ rr, x.length = 8) → rr.flatten.length = rr.length * 8 := by
      intro rr
      induction rr with
      | nil => intro _; rfl
      | cons x rr ih =>
        intro h
        simp only [List.flatten_cons, List.length_append, List.length_cons]
        rw [h x (by simp), ih fun y hy => h y (by simp [hy])]
        omega
    rw [h2 r hg.2.2, hg.2.1]; omega
  have ha : a.length = 8 := hg.1
  refine ⟨ByteArray.mk (a ++ r.flatten).toArray, ?_, ?_, ?_, ?_⟩
  · simp only [wrapWithIv]
    show (do let __x ← wrapRounds key (plain.size / 8) (5 + 1) _; _) = _
    rw [hw]; rfl
  · rw [size_mk, List.length_append, ha, hflat]; omega
  · rw [size_mk, List.length_append, ha, hflat]; omega
  · rw [toList_mk, List.take_left' ha]
    have hparse : ((List.range (plain.size / 8)).map fun index =>
        ((a ++ r.flatten).drop (8 + index * 8)).take 8) = r := by
      have := chunks_flatten r hg.2.2
      rw [hg.2.1] at this
      conv => rhs; rw [← this]
      simp only [chunks]
      apply List.map_congr_left
      intro i _
      rw [← List.drop_drop, List.drop_left' ha]
    rw [hparse]
    exact hu

/-- A blob is rejected unless it is at least 24 bytes long. -/
theorem unwrap_rejects_short (key : ByteArray) {input : ByteArray} (h : input.size < 24) :
    unwrap key input = .error "RFC 3394 input must be at least 24 bytes and 8-byte aligned" := by
  rw [unwrap, ite_eq_left (by simp [h])]

/-- A blob is rejected unless it is a whole number of 64-bit blocks. -/
theorem unwrap_rejects_unaligned (key : ByteArray) {input : ByteArray} (h : input.size % 8 ≠ 0) :
    unwrap key input = .error "RFC 3394 input must be at least 24 bytes and 8-byte aligned" := by
  rw [unwrap, ite_eq_left (by simp [h])]

private theorem item_bad_key {key : ByteArray} (hk : ¬ ValidKeyLength key.size) (n j i : Nat) (a) (r) :
    ∃ msg, unwrap.round.item key n j i a r = .error msg := by
  rw [unwrap.round.item]
  generalize ByteArray.mk _ = block
  by_cases hs : block.size = 16
  · rw [decryptBlock_bad_key hs hk]; exact ⟨_, rfl⟩
  · rw [decryptBlock_bad_block key hs]; exact ⟨_, rfl⟩

/-- A KEK that is not 128, 192 or 256 bits is never accepted. -/
theorem unwrap_rejects_bad_key {key : ByteArray} (hk : ¬ ValidKeyLength key.size) (input : ByteArray) :
    ∃ msg, unwrap key input = .error msg := by
  by_cases hbad : input.size < 24 ∨ input.size % 8 ≠ 0
  · rcases hbad with h | h
    · exact ⟨_, unwrap_rejects_short key h⟩
    · exact ⟨_, unwrap_rejects_unaligned key h⟩
  · rw [unwrap, ite_eq_right (by simpa using hbad)]
    simp only
    rw [unwrap.round, ite_eq_right (by simp)]
    obtain ⟨msg, h⟩ := item_bad_key hk (input.size / 8 - 1) 5 (input.size / 8 - 1 - 1)
      (input.toList.take 8) ((List.range (input.size / 8 - 1)).map fun index =>
        (input.toList.drop (8 + index * 8)).take 8)
    exact ⟨msg, by rw [h]; rfl⟩

/-- Success means the integrity register came out as the default IV, and the output is the
registers: the integrity check cannot be skipped. -/
theorem unwrap_ok_iff {key input out : ByteArray} :
    unwrap key input = .ok out ↔
      ¬ (input.size < 24 ∨ input.size % 8 ≠ 0) ∧ ∃ r,
        unwrap.round key (input.size / 8 - 1) 6 5 (input.toList.take 8)
          ((List.range (input.size / 8 - 1)).map fun index => (input.toList.drop (8 + index * 8)).take 8) =
            .ok (defaultIv, r) ∧ out = ByteArray.mk r.flatten.toArray := by
  by_cases hbad : input.size < 24 ∨ input.size % 8 ≠ 0
  · simp only [hbad, not_true_eq_false, false_and, iff_false]
    rcases hbad with h | h
    · rw [unwrap_rejects_short key h]; simp
    · rw [unwrap_rejects_unaligned key h]; simp
  · simp only [hbad, not_false_eq_true, true_and]
    rw [unwrap, ite_eq_right (by simpa using hbad)]
    simp only
    cases hr : unwrap.round key (input.size / 8 - 1) 6 5 (input.toList.take 8)
        ((List.range (input.size / 8 - 1)).map fun index => (input.toList.drop (8 + index * 8)).take 8) with
    | error e => simp [bind, Except.bind]
    | ok st =>
      obtain ⟨a, r⟩ := st
      simp only [bind, Except.bind]
      by_cases ha : a = defaultIv
      · subst ha
        simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, Except.ok.injEq, Prod.mk.injEq, true_and]
        constructor
        · intro h; exact ⟨r, rfl, h.symm⟩
        · rintro ⟨r', rfl, rfl⟩; rfl
      · have : (a != defaultIv) = true := by simpa using ha
        simp only [this, ite_true]
        constructor
        · intro h; cases h
        · rintro ⟨r', h, _⟩; cases h; exact absurd rfl ha

/-- A wrong final integrity register is reported as such, whatever the registers contain. -/
theorem unwrap_integrity_failure {key input : ByteArray} {a : List UInt8} {r : List (List UInt8)}
    (hbad : ¬ (input.size < 24 ∨ input.size % 8 ≠ 0))
    (hr : unwrap.round key (input.size / 8 - 1) 6 5 (input.toList.take 8)
        ((List.range (input.size / 8 - 1)).map fun index => (input.toList.drop (8 + index * 8)).take 8) =
          .ok (a, r))
    (ha : a ≠ defaultIv) :
    unwrap key input = .error "RFC 3394 integrity check failed" := by
  rw [unwrap, ite_eq_right (by simpa using hbad)]
  simp only [hr, bind, Except.bind]
  rw [ite_eq_left (by simpa using ha)]

/-- Unwrapping removes exactly the 8-byte integrity register, from a valid blob and a valid KEK. -/
theorem unwrap_ok_size {key input out : ByteArray} (h : unwrap key input = .ok out) :
    out.size + 8 = input.size ∧ ValidKeyLength key.size := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hbad, r, hr, rfl⟩ := unwrap_ok_iff.mp h
    have hsize : 24 ≤ input.size ∧ input.size % 8 = 0 := by omega
    have hdata : input.toList.length = input.size := length_toList _
    have hrest : (input.toList.drop 8).length = (input.size / 8 - 1) * 8 := by
      simp [hdata]; omega
    obtain ⟨hc1, hc2⟩ := good_chunks (input.size / 8 - 1) hrest
    have hg := round_good (n := input.size / 8 - 1) 6 5
      (s := (input.toList.take 8, chunks (input.size / 8 - 1) (input.toList.drop 8)))
      ⟨by simp [hdata]; omega, hc1, hc2⟩
      (by
        simpa [chunks, List.drop_drop] using hr)
    have h2 : ∀ (rr : List (List UInt8)), (∀ x ∈ rr, x.length = 8) → rr.flatten.length = rr.length * 8 := by
      intro rr
      induction rr with
      | nil => intro _; rfl
      | cons x rr ih =>
        intro h
        simp only [List.flatten_cons, List.length_append, List.length_cons]
        rw [h x (by simp), ih fun y hy => h y (by simp [hy])]
        omega
    rw [size_mk, h2 r hg.2.2, hg.2.1]
    omega
  · by_cases hk : ValidKeyLength key.size
    · exact hk
    · obtain ⟨msg, h'⟩ := unwrap_rejects_bad_key hk input
      rw [h] at h'; cases h'

/-- Unwrap inverts wrap for every valid KEK and every multiple-of-8 key of at least 16 bytes. -/
theorem unwrap_wrap {key plain : ByteArray} (hk : ValidKeyLength key.size)
    (hp : plain.size % 8 = 0) (hp16 : 16 ≤ plain.size) :
    ∃ cipher, wrap key plain = .ok cipher ∧ cipher.size = plain.size + 8 ∧
      unwrap key cipher = .ok plain := by
  have hivEq : (ByteArray.mk defaultIv.toArray).toList = defaultIv := toList_mk _
  have hiv : (ByteArray.mk defaultIv.toArray).toList.length = 8 := by rw [hivEq]; rfl
  obtain ⟨c, hw, hs, hn, hr⟩ := wrap_parse (iv := ByteArray.mk defaultIv.toArray) hk hiv hp hp16
  rw [hivEq] at hw hr
  refine ⟨c, hw, hs, unwrap_ok_iff.mpr ⟨by omega, chunks (plain.size / 8) plain.toList, ?_, ?_⟩⟩
  · rw [hn]; exact hr
  · have hlen : plain.toList.length = plain.size / 8 * 8 := by rw [length_toList]; omega
    rw [flatten_chunks _ hlen, mk_toList]

/-- A blob wrapped under a different initial value is rejected by the integrity check. -/
theorem unwrap_rejects_wrong_iv {key plain : ByteArray} {iv : List UInt8} (hk : ValidKeyLength key.size)
    (hiv : iv.length = 8) (hne : iv ≠ defaultIv) (hp : plain.size % 8 = 0) (hp16 : 16 ≤ plain.size) :
    ∃ cipher, wrapWithIv key iv plain = .ok cipher ∧
      unwrap key cipher = .error "RFC 3394 integrity check failed" := by
  have hivEq : (ByteArray.mk iv.toArray).toList = iv := toList_mk _
  obtain ⟨c, hw, hs, hn, hr⟩ := wrap_parse (iv := ByteArray.mk iv.toArray) hk (by rw [hivEq]; exact hiv) hp hp16
  rw [hivEq] at hw hr
  refine ⟨c, hw, unwrap_integrity_failure (by omega) (r := chunks (plain.size / 8) plain.toList) ?_ hne⟩
  rw [hn]; exact hr

/-! RFC 3394 section 4 vectors, checked by the kernel. -/

theorem rfc3394_unwrap_128_128 :
    (unwrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f])
      (ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5])).toOption =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) := by
  decide +kernel

theorem rfc3394_unwrap_192_128 :
    (unwrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17])
      (ByteArray.mk #[0x96,0x77,0x8b,0x25,0xae,0x6c,0xa4,0x35,0xf9,0x2b,0x5b,0x97,0xc0,0x50,0xae,0xd2,0x46,0x8a,0xb8,0xa1,0x7a,0xd8,0x4e,0x5d])).toOption =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) := by
  decide +kernel

theorem rfc3394_unwrap_256_128 :
    (unwrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17,0x18,0x19,0x1a,0x1b,0x1c,0x1d,0x1e,0x1f])
      (ByteArray.mk #[0x64,0xe8,0xc3,0xf9,0xce,0x0f,0x5b,0xa2,0x63,0xe9,0x77,0x79,0x05,0x81,0x8a,0x2a,0x93,0xc8,0x19,0x1e,0x7d,0x6e,0x8a,0xe7])).toOption =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) := by
  decide +kernel

theorem rfc3394_wrap_128_128 :
    (wrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f])
      (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff])).toOption =
    some (ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5]) := by
  decide +kernel

/-! ### An RFC 3394 specification, in the words of its section 2.2

Registers here are 64-bit numbers and the block cipher is FIPS-197's `specCipher` and `specInvCipher` above, so nothing is
shared with the list-of-lists state and counter arithmetic of `unwrap` and `wrap`. -/

namespace Rfc3394

/-- A 64-bit value as its bytes, most significant first (section 2: the MSB is the first octet). -/
def toBytes (w : BitVec 64) : List UInt8 :=
  (List.range 8).map fun i => UInt8.ofNat (w.toNat / 256 ^ (7 - i) % 256)

/-- Eight bytes, most significant first, as a 64-bit value. -/
def ofBytes (l : List UInt8) : BitVec 64 :=
  BitVec.ofNat 64 (l.foldl (fun value byte => value * 256 + byte.toNat) 0)

/-- `A6A6A6A6A6A6A6A6`, the default initial value of section 2.2.3.1. -/
def iv : BitVec 64 := 0xA6A6A6A6A6A6A6A6#64

/-- The block `A | B`. -/
def join (a b : BitVec 64) : ByteArray := ByteArray.mk (toBytes a ++ toBytes b).toArray

/-- `MSB(64, B)`. -/
def msb (b : ByteArray) : BitVec 64 := ofBytes (b.toList.take 8)

/-- `LSB(64, B)`. -/
def lsb (b : ByteArray) : BitVec 64 := ofBytes (b.toList.drop 8)

/-- The integrity register `A`, and the registers `R[i]` for `i ≥ 1`. -/
structure State where
  A : BitVec 64
  R : Nat → BitVec 64

/-- `R[i] := value`. -/
def setR (R : Nat → BitVec 64) (i : Nat) (value : BitVec 64) : Nat → BitVec 64 := fun k => if k = i then value else R k

/-- The body of the loop of section 2.2.1 for `t = n*j + i`:
`B = AES(K, A | R[i])`, `A = MSB(64, B) ^ t`, `R[i] = LSB(64, B)`. -/
def wrapStep (key : ByteArray) (n j i : Nat) (s : State) : State :=
  let b := specCipher key (join s.A (s.R i))
  ⟨msb b ^^^ BitVec.ofNat 64 (n * j + i), setR s.R i (lsb b)⟩

/-- `For i = 1 to k`. -/
def wrapInner (key : ByteArray) (n j : Nat) : Nat → State → State
  | 0, s => s
  | i + 1, s => wrapStep key n j (i + 1) (wrapInner key n j i s)

/-- `For j = 0 to m - 1`, with `i` to `n` inside. -/
def wrapOuter (key : ByteArray) (n : Nat) : Nat → State → State
  | 0, s => s
  | j + 1, s => wrapInner key n j n (wrapOuter key n j s)

/-- The body of the loop of section 2.2.2 for `t = n*j + i`:
`B = AES-1(K, (A ^ t) | R[i])`, `A = MSB(64, B)`, `R[i] = LSB(64, B)`. -/
def unwrapStep (key : ByteArray) (n j i : Nat) (s : State) : State :=
  let b := specInvCipher key (join (s.A ^^^ BitVec.ofNat 64 (n * j + i)) (s.R i))
  ⟨msb b, setR s.R i (lsb b)⟩

/-- `For i = k to 1`. -/
def unwrapInner (key : ByteArray) (n j : Nat) : Nat → State → State
  | 0, s => s
  | i + 1, s => unwrapInner key n j i (unwrapStep key n j (i + 1) s)

/-- `For j = m - 1 to 0`, with `i` from `n` inside. -/
def unwrapOuter (key : ByteArray) (n : Nat) : Nat → State → State
  | 0, s => s
  | j + 1, s => unwrapOuter key n j (unwrapInner key n j n s)

/-- The 64-bit block number `i` of some data. -/
def block (data : ByteArray) (i : Nat) : BitVec 64 := ofBytes ((data.toList.drop (8 * i)).take 8)

/-- The registers `R[1]` to `R[n]`, in order. -/
def registers (R : Nat → BitVec 64) (n : Nat) : List UInt8 := (List.range n).flatMap fun k => toBytes (R (k + 1))

/-- Section 2.2.1 with the default initial value: `P[1..n]` is wrapped into `C[0] = A`, `C[i] = R[i]`. -/
def specWrap (key plain : ByteArray) : ByteArray :=
  let n := plain.size / 8
  let s := wrapOuter key n 6 ⟨iv, fun i => block plain (i - 1)⟩
  ByteArray.mk (toBytes s.A ++ registers s.R n).toArray

/-- Section 2.2.2 and the check of section 2.2.3.1: `C[0..n]` is unwrapped into `P[i] = R[i]` if `A` is the initial value. -/
def specUnwrap (key input : ByteArray) : Option ByteArray :=
  let n := input.size / 8 - 1
  let s := unwrapOuter key n 6 ⟨block input 0, fun i => block input i⟩
  if s.A = iv then some (ByteArray.mk (registers s.R n).toArray) else none

end Rfc3394

namespace Rfc3394

/-- The last `n` bytes of a number, most significant first. -/
private def digits : Nat → Nat → List UInt8
  | 0, _ => []
  | n + 1, x => digits n (x / 256) ++ [UInt8.ofNat (x % 256)]

private theorem length_digits (n x : Nat) : (digits n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [digits, ih]

private theorem range_digits (x : Nat) :
    (List.range 8).map (fun i => UInt8.ofNat (x / 256 ^ (7 - i) % 256)) = digits 8 x := by
  simp [digits, show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, Nat.div_div_eq_div_mul]

private theorem toBytes_eq_digits (w : BitVec 64) : toBytes w = digits 8 w.toNat := range_digits _

private theorem foldl_digits (n x : Nat) :
    (digits n x).foldl (fun value byte => value * 256 + byte.toNat) 0 = x % 256 ^ n := by
  induction n generalizing x with
  | zero => simp [digits, Nat.mod_one]
  | succ n ih =>
    simp only [digits, List.foldl_append, ih, List.foldl_cons, List.foldl_nil, UInt8.toNat_ofNat']
    rw [show (2 : Nat) ^ 8 = 256 from rfl, Nat.mod_mod, show (256 : Nat) ^ (n + 1) = 256 * 256 ^ n from Nat.pow_succ',
      Nat.mod_mul, Nat.mul_comm, Nat.add_comm]

private theorem digits_foldl_reverse (l : List UInt8) :
    digits l.length (l.reverse.foldl (fun value byte => value * 256 + byte.toNat) 0) = l.reverse := by
  induction l with
  | nil => rfl
  | cons b l ih =>
    simp only [List.reverse_cons, List.length_cons, List.foldl_append, List.foldl_cons, List.foldl_nil, digits]
    have hb := b.toNat_lt
    generalize l.reverse.foldl (fun value byte => value * 256 + byte.toNat) 0 = v at ih
    rw [show (v * 256 + b.toNat) / 256 = v by omega, show (v * 256 + b.toNat) % 256 = b.toNat by omega, ih,
      UInt8.ofNat_toNat]

private theorem digits_foldl (l : List UInt8) :
    digits l.length (l.foldl (fun value byte => value * 256 + byte.toNat) 0) = l := by
  have := digits_foldl_reverse l.reverse
  simpa using this

private theorem digits_mod (n x : Nat) : digits n (x % 256 ^ n) = digits n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [digits]
    have hpow : 256 ^ (n + 1) = 256 * 256 ^ n := Nat.pow_succ'
    have h1 : x % 256 ^ (n + 1) / 256 = x / 256 % 256 ^ n := by
      rw [hpow, Nat.mod_mul_right_div_self]
    have h2 : x % 256 ^ (n + 1) % 256 = x % 256 := by
      rw [hpow, Nat.mod_mul_right_mod]
    rw [h1, h2, ih]

private theorem digits_xor (n a t : Nat) :
    ((digits n a).zip (digits n t)).map (fun pair => KeyWrap.xorByte pair.1 pair.2) = digits n (a ^^^ t) := by
  induction n generalizing a t with
  | zero => rfl
  | succ n ih =>
    simp only [digits]
    rw [List.zip_append (by rw [length_digits, length_digits]), List.map_append, ih]
    have h1 : (a ^^^ t) / 256 = a / 256 ^^^ t / 256 := Nat.xor_div_two_pow (n := 8)
    have h2 : (a ^^^ t) % 256 = a % 256 ^^^ t % 256 := Nat.xor_mod_two_pow (n := 8)
    have ha : a % 256 < 256 := Nat.mod_lt _ (by decide)
    have ht : t % 256 < 256 := Nat.mod_lt _ (by decide)
    rw [h1, h2]
    simp [KeyWrap.xorByte]

theorem length_toBytes (w : BitVec 64) : (toBytes w).length = 8 := by simp [toBytes]

/-- A value is what its bytes put together say. -/
theorem ofBytes_toBytes (w : BitVec 64) : ofBytes (toBytes w) = w := by
  apply BitVec.eq_of_toNat_eq
  rw [ofBytes, toBytes_eq_digits, foldl_digits, BitVec.toNat_ofNat, Nat.mod_mod_of_dvd _ (by decide)]
  exact Nat.mod_eq_of_lt w.isLt

/-- Eight bytes are what the value they put together says. -/
theorem toBytes_ofBytes {l : List UInt8} (h : l.length = 8) : toBytes (ofBytes l) = l := by
  rw [toBytes_eq_digits, ofBytes, BitVec.toNat_ofNat]
  have := digits_mod 8 (l.foldl (fun value byte => value * 256 + byte.toNat) 0)
  rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide] at this
  rw [this]
  have := digits_foldl l
  rwa [h] at this

/-- XOR with the counter, byte by byte, is the XOR of the 64-bit values. -/
theorem xorT_toBytes (a : BitVec 64) (t : Nat) : xorT (toBytes a) t = toBytes (a ^^^ BitVec.ofNat 64 t) := by
  rw [xorT, show tBytes t = digits 8 t from range_digits t, toBytes_eq_digits, toBytes_eq_digits, digits_xor, BitVec.toNat_xor, BitVec.toNat_ofNat,
    ← digits_mod 8 (a.toNat ^^^ t % 2 ^ 64), ← digits_mod 8 (a.toNat ^^^ t)]
  rw [show (256 : Nat) ^ 8 = 2 ^ 64 by decide, Nat.xor_mod_two_pow, Nat.xor_mod_two_pow, Nat.mod_mod]

theorem toBytes_iv : toBytes iv = defaultIv := by decide

/-- The state of the list code and that of the specification say the same. -/
def Rel (n : Nat) (a : List UInt8) (r : List (List UInt8)) (s : State) : Prop :=
  a = toBytes s.A ∧ r.length = n ∧ ∀ k, k < n → r[k]! = toBytes (s.R (k + 1))

private theorem take_msb {d : ByteArray} (hd : d.size = 16) : d.toList.take 8 = toBytes (msb d) := by
  rw [msb, toBytes_ofBytes (by simp [length_toList, hd])]

private theorem drop_lsb {d : ByteArray} (hd : d.size = 16) : d.toList.drop 8 = toBytes (lsb d) := by
  rw [lsb, toBytes_ofBytes (by simp [length_toList, hd])]

private theorem Rel.step {n i : Nat} {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s)
    {d : ByteArray} (hd : d.size = 16) {final : BitVec 64} {a' : List UInt8} (ha : a' = toBytes final) :
    Rel n a' (replaceAt r i (d.toList.drop 8)) ⟨final, setR s.R (i + 1) (lsb d)⟩ := by
  refine ⟨ha, by rw [length_replaceAt, h.2.1], fun k hk => ?_⟩
  rw [getElem_replaceAt _ _ _ _ (by rw [h.2.1]; exact hk)]
  simp only [setR, Nat.add_right_cancel_iff]
  split
  · exact drop_lsb hd
  · exact h.2.2 k hk

private theorem Rel.block_eq {n i : Nat} {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s)
    (hi : i < n) (t : Nat) : ByteArray.mk (xorT a t ++ r[i]!).toArray = join (s.A ^^^ BitVec.ofNat 64 t) (s.R (i + 1)) := by
  rw [h.1, h.2.2 i hi, xorT_toBytes, join]

private theorem Rel.block_eq' {n i : Nat} {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s)
    (hi : i < n) : ByteArray.mk (a ++ r[i]!).toArray = join s.A (s.R (i + 1)) := by
  rw [h.1, h.2.2 i hi, join]

theorem size_join (a b : BitVec 64) : (join a b).size = 16 := by
  rw [join, size_mk, List.length_append, length_toBytes, length_toBytes]

private theorem item_spec {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (j : Nat) {i : Nat} (hi : i < n)
    {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    ∃ a' r', unwrap.round.item key n j i a r = .ok (a', r') ∧ Rel n a' r' (unwrapInner key n j (i + 1) s) := by
  induction i generalizing a r s with
  | zero =>
    rw [unwrap.round.item, h.block_eq hi]
    simp only [decryptBlock_eq_specInvCipher hk (size_join _ _), bind, Except.bind, ↓reduceIte]
    exact ⟨_, _, rfl, h.step (size_specInvCipher ..) (take_msb (size_specInvCipher ..))⟩
  | succ i ih =>
    rw [unwrap.round.item, h.block_eq hi]
    simp only [decryptBlock_eq_specInvCipher hk (size_join _ _), bind, Except.bind]
    rw [ite_eq_right (by simp)]
    exact ih (by omega) (h.step (size_specInvCipher ..) (take_msb (size_specInvCipher ..)))

private theorem round_spec {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (hn : 0 < n) (j : Nat)
    {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    ∃ a' r', unwrap.round key n (j + 1) j a r = .ok (a', r') ∧ Rel n a' r' (unwrapOuter key n (j + 1) s) := by
  induction j generalizing a r s with
  | zero =>
    obtain ⟨a', r', hi, hrel⟩ := item_spec hk (n := n) 0 (i := n - 1) (by omega) h
    rw [show n - 1 + 1 = n by omega] at hrel
    rw [unwrap.round, ite_eq_right (by simp), hi]
    exact ⟨a', r', rfl, hrel⟩
  | succ j ih =>
    obtain ⟨a1, r1, hi, hrel⟩ := item_spec hk (n := n) (j + 1) (i := n - 1) (by omega) h
    rw [show n - 1 + 1 = n by omega] at hrel
    obtain ⟨a', r', hr, hrel'⟩ := ih hrel
    refine ⟨a', r', ?_, hrel'⟩
    rw [unwrap.round, ite_eq_right (by simp), hi]
    simpa [bind, Except.bind] using hr

private theorem wrapItem_spec {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (j : Nat) {i : Nat} (hi : i < n)
    {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    ∃ a' r', wrapItem key n j i (a, r) = .ok (a', r') ∧ Rel n a' r' (wrapStep key n j (i + 1) s) := by
  simp only [wrapItem]
  rw [h.block_eq' hi, encryptBlock_eq_specCipher hk (size_join _ _)]
  refine ⟨_, _, rfl, h.step (size_specCipher ..) ?_⟩
  rw [take_msb (size_specCipher ..), xorT_toBytes]
  rfl

private theorem wrapPass_spec {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (j : Nat) {k : Nat} (hk' : k ≤ n)
    {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    ∃ a' r', wrapPass key n j k (a, r) = .ok (a', r') ∧ Rel n a' r' (wrapInner key n j k s) := by
  induction k with
  | zero => exact ⟨a, r, rfl, h⟩
  | succ k ih =>
    obtain ⟨a1, r1, h1, g1⟩ := ih (by omega)
    obtain ⟨a2, r2, h2, g2⟩ := wrapItem_spec hk j (i := k) (by omega) g1
    exact ⟨a2, r2, by simp only [wrapPass, h1, bind, Except.bind]; exact h2, g2⟩

private theorem wrapRounds_spec {key : ByteArray} (hk : ValidKeyLength key.size) {n : Nat} (m : Nat)
    {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    ∃ a' r', wrapRounds key n m (a, r) = .ok (a', r') ∧ Rel n a' r' (wrapOuter key n m s) := by
  induction m with
  | zero => exact ⟨a, r, rfl, h⟩
  | succ m ih =>
    obtain ⟨a1, r1, h1, g1⟩ := ih
    obtain ⟨a2, r2, h2, g2⟩ := wrapPass_spec hk m (Nat.le_refl n) g1
    exact ⟨a2, r2, by simp only [wrapRounds, h1, bind, Except.bind]; exact h2, g2⟩

private theorem Rel.flatten {n : Nat} {a : List UInt8} {r : List (List UInt8)} {s : State} (h : Rel n a r s) :
    r.flatten = registers s.R n := by
  have : r = (List.range n).map fun k => toBytes (s.R (k + 1)) := by
    apply List.ext_getElem (by simp [h.2.1])
    intro k h1 h2
    have hk : k < n := by rw [h.2.1] at h1; exact h1
    rw [← bang_eq r h1, h.2.2 k hk]
    simp
  rw [this, registers, List.flatMap_def]

private theorem take_block {data : ByteArray} {i : Nat} (h : 8 * i + 8 ≤ data.size) :
    (data.toList.drop (8 * i)).take 8 = toBytes (block data i) := by
  rw [block, toBytes_ofBytes]
  simp only [List.length_take, List.length_drop, length_toList]
  omega

end Rfc3394

open Rfc3394

/-- **The wrap of this file is RFC 3394's**, for every valid key encryption key and every whole number of 64-bit blocks. -/
theorem wrap_eq_specWrap {key plain : ByteArray} (hk : ValidKeyLength key.size) (hp : plain.size % 8 = 0) :
    wrap key plain = .ok (specWrap key plain) := by
  have hrel : Rel (plain.size / 8) defaultIv (chunks (plain.size / 8) plain.toList)
      ⟨iv, fun i => block plain (i - 1)⟩ := by
    refine ⟨toBytes_iv.symm, by simp [chunks], fun k hk => ?_⟩
    have hlt : k < (chunks (plain.size / 8) plain.toList).length := by simp [chunks, hk]
    rw [bang_eq _ hlt]
    simp only [chunks, List.getElem_map, List.getElem_range, Nat.add_sub_cancel]
    rw [Nat.mul_comm k 8]
    apply take_block
    omega
  obtain ⟨a, r, hw, hg⟩ := wrapRounds_spec hk (n := plain.size / 8) 6 hrel
  simp only [wrap, wrapWithIv, hw, bind, Except.bind, specWrap]
  rw [hg.flatten, hg.1]

/-- **`unwrap` is RFC 3394's**, on every valid key encryption key and every input of the right shape: other shapes are
rejected, see `unwrap_rejects_short` and `unwrap_rejects_unaligned`. -/
theorem unwrap_eq_specUnwrap {key input : ByteArray} (hk : ValidKeyLength key.size)
    (hshape : ¬ (input.size < 24 ∨ input.size % 8 ≠ 0)) :
    unwrap key input = match specUnwrap key input with
      | some plain => .ok plain
      | none => .error "RFC 3394 integrity check failed" := by
  have hrel : Rel (input.size / 8 - 1) (input.toList.take 8)
      ((List.range (input.size / 8 - 1)).map fun index => (input.toList.drop (8 + index * 8)).take 8)
      ⟨block input 0, fun i => block input i⟩ := by
    refine ⟨by rw [← take_block (i := 0) (by omega)]; rfl, by simp, fun k hk => ?_⟩
    have hlt : k < ((List.range (input.size / 8 - 1)).map fun index =>
        (input.toList.drop (8 + index * 8)).take 8).length := by simp [hk]
    rw [bang_eq _ hlt]
    simp only [List.getElem_map, List.getElem_range]
    rw [show 8 + k * 8 = 8 * (k + 1) by omega]
    apply take_block
    omega
  obtain ⟨a, r, hr, hg⟩ := round_spec hk (n := input.size / 8 - 1) (by omega) 5 hrel
  rw [unwrap, ite_eq_right (by simpa using hshape)]
  simp only [hr, bind, Except.bind, specUnwrap]
  rw [hg.flatten, hg.1]
  by_cases hiv : (unwrapOuter key (input.size / 8 - 1) 6 ⟨block input 0, fun i => block input i⟩).A = iv
  · simp only [hiv, toBytes_iv, ↓reduceIte, bne_self_eq_false, Bool.false_eq_true]
  · have hne : toBytes (unwrapOuter key (input.size / 8 - 1) 6 ⟨block input 0, fun i => block input i⟩).A ≠ defaultIv := by
      intro h
      apply hiv
      rw [← ofBytes_toBytes (unwrapOuter key _ 6 _).A, h, ← toBytes_iv, ofBytes_toBytes]
    simp [hiv, hne]

/-- Unwrapping undoes wrapping, on the specification's own terms. -/
theorem specUnwrap_specWrap {key plain : ByteArray} (hk : ValidKeyLength key.size) (hp : plain.size % 8 = 0)
    (hp16 : 16 ≤ plain.size) : specUnwrap key (specWrap key plain) = some plain := by
  obtain ⟨c, hw, hs, hu⟩ := unwrap_wrap hk hp hp16
  rw [wrap_eq_specWrap hk hp] at hw
  cases hw
  rw [unwrap_eq_specUnwrap hk (by omega)] at hu
  cases hsp : specUnwrap key (specWrap key plain) with
  | none => simp [hsp] at hu
  | some p => simp only [hsp, Except.ok.injEq] at hu; rw [hu]

/-- A blob the specification doesn't accept is not unwrapped, and one it does is. -/
theorem unwrap_ok_iff_specUnwrap {key input plain : ByteArray} (hk : ValidKeyLength key.size)
    (hshape : ¬ (input.size < 24 ∨ input.size % 8 ≠ 0)) :
    unwrap key input = .ok plain ↔ specUnwrap key input = some plain := by
  rw [unwrap_eq_specUnwrap hk hshape]
  cases specUnwrap key input <;> simp

/-! The specification reproduces section 4, from the general theorems and the kernel-checked vectors above. -/

private theorem specWrap_of_wrap {key plain c : ByteArray} (hk : ValidKeyLength key.size) (hp : plain.size % 8 = 0)
    (h : (wrap key plain).toOption = some c) : specWrap key plain = c := by
  rw [wrap_eq_specWrap hk hp] at h
  simpa [Except.toOption] using h

private theorem specUnwrap_of_unwrap {key input p : ByteArray} (hk : ValidKeyLength key.size)
    (hshape : ¬ (input.size < 24 ∨ input.size % 8 ≠ 0)) (h : (unwrap key input).toOption = some p) :
    specUnwrap key input = some p := by
  rw [unwrap_eq_specUnwrap hk hshape] at h
  cases hs : specUnwrap key input <;> simp_all [Except.toOption]

theorem rfc3394_128_128_specWrap :
    specWrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f])
      (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) =
    ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5] :=
  specWrap_of_wrap (by decide) rfl rfc3394_wrap_128_128

theorem rfc3394_128_128_specUnwrap :
    specUnwrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f])
      (ByteArray.mk #[0x1f,0xa6,0x8b,0x0a,0x81,0x12,0xb4,0x47,0xae,0xf3,0x4b,0xd8,0xfb,0x5a,0x7b,0x82,0x9d,0x3e,0x86,0x23,0x71,0xd2,0xcf,0xe5]) =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) :=
  specUnwrap_of_unwrap (by decide) (by decide) rfc3394_unwrap_128_128

theorem rfc3394_192_128_specUnwrap :
    specUnwrap (ByteArray.mk #[0x00,0x01,0x02,0x03,0x04,0x05,0x06,0x07,0x08,0x09,0x0a,0x0b,0x0c,0x0d,0x0e,0x0f,0x10,0x11,0x12,0x13,0x14,0x15,0x16,0x17])
      (ByteArray.mk #[0x96,0x77,0x8b,0x25,0xae,0x6c,0xa4,0x35,0xf9,0x2b,0x5b,0x97,0xc0,0x50,0xae,0xd2,0x46,0x8a,0xb8,0xa1,0x7a,0xd8,0x4e,0x5d]) =
    some (ByteArray.mk #[0x00,0x11,0x22,0x33,0x44,0x55,0x66,0x77,0x88,0x99,0xaa,0xbb,0xcc,0xdd,0xee,0xff]) :=
  specUnwrap_of_unwrap (by decide) (by decide) rfc3394_unwrap_192_128

/-! What these establish: `unwrap` and the `wrap` of this file compute `specUnwrap` and `specWrap` on every valid input.
`Rfc3394` is Lean, not the RFC, and says what the RFC says only by being read against it and by the vectors of section 4;
the registers are 64-bit numbers, the initial value is the default one of section 2.2.3.1 and the counter `t` is truncated
to 64 bits, past any input that fits in memory. The RFC's alternative initial values and its padding (RFC 5649) are not
here. Production has only `unwrap`: nothing in it needs the forward cipher, so `encryptBlock` and `wrap` stay here. -/

end Bap.Proofs.Crypto
