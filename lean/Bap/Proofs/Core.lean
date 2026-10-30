import Bap.Core.Assoc
import Bap.Core.Memory
import Bap.Core.Sexp
import Bap.Core.Types
import Bap.Core.Word
import Std.Data.TreeMap.Lemmas
import Lean.Elab.Command

set_option linter.unusedSimpArgs false

namespace Bap.Proofs.Core

open Lean Elab Command in
/-- Brings `private` declarations of an imported module into scope under their short names. -/
local elab "open_private " m:ident names:ident* : command => do
  for n in names do
    let full := n.getId
    let decl := mkPrivateNameCore m.getId full
    modifyScope fun s => { s with openDecls := .explicit (Name.mkSimple full.getString!) decl :: s.openDecls }

namespace WordLaws

theorem udiv_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    Word.udiv left right = left / right := by
  simp [Word.udiv, h]

theorem urem_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    Word.urem left right = left % right := by
  simp [Word.urem, h]

theorem sdiv_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    Word.sdiv left right = BitVec.sdiv left right := by
  simp [Word.sdiv, h]

theorem srem_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    Word.srem left right = BitVec.srem left right := by
  simp [Word.srem, h]

theorem toNat_udiv_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    BitVec.toNat (Word.udiv left right) = left.toNat / right.toNat := by
  rw [udiv_of_ne h, BitVec.toNat_udiv]

theorem toNat_urem_of_ne {left right : BitVec width} (h : right ≠ 0#width) :
    BitVec.toNat (Word.urem left right) = left.toNat % right.toNat := by
  rw [urem_of_ne h, BitVec.toNat_umod]

theorem urem_lt {left right : BitVec width} (h : right ≠ 0#width) :
    BitVec.toNat (Word.urem left right) < right.toNat := by
  rw [toNat_urem_of_ne h]
  apply Nat.mod_lt
  have : right.toNat ≠ 0 := by
    intro hz
    exact h (BitVec.eq_of_toNat_eq (by simpa using hz))
  omega

private theorem udiv_mul_add_umod (a b : BitVec width) : a / b * b + a % b = a := by
  apply BitVec.eq_of_toNat_eq
  have hlt : a.toNat < 2 ^ width := a.isLt
  have hdm := Nat.div_add_mod a.toNat b.toNat
  rw [Nat.mul_comm] at hdm
  simp only [BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_udiv, BitVec.toNat_umod]
  have h1 : a.toNat / b.toNat * b.toNat < 2 ^ width := by omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega)]
  exact hdm

/-- Euclidean division identity for unsigned operands, including division by zero. -/
theorem udiv_mul_add_urem (left right : BitVec width) :
    Word.udiv left right * right + Word.urem left right = left := by
  by_cases h : right = 0#width
  · subst h
    simp [Word.udiv, Word.urem]
  · rw [udiv_of_ne h, urem_of_ne h]
    exact udiv_mul_add_umod left right

/-- Truncated signed division identity, including division by zero and `intMin / -1`. -/
theorem sdiv_mul_add_srem (left right : BitVec width) :
    Word.sdiv left right * right + Word.srem left right = left := by
  by_cases h : right = 0#width
  · subst h
    simp [Word.sdiv, Word.srem]
  · rw [sdiv_of_ne h, srem_of_ne h, BitVec.sdiv_eq, BitVec.srem_eq]
    have k1 := udiv_mul_add_umod left (-right)
    have k2 := udiv_mul_add_umod (-left) right
    have k3 := udiv_mul_add_umod (-left) (-right)
    have k0 := udiv_mul_add_umod left right
    cases left.msb <;> cases right.msb <;> simp only [BitVec.udiv_eq]
    · exact k0
    · grind
    · grind
    · grind

theorem shl_toNat (value amount : BitVec width) :
    BitVec.toNat (Word.shl value amount) = value.toNat * 2 ^ amount.toNat % 2 ^ width := by
  simp [Word.shl, Word.toNat, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem lshr_toNat (value amount : BitVec width) :
    BitVec.toNat (Word.lshr value amount) = value.toNat / 2 ^ amount.toNat := by
  simp [Word.lshr, Word.toNat, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem ashr_toInt (value amount : BitVec width) :
    BitVec.toInt (Word.ashr value amount) = value.toInt >>> amount.toNat := by
  simp [Word.ashr, Word.toNat, BitVec.toInt_sshiftRight]

theorem shl_overflow (value amount : BitVec width) (h : width ≤ amount.toNat) :
    Word.shl value amount = 0#width := by
  apply BitVec.eq_of_toNat_eq
  rw [shl_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  rw [hk, Nat.pow_add, ← Nat.mul_assoc, Nat.mul_comm]
  exact Nat.mod_eq_zero_of_dvd (Nat.dvd_mul_left_of_dvd (Nat.dvd_mul_left _ _) _)

theorem lshr_overflow (value amount : BitVec width) (h : width ≤ amount.toNat) :
    Word.lshr value amount = 0#width := by
  apply BitVec.eq_of_toNat_eq
  rw [lshr_toNat]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  apply Nat.div_eq_of_lt
  exact Nat.lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by decide) h)

theorem bool_eq_one_iff (value : Bool) : Word.bool value = 1#1 ↔ value = true := by
  cases value <;> decide

theorem eq_eq_one_iff (left right : BitVec width) : Word.eq left right = 1#1 ↔ left = right := by
  simp [Word.eq, bool_eq_one_iff]

theorem neq_eq_one_iff (left right : BitVec width) : Word.neq left right = 1#1 ↔ left ≠ right := by
  simp [Word.neq, bool_eq_one_iff]

theorem lt_eq_one_iff (left right : BitVec width) : Word.lt left right = 1#1 ↔ left.toNat < right.toNat := by
  simp [Word.lt, bool_eq_one_iff, BitVec.lt_def]

theorem le_eq_one_iff (left right : BitVec width) : Word.le left right = 1#1 ↔ left.toNat ≤ right.toNat := by
  simp [Word.le, bool_eq_one_iff, BitVec.le_def]

theorem slt_eq_one_iff (left right : BitVec width) : Word.slt left right = 1#1 ↔ left.toInt < right.toInt := by
  simp [Word.slt, bool_eq_one_iff, BitVec.slt, decide_eq_true_eq]

theorem sle_eq_one_iff (left right : BitVec width) : Word.sle left right = 1#1 ↔ left.toInt ≤ right.toInt := by
  simp [Word.sle, bool_eq_one_iff, BitVec.sle, decide_eq_true_eq]

private theorem bool_not (value : Bool) : Word.bool (!value) = ~~~(Word.bool value) := by
  cases value <;> decide

theorem le_eq_not_gt (left right : BitVec width) : Word.le left right = ~~~(Word.lt right left) := by
  rw [Word.le, Word.lt, ← bool_not]
  congr 1
  simp only [BitVec.le_def, BitVec.lt_def]
  by_cases h : left.toNat ≤ right.toNat <;> simp [h] <;> omega

theorem sle_eq_not_sgt (left right : BitVec width) : Word.sle left right = ~~~(Word.slt right left) := by
  rw [Word.sle, Word.slt, ← bool_not]
  congr 1
  simp only [BitVec.sle, BitVec.slt]
  by_cases h : left.toInt ≤ right.toInt <;> simp [h] <;> omega

/-- Ordering trichotomy for the unsigned comparison. -/
theorem lt_trichotomy (left right : BitVec width) :
    Word.lt left right = 1#1 ∨ Word.eq left right = 1#1 ∨ Word.lt right left = 1#1 := by
  rw [lt_eq_one_iff, eq_eq_one_iff, lt_eq_one_iff]
  by_cases h : left = right
  · exact Or.inr (Or.inl h)
  · have : left.toNat ≠ right.toNat := fun hn => h (BitVec.eq_of_toNat_eq hn)
    omega

theorem signed_toInt {source : Nat} (value : BitVec source) (h : source ≤ width) :
    BitVec.toInt (Word.signed width value) = value.toInt := by
  simp [Word.signed, BitVec.toInt_signExtend_of_le h]

theorem unsigned_toNat {source : Nat} (value : BitVec source) (h : source ≤ width) :
    BitVec.toNat (Word.unsigned width value) = value.toNat := by
  simp only [Word.unsigned, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  exact Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le value.isLt (Nat.pow_le_pow_right (by decide) h))

theorem low_toNat {source : Nat} (value : BitVec source) :
    BitVec.toNat (Word.low width value) = value.toNat % 2 ^ width := by
  simp [Word.low, BitVec.toNat_setWidth]

theorem high_ok {source : Nat} (value : BitVec source) (h0 : 0 < width) (h : width ≤ source) :
    ∃ result, Word.high width value = .ok result ∧
      BitVec.toNat result = value.toNat / 2 ^ (source - width) := by
  refine ⟨_, by simp only [Word.high, h0, h, and_self, ite_true]; rfl, ?_⟩
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.ushiftRight_eq, BitVec.toNat_ushiftRight]
  rw [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
  apply Nat.div_lt_of_lt_mul
  rw [← Nat.pow_add, show source - width + width = source by omega]
  exact value.isLt

theorem high_error {source : Nat} (value : BitVec source) (h : ¬ (0 < width ∧ width ≤ source)) :
    Word.high width value = .error "invalid high cast" := by
  simp [Word.high, h]

theorem concat_toNat {lw rw : Nat} (left : BitVec lw) (right : BitVec rw) :
    BitVec.toNat (Word.concat left right) = 2 ^ rw * left.toNat + right.toNat := by
  rw [Nat.two_pow_add_eq_or_of_lt right.isLt]
  simp [Word.concat, BitVec.toNat_append, Nat.shiftLeft_eq, Nat.mul_comm]

/-- `low` and `high` project both halves back out of a `concat`. -/
theorem low_concat {lw rw : Nat} (left : BitVec lw) (right : BitVec rw) :
    Word.low rw (Word.concat left right) = right := by
  apply BitVec.eq_of_toNat_eq
  rw [low_toNat, concat_toNat, Nat.mul_add_mod, Nat.mod_eq_of_lt right.isLt]

theorem high_concat {lw rw : Nat} (left : BitVec lw) (right : BitVec rw) (h : 0 < lw) :
    Word.high lw (Word.concat left right) = .ok left := by
  obtain ⟨result, hok, hval⟩ := high_ok (width := lw) (Word.concat left right) h (by omega)
  rw [hok]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [hval, concat_toNat, show lw + rw - lw = rw by omega]
  rw [Nat.mul_add_div (Nat.two_pow_pos rw), Nat.div_eq_of_lt right.isLt, Nat.add_zero]

theorem extract_ok {source : Nat} (value : BitVec source) (hi lo : Nat) (h1 : lo ≤ hi) (h2 : hi < source) :
    Word.extract hi lo value = .ok (BitVec.extractLsb hi lo value) := by
  simp [Word.extract, show ¬ hi < lo by omega, show ¬ source ≤ hi by omega]

theorem extract_toNat {source : Nat} (value : BitVec source) (hi lo : Nat) :
    (BitVec.extractLsb hi lo value).toNat = (value.toNat / 2 ^ lo) % 2 ^ (hi - lo + 1) := by
  simp [BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_eq_div_pow]

/-- `Word.smod` is exactly the SMT-LIB `bvsmod` definition, stated on absolute values. -/
theorem smod_spec (left right : BitVec width) :
    Word.smod left right =
      let absLeft := if left.msb then -left else left
      let absRight := if right.msb then -right else right
      let u := absLeft % absRight
      if u = 0#width then u
      else match left.msb, right.msb with
        | false, false => u
        | true, false => -u + right
        | false, true => u + right
        | true, true => -u := by
  simp only [Word.smod, BitVec.smod_eq, BitVec.umod_eq]
  cases hl : left.msb <;> cases hr : right.msb
  · simp only [Bool.false_eq_true, ite_false]
    split <;> simp_all
  · simp only [Bool.false_eq_true, ite_false, ite_true]
  · simp only [Bool.false_eq_true, ite_false, ite_true]
    split
    · rfl
    · rw [BitVec.sub_eq_add_neg, BitVec.add_comm]
  · simp only [ite_true]
    split <;> simp_all

theorem smod_zero (left : BitVec width) : Word.smod left 0#width = left :=
  BitVec.smod_zero

/-- The signed reading of `smod` is floored modulus, which cannot overflow. -/
theorem smod_toInt (left right : BitVec width) :
    BitVec.toInt (Word.smod left right) = left.toInt.fmod right.toInt :=
  BitVec.toInt_smod

/-- Division with floored quotient: `left` differs from the result by a multiple of `right`. -/
theorem smod_congruent (left right : BitVec width) :
    ∃ quotient : Int, left.toInt = quotient * right.toInt + BitVec.toInt (Word.smod left right) := by
  refine ⟨left.toInt.fdiv right.toInt, ?_⟩
  rw [smod_toInt, Int.fdiv_mul_add_fmod]

/-- A nonzero result takes the divisor's sign and is smaller than the divisor in magnitude. -/
theorem smod_bound_of_pos {left right : BitVec width} (h : 0 < right.toInt) :
    0 ≤ BitVec.toInt (Word.smod left right) ∧ BitVec.toInt (Word.smod left right) < right.toInt := by
  rw [smod_toInt]
  exact ⟨Int.fmod_nonneg_of_pos _ h, Int.fmod_lt_of_pos _ h⟩

theorem smod_bound_of_neg {left right : BitVec width} (h : right.toInt < 0) :
    right.toInt < BitVec.toInt (Word.smod left right) ∧ BitVec.toInt (Word.smod left right) ≤ 0 := by
  rw [smod_toInt, Int.fmod_eq_emod]
  have h1 := Int.emod_nonneg left.toInt (show right.toInt ≠ 0 by omega)
  have h2 := Int.emod_lt_of_pos left.toInt (show 0 < -right.toInt by omega)
  rw [Int.emod_neg] at h2
  split
  · rename_i hc
    rcases hc with hc | hc
    · omega
    · have := Int.emod_eq_zero_of_dvd hc
      omega
  · rename_i hc
    have : left.toInt % right.toInt ≠ 0 := fun hz =>
      hc (Or.inr (Int.dvd_of_emod_eq_zero hz))
    omega

/-- On nonnegative operands `smod` is the unsigned remainder. -/
theorem smod_of_msb_false {left right : BitVec width} (hl : left.msb = false) (hr : right.msb = false) :
    Word.smod left right = Word.urem left right := by
  by_cases h : right = 0#width
  · subst h
    simp [Word.smod, Word.urem]
  · rw [urem_of_ne h]
    simp [Word.smod, BitVec.smod_eq, hl, hr, BitVec.umod_eq]

end WordLaws

namespace AssocLaws
variable {α β : Type _} [DecidableEq α]

theorem get_cons (key k : α) (v : β) (rest : List (α × β)) :
    Assoc.get key ((k, v) :: rest) = if key = k then some v else Assoc.get key rest := by
  by_cases h : key = k
  · simp [Assoc.get, h]
  · have : (key == k) = false := by simpa using h
    simp [Assoc.get, List.lookup, this, h]

theorem get_remove (key target : α) (entries : List (α × β)) :
    Assoc.get key (Assoc.remove target entries) =
      if key = target then none else Assoc.get key entries := by
  induction entries with
  | nil => simp [Assoc.remove]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    by_cases hk : k = target
    · subst hk
      have heq : Assoc.remove k ((k, v) :: rest) = Assoc.remove k rest := by simp [Assoc.remove]
      rw [heq, ih, get_cons]
      by_cases h : key = k <;> simp [h]
    · have heq : Assoc.remove target ((k, v) :: rest) = (k, v) :: Assoc.remove target rest := by
        simp [Assoc.remove, hk]
      rw [heq, get_cons, ih, get_cons]
      by_cases h : key = target
      · subst h; simp [Ne.symm hk]
      · simp [h]

theorem get_remove_same (key : α) (entries : List (α × β)) :
    Assoc.get key (Assoc.remove key entries) = none := by
  simp [get_remove]

theorem get_remove_other {key target : α} (h : key ≠ target) (entries : List (α × β)) :
    Assoc.get key (Assoc.remove target entries) = Assoc.get key entries := by
  simp [get_remove, h]

theorem put_eq_cons_remove (key : α) (value : β) (entries : List (α × β)) :
    Assoc.put key value entries = (key, value) :: Assoc.remove key entries := rfl

/-- Full characterisation of lookups after an update. -/
theorem get_put (key target : α) (value : β) (entries : List (α × β)) :
    Assoc.get key (Assoc.put target value entries) =
      if key = target then some value else Assoc.get key entries := by
  rw [put_eq_cons_remove, get_cons, get_remove]
  by_cases h : key = target <;> simp [h]

theorem get_put_other {key target : α} (h : key ≠ target) (value : β) (entries : List (α × β)) :
    Assoc.get key (Assoc.put target value entries) = Assoc.get key entries := by
  simp [get_put, h]

theorem remove_remove_same (key : α) (entries : List (α × β)) :
    Assoc.remove key (Assoc.remove key entries) = Assoc.remove key entries := by
  simp [Assoc.remove, List.filter_filter]

theorem remove_comm (first second : α) (entries : List (α × β)) :
    Assoc.remove first (Assoc.remove second entries) =
      Assoc.remove second (Assoc.remove first entries) := by
  simp only [Assoc.remove, List.filter_filter]
  congr 1
  funext entry
  exact Bool.and_comm _ _

/-- Writing the same key twice leaves the same list as writing only the last value. -/
theorem put_put_same (key : α) (old new : β) (entries : List (α × β)) :
    Assoc.put key new (Assoc.put key old entries) = Assoc.put key new entries := by
  simp [Assoc.put, List.filter_filter]

theorem remove_put_same (key : α) (value : β) (entries : List (α × β)) :
    Assoc.remove key (Assoc.put key value entries) = Assoc.remove key entries := by
  simp [Assoc.put, Assoc.remove, List.filter_filter]

theorem put_remove_same (key : α) (value : β) (entries : List (α × β)) :
    Assoc.put key value (Assoc.remove key entries) = Assoc.put key value entries := by
  simp [Assoc.put, Assoc.remove, List.filter_filter]

theorem get_put_comm {first second : α} (h : first ≠ second) (x y : β) (entries : List (α × β)) (key : α) :
    Assoc.get key (Assoc.put first x (Assoc.put second y entries)) =
      Assoc.get key (Assoc.put second y (Assoc.put first x entries)) := by
  simp only [get_put]
  by_cases h1 : key = first
  · subst h1; simp [h]
  · simp [h1]

theorem mem_of_get_some {key : α} {value : β} {entries : List (α × β)}
    (h : Assoc.get key entries = some value) : (key, value) ∈ entries := by
  induction entries with
  | nil => simp at h
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    rw [get_cons] at h
    by_cases hk : key = k
    · subst hk
      simp only [ite_true, Option.some.injEq] at h
      simp [h]
    · simp only [hk, ite_false] at h
      exact List.mem_cons_of_mem _ (ih h)

theorem get_isSome_iff_mem_keys (key : α) (entries : List (α × β)) :
    (Assoc.get key entries).isSome ↔ key ∈ Assoc.keys entries := by
  induction entries with
  | nil => simp [Assoc.keys]
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    rw [get_cons]
    by_cases hk : key = k
    · simp [hk, Assoc.keys]
    · simp only [hk, ite_false, ih]
      simp [Assoc.keys, hk]

theorem keys_remove (key : α) (entries : List (α × β)) :
    Assoc.keys (Assoc.remove key entries) = (Assoc.keys entries).filter (· != key) := by
  simp [Assoc.keys, Assoc.remove, List.filter_map, Function.comp_def]

/-- `put` and `remove` keep association lists free of duplicate keys. -/
theorem nodup_keys_remove (key : α) {entries : List (α × β)} (h : (Assoc.keys entries).Nodup) :
    (Assoc.keys (Assoc.remove key entries)).Nodup := by
  rw [keys_remove]
  exact h.filter _

theorem nodup_keys_put (key : α) (value : β) {entries : List (α × β)} (h : (Assoc.keys entries).Nodup) :
    (Assoc.keys (Assoc.put key value entries)).Nodup := by
  rw [put_eq_cons_remove]
  have hn := nodup_keys_remove key h
  simp only [Assoc.keys, List.map_cons, List.nodup_cons]
  refine ⟨?_, hn⟩
  have := keys_remove key entries
  simp only [Assoc.keys] at this
  rw [this]
  simp

/-- With unique keys, `get` is exactly list membership. -/
theorem get_eq_some_iff {key : α} {value : β} {entries : List (α × β)}
    (h : (Assoc.keys entries).Nodup) : Assoc.get key entries = some value ↔ (key, value) ∈ entries := by
  refine ⟨mem_of_get_some, ?_⟩
  induction entries with
  | nil => simp
  | cons entry rest ih =>
    obtain ⟨k, v⟩ := entry
    intro hm
    simp only [Assoc.keys, List.map_cons, List.nodup_cons] at h
    rw [get_cons]
    simp only [List.mem_cons, Prod.mk.injEq] at hm
    rcases hm with ⟨rfl, rfl⟩ | hm
    · simp
    · have hne : key ≠ k := by
        rintro rfl
        exact h.1 (List.mem_map.mpr ⟨_, hm, rfl⟩)
      simp only [hne, ite_false]
      exact ih h.2 hm

theorem length_remove_le (key : α) (entries : List (α × β)) :
    (Assoc.remove key entries).length ≤ entries.length :=
  List.length_filter_le _ _

/-- Lookups determine the result of `put` up to membership: a stale binding can't survive. -/
theorem not_mem_keys_remove (key : α) (entries : List (α × β)) :
    key ∉ Assoc.keys (Assoc.remove key entries) := by
  rw [← get_isSome_iff_mem_keys, get_remove_same]
  simp

end AssocLaws

namespace TypesLaws

theorem base_eq_self_iff (var : Var) : var.base = var ↔ var.index = 0 := by
  cases var
  simp [Var.base, eq_comm]

/-- Two variables are equal iff they share a base and an index. -/
theorem var_ext_base {left right : Var} : left = right ↔ left.base = right.base ∧ left.index = right.index := by
  cases left; cases right
  simp [Var.base]
  grind

end TypesLaws

namespace MemoryLaws
open Bap.Memory hiding read

private abbrev freshPage : ByteArray := ByteArray.mk (List.replicate pageSize 0).toArray

/-- Representation invariant: every materialised page is exactly `pageSize` bytes long. -/
def PagesSized (memory : Memory addressWidth) : Prop :=
  ∀ index page, memory.pages.get? index = some page → page.size = pageSize

private theorem page_getBang (p : ByteArray) (j : Nat) : p[j]! = p.data[j]! := by
  by_cases h : j < p.size
  · have h' : j < p.data.size := h
    rw [getElem!_pos p j h, getElem!_pos p.data j h']; rfl
  · have h' : ¬ j < p.data.size := h
    rw [getElem!_neg p j h, getElem!_neg p.data j h']

private theorem page_get_set (page : ByteArray) (i j : Nat) (value : UInt8) :
    (page.set! i value)[j]! = if i = j ∧ i < page.size then value else page[j]! := by
  rw [page_getBang, page_getBang]
  obtain ⟨d⟩ := page
  show (d.set! i value)[j]! = if i = j ∧ i < d.size then value else d[j]!
  simp only [getElem!_def, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i < d.size <;> simp [hlt]
  · simp [hij]

private theorem page_size_set (page : ByteArray) (i : Nat) (value : UInt8) :
    (page.set! i value).size = page.size := by
  obtain ⟨d⟩ := page
  show (d.set! i value).size = d.size
  simp

private theorem replicate_get (n j : Nat) : (ByteArray.mk (List.replicate n 0).toArray)[j]! = 0 := by
  rw [page_getBang]
  show (List.replicate n (0:UInt8)).toArray[j]! = 0
  simp only [getElem!_def]
  by_cases h : j < n <;> simp [h] <;> rfl

private theorem replicate_size (n : Nat) : (ByteArray.mk (List.replicate n 0).toArray).size = n := by
  show (List.replicate n (0:UInt8)).toArray.size = n
  simp

private theorem fresh_size : freshPage.size = pageSize := replicate_size _

private theorem fresh_get (j : Nat) : freshPage[j]! = 0 := by
  unfold freshPage
  exact replicate_get pageSize j

theorem empty_pagesSized : PagesSized (empty addressWidth) := by
  intro index page h
  simp [empty] at h

private theorem pages_get?_writeByte (memory : Memory addressWidth) (address : BitVec addressWidth)
    (value : UInt8) (index : Nat) :
    (writeByte memory address value).pages.get? index =
      if address.toNat / pageSize = index then
        some (((memory.pages.get? index).getD freshPage).set! (address.toNat % pageSize) value)
      else memory.pages.get? index := by
  simp only [writeByte, Std.TreeMap.get?_eq_getElem?]
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : address.toNat / pageSize = index
  · subst h
    rw [ite_eq_left (by simp), ite_eq_left rfl]
  · rw [ite_eq_right (by simpa using h), ite_eq_right h]

private theorem page_of_get_size {memory : Memory addressWidth} (h : PagesSized memory) (index : Nat) :
    ((memory.pages.get? index).getD freshPage).size = pageSize := by
  cases hg : memory.pages.get? index with
  | none => exact fresh_size
  | some p => simpa using h index p hg

theorem writeByte_pagesSized {memory : Memory addressWidth} (h : PagesSized memory)
    (address : BitVec addressWidth) (value : UInt8) : PagesSized (writeByte memory address value) := by
  intro index page hp
  rw [pages_get?_writeByte] at hp
  split at hp
  · simp only [Option.some.injEq] at hp
    subst hp
    rw [page_size_set]
    exact page_of_get_size h index
  · exact h index page hp

/-- Read-after-write at the written address. -/
theorem readByte_writeByte_same {memory : Memory addressWidth} (h : PagesSized memory)
    (address : BitVec addressWidth) (value : UInt8) :
    readByte (writeByte memory address value) address = value := by
  simp only [readByte]
  rw [pages_get?_writeByte]
  simp only [ite_true]
  rw [page_get_set, page_of_get_size h]
  have hlt : address.toNat % pageSize < pageSize := Nat.mod_lt _ (by decide)
  simp [hlt]

/-- Without the size invariant a write into an undersized page is silently lost. -/
theorem readByte_writeByte_requires_pagesSized :
    let memory : Memory 64 := ⟨Std.TreeMap.empty.insert 0 ByteArray.empty⟩
    readByte (writeByte memory 0#64 1) 0#64 = 0 := by
  simp only [readByte, writeByte]
  simp
  rfl

/-- Reads are unaffected by a write to any other address. -/
theorem readByte_writeByte_other (memory : Memory addressWidth) {address other : BitVec addressWidth}
    (hne : other ≠ address) (value : UInt8) :
    readByte (writeByte memory address value) other = readByte memory other := by
  simp only [readByte]
  rw [pages_get?_writeByte]
  have hnat : other.toNat ≠ address.toNat := fun h => hne (BitVec.eq_of_toNat_eq h)
  by_cases hp : address.toNat / pageSize = other.toNat / pageSize
  · simp only [hp, ite_true]
    have hm : address.toNat % pageSize ≠ other.toNat % pageSize := by
      intro hm
      apply hnat
      have h1 := Nat.div_add_mod address.toNat pageSize
      have h2 := Nat.div_add_mod other.toNat pageSize
      rw [hp, hm] at h1
      omega
    rw [page_get_set]
    simp only [hm, false_and, ite_false]
    cases hg : memory.pages.get? (other.toNat / pageSize) with
    | none =>
      simp only [Option.getD_none]
      rw [fresh_get]
    | some p => simp
  · simp [hp]

theorem readByte_writeByte (memory : Memory addressWidth) (h : PagesSized memory)
    (address other : BitVec addressWidth) (value : UInt8) :
    readByte (writeByte memory address value) other =
      if other = address then value else readByte memory other := by
  by_cases he : other = address
  · subst he; simp [readByte_writeByte_same h]
  · simp [he, readByte_writeByte_other memory he]

theorem readByte_empty (address : BitVec addressWidth) : readByte (empty addressWidth) address = 0 := by
  simp [readByte, empty]

/-- Observational equality: writes to distinct addresses commute. -/
theorem readByte_write_comm {memory : Memory addressWidth} (h : PagesSized memory)
    {first second : BitVec addressWidth} (hne : first ≠ second) (x y : UInt8) (address : BitVec addressWidth) :
    readByte (writeByte (writeByte memory first x) second y) address =
      readByte (writeByte (writeByte memory second y) first x) address := by
  rw [readByte_writeByte _ (writeByte_pagesSized h _ _), readByte_writeByte _ h,
    readByte_writeByte _ (writeByte_pagesSized h _ _), readByte_writeByte _ h]
  by_cases h1 : address = second
  · subst h1; simp [hne.symm]
  · simp [h1]

/-- Observational equality: the second write to an address wins. -/
theorem readByte_write_overwrite {memory : Memory addressWidth} (h : PagesSized memory)
    (target : BitVec addressWidth) (old new : UInt8) (address : BitVec addressWidth) :
    readByte (writeByte (writeByte memory target old) target new) address =
      readByte (writeByte memory target new) address := by
  rw [readByte_writeByte _ (writeByte_pagesSized h _ _), readByte_writeByte _ h,
    readByte_writeByte _ h]
  by_cases h1 : address = target <;> simp [h1]

private theorem readByte_foldl_write (memory : Memory addressWidth) (h : PagesSized memory)
    (cells : List (BitVec addressWidth × UInt8)) (address : BitVec addressWidth) :
    readByte (cells.foldl (fun memory cell => writeByte memory cell.1 cell.2) memory) address =
      (cells.reverse.lookup address).getD (readByte memory address) := by
  induction cells generalizing memory with
  | nil => simp
  | cons cell rest ih =>
    rw [List.foldl_cons, ih _ (writeByte_pagesSized h _ _), List.reverse_cons, List.lookup_append]
    rw [readByte_writeByte _ h]
    cases hl : rest.reverse.lookup address with
    | some value => simp
    | none =>
      obtain ⟨a, v⟩ := cell
      by_cases he : address = a
      · subst he; simp
      · have : (address == a) = false := by simpa using he
        simp [List.lookup, this, he]

theorem ofCells_pagesSized (cells : List (BitVec addressWidth × UInt8)) :
    PagesSized (ofCells cells) := by
  suffices ∀ (memory : Memory addressWidth), PagesSized memory →
      PagesSized (cells.foldl (fun memory cell => writeByte memory cell.1 cell.2) memory) from
    this _ empty_pagesSized
  induction cells with
  | nil => exact fun _ h => h
  | cons cell rest ih => exact fun memory h => ih _ (writeByte_pagesSized h _ _)

/-- `ofCells` is last-writer-wins over the cell list, with zero for absent addresses. -/
theorem readByte_ofCells (cells : List (BitVec addressWidth × UInt8)) (address : BitVec addressWidth) :
    readByte (ofCells cells) address = (cells.reverse.lookup address).getD 0 := by
  have := readByte_foldl_write (empty addressWidth) empty_pagesSized cells address
  rw [readByte_empty] at this
  exact this

/-! ### Snapshots through `cells` -/

/-- Every page lies wholly within the address space, so `cells` addresses do not wrap. -/
def Canonical (memory : Memory addressWidth) : Prop :=
  PagesSized memory ∧ ∀ index page, memory.pages.get? index = some page →
    (index + 1) * pageSize ≤ 2 ^ addressWidth

theorem empty_canonical : Canonical (empty addressWidth) :=
  ⟨empty_pagesSized, fun index page h => by simp [empty] at h⟩

theorem writeByte_canonical {memory : Memory addressWidth} (h : Canonical memory) (hw : 8 ≤ addressWidth)
    (address : BitVec addressWidth) (value : UInt8) : Canonical (writeByte memory address value) := by
  refine ⟨writeByte_pagesSized h.1 _ _, fun index page hp => ?_⟩
  rw [pages_get?_writeByte] at hp
  split at hp
  · rename_i he
    subst he
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hw
    have hpow : 2 ^ addressWidth = 2 ^ 8 * 2 ^ k := by rw [hk, Nat.pow_add]
    have hlt := address.isLt
    rw [hpow] at hlt ⊢
    have hps : pageSize = 2 ^ 8 := rfl
    rw [hps]
    have hd : address.toNat / 2 ^ 8 < 2 ^ k := Nat.div_lt_of_lt_mul hlt
    rw [Nat.mul_comm]
    exact Nat.mul_le_mul_left _ hd
  · exact h.2 index page hp

private theorem mem_cells_iff {memory : Memory addressWidth} (h : Canonical memory)
    (address : BitVec addressWidth) (byte : UInt8) :
    (address, byte) ∈ cells memory ↔ byte ≠ 0 ∧ readByte memory address = byte := by
  simp only [cells, List.mem_flatMap, List.mem_filterMap, List.mem_range]
  constructor
  · rintro ⟨⟨index, page⟩, hentry, offset, hoff, hif⟩
    have hget : memory.pages.get? index = some page := by
      rw [Std.TreeMap.get?_eq_getElem?]
      exact Std.TreeMap.mem_toList_iff_getElem?_eq_some.mp hentry
    split at hif
    · simp at hif
    · rename_i hne
      simp only [Option.some.injEq, Prod.mk.injEq] at hif
      obtain ⟨haddr, hbyte⟩ := hif
      subst hbyte
      subst haddr
      have hsize := h.1 _ _ hget
      have hrange := h.2 _ _ hget
      simp only at hoff hne ⊢
      refine ⟨hne, ?_⟩
      have hlt : index * pageSize + offset < 2 ^ addressWidth := by
        rw [Nat.add_mul] at hrange
        omega
      simp only [readByte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
      have hps : 0 < pageSize := by decide
      rw [Nat.mul_comm index pageSize, Nat.mul_add_div hps, Nat.mul_add_mod,
        Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega), Nat.add_zero, hget]
  · rintro ⟨hne, hread⟩
    simp only [readByte] at hread
    split at hread
    · rename_i page hget
      have hsize := h.1 _ _ hget
      have hoff : address.toNat % pageSize < pageSize := Nat.mod_lt _ (by decide)
      refine ⟨(address.toNat / pageSize, page), ?_, address.toNat % pageSize, by show _ < page.size; omega, ?_⟩
      · apply Std.TreeMap.mem_toList_iff_getElem?_eq_some.mpr
        rw [← Std.TreeMap.get?_eq_getElem?]
        exact hget
      · simp only [hread, hne, ite_false, Option.some.injEq, Prod.mk.injEq, and_true]
        apply BitVec.eq_of_toNat_eq
        rw [BitVec.toNat_ofNat, Nat.mul_comm, Nat.div_add_mod, Nat.mod_eq_of_lt address.isLt]
    · exact absurd hread.symm hne

private theorem lookup_getD_of_forall {cells : List (BitVec w × UInt8)} {address : BitVec w} {byte : UInt8}
    (huniq : ∀ other, (address, other) ∈ cells → other = byte)
    (hzero : byte ≠ 0 → (address, byte) ∈ cells) : (cells.lookup address).getD 0 = byte := by
  induction cells with
  | nil =>
    by_cases hb : byte = 0
    · simp [hb]
    · simpa using hzero hb
  | cons cell rest ih =>
    obtain ⟨a, v⟩ := cell
    by_cases he : address = a
    · subst he
      simp only [List.lookup_cons_self, Option.getD_some]
      exact huniq v (by simp)
    · have hbeq : (address == a) = false := by simpa using he
      simp only [List.lookup, hbeq]
      apply ih
      · exact fun other hm => huniq other (List.mem_cons_of_mem _ hm)
      · intro hb
        have := hzero hb
        simp only [List.mem_cons, Prod.mk.injEq] at this
        rcases this with ⟨h1, _⟩ | h2
        · exact absurd h1 he
        · exact h2

/-- A canonical memory is reconstructed exactly (at every address) from its nonzero cells. -/
theorem readByte_ofCells_cells {memory : Memory addressWidth} (h : Canonical memory)
    (address : BitVec addressWidth) :
    readByte (ofCells (cells memory)) address = readByte memory address := by
  rw [readByte_ofCells]
  apply lookup_getD_of_forall
  · intro other hm
    exact ((mem_cells_iff h _ _).mp (List.mem_reverse.mp hm)).2.symm
  · intro hb
    exact List.mem_reverse.mpr ((mem_cells_iff h _ _).mpr ⟨hb, rfl⟩)

/-! ### Multi-byte reads -/

open_private Bap.Core.Memory Bap.Memory.byteAt

/-- The byte sequence `Memory.write` hands to `writeRegion`. -/
def image (value : BitVec valueWidth) (endian : Endian) (size : Nat) : List UInt8 :=
  (List.range size).map fun offset =>
    let byteOffset := match endian with
      | .little => offset
      | .big => size - 1 - offset
    byteAt value.toNat byteOffset

private theorem mod_ne_of_lt {x y limit : Nat} (hxy : x < y) (h : y - x < limit) : x % limit ≠ y % limit := by
  intro he
  have : limit ∣ y - x := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq he.symm)
  have := Nat.le_of_dvd (by omega) this
  omega

/-- Byte at a raw address, the Nat-level reading of `readByte`. -/
private def readAt (pages : Std.TreeMap Nat ByteArray) (address : Nat) : UInt8 :=
  match pages.get? (address / pageSize) with
  | some page => page[address % pageSize]!
  | none => 0

private def Sized (pages : Std.TreeMap Nat ByteArray) : Prop :=
  ∀ index page, pages.get? index = some page → page.size = pageSize

private theorem bang_eq (page : ByteArray) (j : Nat) : page[j]! = (page.data[j]?).getD 0 := by
  rw [page_getBang, getElem!_def]
  cases page.data[j]? <;> rfl

private theorem get!_extract (page : ByteArray) (b e j : Nat) (hj : j < e - b) (he : e ≤ page.size) :
    (page.extract b e)[j]! = page[b + j]! := by
  have hmin : min e page.size = e := by omega
  have hd : min e page.data.size = e := hmin
  rw [bang_eq, bang_eq, ByteArray.data_extract, Array.getElem?_extract, hd, ite_eq_left hj]

/-- The page `writePages` builds for one chunk. -/
private theorem chunk_page (data existing : ByteArray) (offset count po : Nat)
    (hsize : existing.size = pageSize) (hcount : po + count ≤ pageSize) (hdata : offset + count ≤ data.size) :
    let page := if count = pageSize then data.extract offset (offset + count) else
      existing.extract 0 po ++ data.extract offset (offset + count) ++ existing.extract (po + count) pageSize
    page.size = pageSize ∧ ∀ o, o < pageSize →
      page[o]! = if po ≤ o ∧ o < po + count then data[offset + (o - po)]! else existing[o]! := by
  intro page
  have hps : pageSize = 256 := rfl
  have hchunk : (data.extract offset (offset + count)).size = count := by
    simp only [ByteArray.size_extract]; omega
  by_cases hfull : count = pageSize
  · have hpage : page = data.extract offset (offset + count) := ite_eq_left hfull
    rw [hpage]
    have h0 : po = 0 := by omega
    subst h0
    refine ⟨by rw [hchunk, hfull], fun o ho => ?_⟩
    rw [ite_eq_left (by omega), get!_extract _ _ _ _ (by omega) (by omega)]
    simp
  · have hpage : page = existing.extract 0 po ++ data.extract offset (offset + count) ++
        existing.extract (po + count) pageSize := ite_eq_right hfull
    rw [hpage]
    have hl : (existing.extract 0 po).size = po := by
      simp only [ByteArray.size_extract]; omega
    have hr : (existing.extract (po + count) pageSize).size = pageSize - (po + count) := by
      simp only [ByteArray.size_extract, hsize]; omega
    refine ⟨by simp only [ByteArray.size_append, hl, hr, hchunk]; omega, fun o ho => ?_⟩
    have hsplit : ∀ (a b c : ByteArray), (a ++ b ++ c)[o]! =
        if o < a.size then a[o]! else if o < a.size + b.size then b[o - a.size]! else c[o - a.size - b.size]! := by
      intro a b c
      have h1 : (a.data ++ b.data).size = a.size + b.size := by
        rw [Array.size_append]
        rfl
      have h2 : a.data.size = a.size := rfl
      simp only [bang_eq, ByteArray.data_append, Array.getElem?_append, h1, h2]
      by_cases h3 : o < a.size
      · simp only [h3, ite_true, show o < a.size + b.size by omega]
      · by_cases h4 : o < a.size + b.size
        · simp only [h3, h4, ite_true, ite_false]
        · simp only [h3, h4, ite_false, Nat.sub_add_eq]
    rw [hsplit, hl, hchunk]
    by_cases h1 : o < po
    · rw [ite_eq_left h1, ite_eq_right (by omega), get!_extract _ _ _ _ (by omega) (by omega)]
      simp
    · by_cases h2 : o < po + count
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (by omega),
          get!_extract _ _ _ _ (by omega) (by omega)]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega),
          get!_extract _ _ _ _ (by omega) (by omega)]
        congr 1
        omega

open_private Bap.Core.Memory Bap.Memory.writePages Bap.Memory.readPages

private theorem readAt_insert (pages : Std.TreeMap Nat ByteArray) (index : Nat) (page : ByteArray) (a : Nat) :
    readAt (pages.insert index page) a =
      if a / pageSize = index then page[a % pageSize]! else readAt pages a := by
  simp only [readAt, Std.TreeMap.get?_eq_getElem?]
  rw [Std.TreeMap.getElem?_insert]
  by_cases h : a / pageSize = index
  · subst h
    rw [ite_eq_left (by simp), ite_eq_left rfl]
  · rw [ite_eq_right (by rw [Nat.compare_eq_eq]; exact fun e => h e.symm), ite_eq_right h]

private theorem existing_size {pages : Std.TreeMap Nat ByteArray} (h : Sized pages) (index : Nat) :
    ((pages.get? index).getD freshPage).size = pageSize := by
  cases hg : pages.get? index with
  | none => exact fresh_size
  | some p => simpa using h index p hg

private theorem readAt_existing (pages : Std.TreeMap Nat ByteArray) (a : Nat) :
    ((pages.get? (a / pageSize)).getD freshPage)[a % pageSize]! = readAt pages a := by
  simp only [readAt]
  cases hg : pages.get? (a / pageSize) with
  | none =>
    simp only [Option.getD_none]
    rw [fresh_get]
  | some p => simp

/-- Facts about one chunk written at `absolute`: where its bytes land. -/
private theorem chunk_address {address offset limit count k : Nat} (hk : k < count)
    (hc : count ≤ pageSize - (address + offset) % limit % pageSize) (hc2 : count ≤ limit - (address + offset) % limit) :
    (address + (offset + k)) % limit = (address + offset) % limit + k ∧
      ((address + offset) % limit + k) / pageSize = (address + offset) % limit / pageSize ∧
      ((address + offset) % limit + k) % pageSize = (address + offset) % limit % pageSize + k := by
  have hps : pageSize = 256 := rfl
  have h1 : (address + (offset + k)) % limit = (address + offset) % limit + k := by
    rw [← Nat.add_assoc, ← Nat.mod_add_mod, Nat.mod_eq_of_lt (by omega)]
  refine ⟨h1, ?_, ?_⟩
  all_goals
    rw [hps] at hc ⊢
    generalize (address + offset) % limit = x at hc hc2 ⊢
    omega

private theorem writePages_sized (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address : Nat) (data : ByteArray) (offset : Nat) (h : Sized pages) :
    Sized (writePages limit hlimit pages address data offset) := by
  induction hn : data.size - offset using Nat.strongRecOn generalizing pages offset with
  | ind n ih =>
    rw [writePages]
    split
    · exact h
    · rename_i hdone
      have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
      have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
      refine ih _ (by omega) _ _ ?_ rfl
      intro index page hp
      simp only [Std.TreeMap.get?_eq_getElem?] at hp
      rw [Std.TreeMap.getElem?_insert] at hp
      split at hp
      · simp only [Option.some.injEq] at hp
        subst hp
        exact (chunk_page data _ offset _ _ (existing_size h _) (by omega) (by omega)).1
      · exact h index page (by simpa only [Std.TreeMap.get?_eq_getElem?] using hp)

/-- Addresses the rest of the region never touches keep their contents. -/
private theorem writePages_outside (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address : Nat) (data : ByteArray) (offset a : Nat) (h : Sized pages)
    (hne : ∀ j, offset ≤ j → j < data.size → (address + j) % limit ≠ a) :
    readAt (writePages limit hlimit pages address data offset) a = readAt pages a := by
  induction hn : data.size - offset using Nat.strongRecOn generalizing pages offset with
  | ind n ih =>
    rw [writePages]
    split
    · rfl
    · rename_i hdone
      have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
      have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
      have hps : pageSize = 256 := rfl
      simp only
      generalize hcount : min (min (pageSize - (address + offset) % limit % pageSize) (data.size - offset))
        (limit - (address + offset) % limit) = count
      have hpos : 0 < count := by omega
      rw [ih _ (by omega) _ _ ?_ (fun j hj hlt => hne j (by omega) hlt) rfl, readAt_insert]
      · split
        · rename_i hindex
          obtain ⟨hsize, hget⟩ := chunk_page data ((pages.get? ((address + offset) % limit / pageSize)).getD freshPage)
            offset count ((address + offset) % limit % pageSize) (existing_size h _) (by omega) (by omega)
          rw [hget _ (Nat.mod_lt _ (by decide))]
          rw [ite_eq_right, ← hindex, readAt_existing]
          rintro ⟨hlo, hhi⟩
          apply hne (offset + (a % pageSize - (address + offset) % limit % pageSize)) (by omega) (by omega)
          have hk := chunk_address (address := address) (offset := offset) (limit := limit) (count := count)
            (k := a % pageSize - (address + offset) % limit % pageSize) (by omega) (by omega) (by omega)
          rw [hk.1]
          have d1 := Nat.div_add_mod a pageSize
          have d2 := Nat.div_add_mod ((address + offset) % limit) pageSize
          rw [hindex] at d1
          omega
        · rfl
      · intro index page hp
        simp only [Std.TreeMap.get?_eq_getElem?] at hp
        rw [Std.TreeMap.getElem?_insert] at hp
        split at hp
        · simp only [Option.some.injEq] at hp
          subst hp
          exact (chunk_page data _ offset _ _ (existing_size h _) (by omega) (by omega)).1
        · exact h index page (by simpa only [Std.TreeMap.get?_eq_getElem?] using hp)

private theorem writePages_inside (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address : Nat) (data : ByteArray) (offset j : Nat) (h : Sized pages) (hsize : data.size ≤ limit)
    (hlo : offset ≤ j) (hj : j < data.size) :
    readAt (writePages limit hlimit pages address data offset) ((address + j) % limit) = data[j]! := by
  induction hn : data.size - offset using Nat.strongRecOn generalizing pages offset with
  | ind n ih =>
    rw [writePages]
    rw [ite_eq_right (by omega)]
    have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
    have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
    have hps : pageSize = 256 := rfl
    simp only
    generalize hcount : min (min (pageSize - (address + offset) % limit % pageSize) (data.size - offset))
      (limit - (address + offset) % limit) = count
    have hpos : 0 < count := by omega
    have hsized : Sized (pages.insert ((address + offset) % limit / pageSize)
        (if count = pageSize then data.extract offset (offset + count) else
          ((pages.get? ((address + offset) % limit / pageSize)).getD freshPage).extract 0 ((address + offset) % limit % pageSize) ++
            data.extract offset (offset + count) ++
            ((pages.get? ((address + offset) % limit / pageSize)).getD freshPage).extract
              ((address + offset) % limit % pageSize + count) pageSize)) := by
      intro index page hp
      simp only [Std.TreeMap.get?_eq_getElem?] at hp
      rw [Std.TreeMap.getElem?_insert] at hp
      split at hp
      · simp only [Option.some.injEq] at hp
        subst hp
        exact (chunk_page data _ offset _ _ (existing_size h _) (by omega) (by omega)).1
      · exact h index page (by simpa only [Std.TreeMap.get?_eq_getElem?] using hp)
    by_cases hin : j < offset + count
    · rw [writePages_outside limit hlimit _ address data (offset + count) _ hsized (by
        intro j' hj1 hj2
        have : address + j < address + j' := by omega
        exact (mod_ne_of_lt this (by omega)).symm)]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hlo
      have hk := chunk_address (address := address) (offset := offset) (limit := limit) (count := count)
        (k := k) (by omega) (by omega) (by omega)
      rw [hk.1, readAt_insert, ite_eq_left hk.2.1, hk.2.2]
      obtain ⟨_, hget⟩ := chunk_page data ((pages.get? ((address + offset) % limit / pageSize)).getD freshPage)
        offset count ((address + offset) % limit % pageSize) (existing_size h _) (by omega) (by omega)
      rw [hget _ (by omega), ite_eq_left (by omega)]
      congr 2
      omega
    · exact ih _ (by omega) _ _ hsized (by omega) rfl

theorem writeRegion_pagesSized {memory : Memory addressWidth} (h : PagesSized memory) (address : Nat)
    (data : ByteArray) : PagesSized (writeRegion memory address data) :=
  writePages_sized _ _ _ _ _ _ h

/-- Every byte of a region lands at its wrapped address, provided the region does not overlap itself. -/
theorem readByte_writeRegion_inside {memory : Memory addressWidth} (h : PagesSized memory) (address : Nat)
    (data : ByteArray) (hsize : data.size ≤ 2 ^ addressWidth) {j : Nat} (hj : j < data.size)
    (target : BitVec addressWidth) (ht : target.toNat = (address + j) % 2 ^ addressWidth) :
    readByte (writeRegion memory address data) target = data[j]! := by
  have := writePages_inside (2 ^ addressWidth) (Nat.two_pow_pos _) memory.pages address data 0 j h hsize
    (Nat.zero_le _) hj
  rw [← ht] at this
  exact this

/-- Addresses outside a region keep their contents. -/
theorem readByte_writeRegion_outside {memory : Memory addressWidth} (h : PagesSized memory) (address : Nat)
    (data : ByteArray) (target : BitVec addressWidth)
    (hne : ∀ j, j < data.size → (address + j) % 2 ^ addressWidth ≠ target.toNat) :
    readByte (writeRegion memory address data) target = readByte memory target :=
  writePages_outside (2 ^ addressWidth) (Nat.two_pow_pos _) memory.pages address data 0 target.toNat h
    (fun j _ hlt => hne j hlt)

private theorem toNat_add_ofNat (address : BitVec addressWidth) (k : Nat) :
    (address + BitVec.ofNat addressWidth k).toNat = (address.toNat + k) % 2 ^ addressWidth := by
  simp [BitVec.toNat_add]

private theorem byteArray_toList (page : ByteArray) : page.toList = page.data.toList := by
  have key : ∀ i r, i ≤ page.size → ByteArray.toList.loop page i r =
      r.reverse ++ page.data.toList.drop i := by
    intro i r hi
    induction hn : page.size - i using Nat.strongRecOn generalizing i r with
    | ind n ih =>
      rw [ByteArray.toList.loop]
      split
      · rename_i hlt
        rw [ih _ (by omega) (i + 1) _ (by omega) rfl]
        have : page.data.toList.drop i = page.get! i :: page.data.toList.drop (i + 1) := by
          have hd : i < page.data.toList.length := by simpa using hlt
          rw [List.drop_eq_getElem_cons hd]
          congr 1
          obtain ⟨d⟩ := page
          show d.toList[i] = d[i]!
          rw [getElem!_pos d i (by simpa using hd)]
          simp
        rw [this]
        simp
      · have : page.data.toList.drop i = [] := by
          apply List.drop_eq_nil_of_le
          simp only [Array.length_toList]
          exact (by omega : page.size ≤ i)
        simp [this]
  simpa [ByteArray.toList] using key 0 [] (Nat.zero_le _)

private theorem foldl_push (bytes : List UInt8) (output : Array UInt8) :
    (bytes.foldl (init := output) fun output byte => output.push byte).toList = output.toList ++ bytes := by
  induction bytes generalizing output with
  | nil => simp
  | cons byte rest ih => simp [ih]

/-- `readPages` emits exactly the byte at each wrapped address, in order. -/
private theorem readPages_toList (limit : Nat) (hlimit : 0 < limit) (pages : Std.TreeMap Nat ByteArray)
    (address size offset : Nat) (output : Array UInt8) (h : Sized pages) :
    (readPages limit hlimit pages address size offset output).toList =
      output.toList ++ (List.range' offset (size - offset)).map fun j => readAt pages ((address + j) % limit) := by
  induction hn : size - offset using Nat.strongRecOn generalizing offset output with
  | ind n ih =>
    subst hn
    rw [readPages]
    split
    · have : size - offset = 0 := by omega
      simp [this]
    · rename_i hdone
      have h1 : (address + offset) % limit < limit := Nat.mod_lt _ hlimit
      have h2 : (address + offset) % limit % pageSize < pageSize := Nat.mod_lt _ (by decide)
      have hps : pageSize = 256 := rfl
      simp only
      generalize hcount : min (min (pageSize - (address + offset) % limit % pageSize) (size - offset))
        (limit - (address + offset) % limit) = count
      have hpos : 0 < count := by omega
      rw [ih _ (by omega) _ _ rfl, foldl_push, byteArray_toList, List.append_assoc]
      congr 1
      have hsplit : size - offset = count + (size - (offset + count)) := by omega
      conv => rhs; rw [hsplit]
      rw [← List.range'_append_1, List.map_append]
      congr 1
      have hsz := existing_size h ((address + offset) % limit / pageSize)
      have hlen : (((pages.get? ((address + offset) % limit / pageSize)).getD freshPage).extract
          ((address + offset) % limit % pageSize) ((address + offset) % limit % pageSize + count)).size = count := by
        rw [ByteArray.size_extract, hsz]
        omega
      apply List.ext_getElem
      · simp only [Array.length_toList, List.length_map, List.length_range']
        exact hlen
      · intro k hk1 hk2
        have hk : k < count := by simpa using hk2
        have hchunk := chunk_address (address := address) (offset := offset) (limit := limit) (count := count)
          (k := k) hk (by omega) (by omega)
        simp only [List.getElem_map, List.getElem_range', Nat.one_mul, Array.getElem_toList]
        have hget := get!_extract ((pages.get? ((address + offset) % limit / pageSize)).getD freshPage)
          ((address + offset) % limit % pageSize) ((address + offset) % limit % pageSize + count) k
          (by omega) (by omega)
        rw [getElem!_pos _ k (by omega)] at hget
        refine Eq.trans hget ?_
        rw [hchunk.1, ← readAt_existing, hchunk.2.1, hchunk.2.2]

/-- `readRegion` returns the byte at every wrapped address of the region, in order. -/
theorem readRegion_toList {memory : Memory addressWidth} (h : PagesSized memory) (address size : Nat) :
    (readRegion memory address size).data.toList =
      (List.range size).map fun j => readByte memory (BitVec.ofNat addressWidth (address + j)) := by
  have := readPages_toList (2 ^ addressWidth) (Nat.two_pow_pos _) memory.pages address size 0 #[] h
  simp only [readRegion]
  rw [this, List.range_eq_range']
  simp
  intro a _
  simp only [readByte, readAt, BitVec.toNat_ofNat]
  rfl

theorem readRegion_size {memory : Memory addressWidth} (h : PagesSized memory) (address size : Nat) :
    (readRegion memory address size).size = size := by
  have := congrArg List.length (readRegion_toList h address size)
  simpa using this

/-- A region reads back unchanged, including one that wraps past the top of the address space. -/
theorem readRegion_writeRegion {memory : Memory addressWidth} (h : PagesSized memory) (address : Nat)
    (data : ByteArray) (hsize : data.size ≤ 2 ^ addressWidth) :
    readRegion (writeRegion memory address data) address data.size = data := by
  have hsized := writeRegion_pagesSized h address data
  have key : (readRegion (writeRegion memory address data) address data.size).data.toList = data.data.toList := by
    rw [readRegion_toList hsized]
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, Array.length_toList]
      rfl
    · intro k h1 h2
      have hk : k < data.size := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [readByte_writeRegion_inside h address data hsize hk _ (BitVec.toNat_ofNat _ _)]
      simp only [Array.getElem_toList]
      exact (page_getBang data k).trans (getElem!_pos data.data k hk)
  have hd := Array.toList_inj.mp key
  exact congrArg ByteArray.mk hd

private theorem foldl_bytes (v n init : Nat) :
    (((List.range n).map (byteAt v)).reverse).foldl (fun result byte => result * 256 + byte.toNat) init =
      init * 256 ^ n + v % 256 ^ n := by
  induction n generalizing init with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.reverse_append]
    simp only [List.map_cons, List.map_nil, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.foldl_cons]
    rw [ih]
    have hb : (byteAt v n).toNat = v / 256 ^ n % 256 := by
      simp [byteAt, Nat.shiftRight_eq_div_pow, Nat.pow_mul]
    rw [hb, Nat.mod_pow_succ, Nat.pow_succ]
    grind

private theorem image_size (value : BitVec valueWidth) (endian : Endian) (size : Nat) :
    (ByteArray.mk (image value endian size).toArray).size = size := by
  show (image value endian size).toArray.size = size
  simp [image]

theorem write_eq {memory : Memory addressWidth} {address : BitVec addressWidth} {value : BitVec valueWidth}
    (hs : size * 8 = valueWidth) (endian : Endian) :
    Memory.write memory address value endian size =
      .ok (writeRegion memory address.toNat (ByteArray.mk (image value endian size).toArray)) := by
  simp [Memory.write, image, hs, Pure.pure, Except.pure]
  rfl

/-- The width check is the only way `Memory.write` can fail. -/
theorem write_error_of_ne {memory : Memory addressWidth} {address : BitVec addressWidth}
    (value : BitVec valueWidth) (endian : Endian) {size : Nat} (h : size * 8 ≠ valueWidth) :
    Memory.write memory address value endian size =
      .error s!"expected {size * 8} bits, actual {valueWidth}" := by
  simp [Memory.write, h]

theorem write_pagesSized {memory : Memory addressWidth} (h : PagesSized memory) {address : BitVec addressWidth}
    {value : BitVec valueWidth} {endian : Endian} {size : Nat} {updated : Memory addressWidth}
    (hw : Memory.write memory address value endian size = .ok updated) : PagesSized updated := by
  by_cases hs : size * 8 = valueWidth
  · rw [write_eq hs] at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    exact writeRegion_pagesSized h _ _
  · rw [write_error_of_ne value endian hs] at hw
    simp at hw

/-- Read-after-write for the real `Memory.write`, in both endiannesses and wherever the value lies,
including across the top of the address space, as long as it does not overlap itself. -/
theorem read_write {memory : Memory addressWidth} (h : PagesSized memory) (address : BitVec addressWidth)
    (value : BitVec (size * 8)) (endian : Endian) (hsize : size ≤ 2 ^ addressWidth) {updated : Memory addressWidth}
    (hw : Memory.write memory address value endian size = .ok updated) :
    Memory.read updated address endian size = value := by
  rw [write_eq rfl] at hw
  simp only [Except.ok.injEq] at hw
  subst hw
  have hlen : (image value endian size).length = size := by simp [image]
  have hdata := image_size value endian size
  have hbytes : (List.range size).map (fun offset =>
      readByte (writeRegion memory address.toNat (ByteArray.mk (image value endian size).toArray))
        (address + BitVec.ofNat addressWidth offset)) = image value endian size := by
    apply List.ext_getElem
    · simp [hlen]
    · intro k h1 h2
      have hk : k < size := by simpa using h1
      simp only [List.getElem_map, List.getElem_range]
      rw [readByte_writeRegion_inside h address.toNat _ (by omega) (j := k) (by omega) _ (toNat_add_ofNat address k)]
      rw [page_getBang]
      show (image value endian size).toArray[k]! = _
      rw [getElem!_pos _ k (by simpa using h2)]
      simp
  have hvalue : BitVec.ofNat (size * 8) (0 * 256 ^ size + value.toNat % 256 ^ size) = value := by
    apply BitVec.eq_of_toNat_eq
    have hp : (256 : Nat) ^ size = 2 ^ (size * 8) := by
      rw [Nat.mul_comm, Nat.pow_mul]
    simp [hp, Nat.mod_eq_of_lt value.isLt]
  conv => rhs; rw [← hvalue]
  simp only [Memory.read, hbytes]
  congr 1
  rw [← foldl_bytes]
  cases endian with
  | little => simp [image]
  | big =>
    congr 1
    simp only [image]
    apply List.ext_getElem
    · simp
    · intro k h1 h2
      simp at h1
      simp [List.getElem_reverse]

/-- A write leaves every byte outside the written range unchanged. -/
theorem readByte_write_frame {memory : Memory addressWidth} (h : PagesSized memory)
    {address other : BitVec addressWidth} {value : BitVec valueWidth} {endian : Endian} {size : Nat}
    {updated : Memory addressWidth} (hw : Memory.write memory address value endian size = .ok updated)
    (hne : ∀ k, k < size → other ≠ address + BitVec.ofNat addressWidth k) :
    readByte updated other = readByte memory other := by
  by_cases hs : size * 8 = valueWidth
  · rw [write_eq hs] at hw
    simp only [Except.ok.injEq] at hw
    subst hw
    apply readByte_writeRegion_outside h
    intro j hj he
    have hj' : j < size := by rwa [image_size] at hj
    apply hne j hj'
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat, he]
  · rw [write_error_of_ne value endian hs] at hw
    simp at hw

/-- `Memory.read` and `readRegion` see the same bytes. -/
theorem readRegion_eq_readBytes {memory : Memory addressWidth} (h : PagesSized memory) (address : BitVec addressWidth)
    (size : Nat) :
    (readRegion memory address.toNat size).data.toList =
      (List.range size).map fun offset => readByte memory (address + BitVec.ofNat addressWidth offset) := by
  rw [readRegion_toList h]
  apply List.map_congr_left
  intro k _
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [toNat_add_ofNat, BitVec.toNat_ofNat]

/-- Memory reads ignore writes outside the accessed range. -/
theorem read_writeByte_other (memory : Memory addressWidth) (address other : BitVec addressWidth)
    (endian : Endian) (size : Nat) (value : UInt8)
    (hne : ∀ k, k < size → other ≠ address + BitVec.ofNat addressWidth k) :
    Memory.read (writeByte memory other value) address endian size = Memory.read memory address endian size := by
  have : ((List.range size).map fun offset =>
      readByte (writeByte memory other value) (address + BitVec.ofNat addressWidth offset)) =
      (List.range size).map fun offset =>
      readByte memory (address + BitVec.ofNat addressWidth offset) := by
    apply List.map_congr_left
    intro k hk
    exact readByte_writeByte_other memory (hne k (List.mem_range.mp hk)).symm value
  simp only [Memory.read, this]

/-- One-byte reads are endian-independent and equal `readByte`. -/
theorem read_one (memory : Memory addressWidth) (address : BitVec addressWidth) (endian : Endian) :
    (Memory.read memory address endian 1).toNat = (readByte memory address).toNat := by
  have hlt := (readByte memory address).toNat_lt
  cases endian <;> simp [Memory.read]

/-- Big- and little-endian reads see the same bytes in reversed order. -/
theorem read_big_eq_foldl (memory : Memory addressWidth) (address : BitVec addressWidth) (size : Nat) :
    Memory.read memory address .big size = BitVec.ofNat (size * 8)
      (((List.range size).map fun offset =>
        readByte memory (address + BitVec.ofNat addressWidth offset)).foldl
          (fun result byte => result * 256 + byte.toNat) 0) := rfl

/-! ### Values -/

theorem asBits_eq_ok_iff (value : Value) (bits : Σ width, BitVec width) :
    value.asBits = .ok bits ↔ value = .bits bits.2 := by
  obtain ⟨w, b⟩ := bits
  cases value with
  | bits x =>
    simp only [Value.asBits, Except.ok.injEq, Value.bits.injEq]
    constructor
    · intro h; cases h; exact ⟨rfl, HEq.rfl⟩
    · rintro ⟨rfl, h⟩; cases h; rfl
  | memory m => simp [Value.asBits]
  | undefined => simp [Value.asBits]

/-- A value's reported type determines the shape of what it holds. -/
theorem type_imm_iff (value : Value) (width : Nat) :
    value.type = .imm width ↔ ∃ bits : BitVec width, value = .bits bits := by
  cases value with
  | @bits w b =>
    simp only [Value.type, Typ.imm.injEq]
    constructor
    · rintro rfl; exact ⟨b, rfl⟩
    · rintro ⟨x, hx⟩; cases hx; rfl
  | memory m => simp [Value.type]
  | undefined => simp [Value.type]

end MemoryLaws

namespace SexpLaws
open Bap.Sexp
open_private Bap.Core.Sexp Bap.Sexp.escape Bap.Sexp.parseEscaped Bap.Sexp.parseQuoted Bap.Sexp.parseAtom Bap.Sexp.needsQuotes

theorem expectTagged_tagged (tag : String) (args : List Sexp) :
    expectTagged tag args.length (tagged tag args) = .ok args := by
  simp [expectTagged, tagged, asList, bind, Except.bind]

theorem expectTagged_length {tag : String} {arity : Nat} {value : Sexp} {args : List Sexp}
    (h : expectTagged tag arity value = .ok args) : args.length = arity ∧ value = tagged tag args := by
  cases value with
  | atom name => simp [expectTagged, asList, bind, Except.bind] at h
  | list items =>
    simp only [expectTagged, asList, bind, Except.bind] at h
    split at h
    · split at h
      · rename_i hif
        simp only [Except.ok.injEq] at h
        subst h
        simp_all [tagged]
      · simp at h
    · simp at h

theorem nat_atom_toString (n : Nat) : Sexp.nat (.atom (toString n)) = .ok n := by
  have hdigits : ∀ c ∈ (toString n).toList, c.isDigit = true := by
    intro c hc
    rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  have hisNat : (toString n).isNat = true :=
    String.isNat_of_isDigit (by simp [Nat.toString_eq_repr, Nat.repr_ne_empty]) hdigits
  have hfilter : (toString n).toList.filter (· != '_') = (toString n).toList := by
    apply List.filter_eq_self.mpr
    intro c hc
    have := hdigits c hc
    simp only [bne_iff_ne, ne_eq]
    rintro rfl
    simp at this
  have : (toString n).toNat? = some n := by
    rw [String.toNat?_eq_some_ofDigitChars hisNat, hfilter, Nat.toString_eq_repr, Nat.toList_repr,
      Nat.ofDigitChars_ten_toDigits]
  simp [Sexp.nat, asAtom, this, bind, Except.bind]

theorem dropComment_suffix (input : List Char) : dropComment input <:+ input := by
  induction input with
  | nil => simp [dropComment]
  | cons c rest ih =>
    by_cases h : c = '\n'
    · subst h; simp [dropComment]
    · simp only [dropComment, h]
      exact ih.trans (List.suffix_cons _ _)

/-- A comment ends after the first newline, whatever follows it. -/
theorem dropComment_append (comment rest : List Char) (h : '\n' ∉ comment) :
    dropComment (comment ++ '\n' :: rest) = rest := by
  induction comment with
  | nil => simp [dropComment]
  | cons c tail ih =>
    simp only [List.mem_cons, not_or] at h
    have hc : c ≠ '\n' := fun e => h.1 e.symm
    simp only [List.cons_append, dropComment, hc]
    exact ih h.2

/-- Every character the printer escapes is read back by the quoted-atom parser. -/
private theorem parseQuoted_escape (fuel : Nat) (chars rest : List Char)
    (hfuel : chars.length < fuel) :
    parseQuoted fuel (chars.flatMap escape ++ '"' :: rest) = .ok (String.ofList chars, rest) := by
  induction chars generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp at hfuel
    | succ f => simp [parseQuoted]
  | cons c tail ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ f =>
      simp only [List.length_cons, Nat.add_lt_add_iff_right] at hfuel
      have iht := ih f hfuel
      have happend : String.ofList [c] ++ String.ofList tail = String.ofList (c :: tail) := by
        simp [← String.toList_inj]
      simp only [List.flatMap_cons, List.append_assoc]
      by_cases h1 : c = '"'
      · subst h1
        simp [escape, parseQuoted, iht, parseEscaped, bind, Except.bind, ← happend]
      by_cases h2 : c = '\\'
      · subst h2
        simp [escape, parseQuoted, iht, parseEscaped, bind, Except.bind, ← happend]
      by_cases h3 : c = '\n'
      · subst h3
        simp [escape, parseQuoted, iht, parseEscaped, bind, Except.bind, ← happend]
      by_cases h4 : c = '\r'
      · subst h4
        simp [escape, parseQuoted, iht, parseEscaped, bind, Except.bind, ← happend]
      by_cases h5 : c = '\t'
      · subst h5
        simp [escape, parseQuoted, iht, parseEscaped, bind, Except.bind, ← happend]
      have hesc : escape c = [c] := by simp [escape, h1, h2, h3, h4, h5]
      simp [hesc, parseQuoted, iht, h1, h2, bind, Except.bind, ← happend]

/-- Atoms the printer leaves unquoted contain no delimiter the atom parser would stop at. -/
private theorem needsQuotes_false_iff (value : String) :
    needsQuotes value = false ↔ value.toList ≠ [] ∧ value.toList.head? ≠ some '\'' ∧ ∀ c ∈ value.toList,
      c.isWhitespace = false ∧ c ≠ '(' ∧ c ≠ ')' ∧ c ≠ ';' ∧ c ≠ '"' ∧ c ≠ '\\' := by
  simp [needsQuotes, String.isEmpty_iff]

private def Unquoted (c : Char) : Bool :=
  !(c.isWhitespace || c == '(' || c == ')' || c == ';')

private theorem parseAtom_delimited (chars rest : List Char)
    (hchars : ∀ c ∈ chars, Unquoted c = true)
    (hrest : ∀ c, rest.head? = some c → Unquoted c = false) :
    parseAtom (chars ++ rest) = (String.ofList chars, rest) := by
  have htake : (chars ++ rest).takeWhile (fun c => !(c.isWhitespace ∨ c = '(' ∨ c = ')' ∨ c = ';')) = chars := by
    induction chars with
    | nil =>
      cases rest with
      | nil => rfl
      | cons d tail =>
        have := hrest d rfl
        simp only [Unquoted] at this
        simp [List.takeWhile, this]
        grind
    | cons c tail ih =>
      have hc := hchars c (by simp)
      simp only [Unquoted] at hc
      have ih' := ih (fun d hd => hchars d (List.mem_cons_of_mem _ hd))
      have : (!decide (c.isWhitespace = true ∨ c = '(' ∨ c = ')' ∨ c = ';')) = true := by
        grind
      simp only [List.cons_append, List.takeWhile, ih', this]
  simp only [parseAtom, htake]
  simp

private theorem skipSpace_nil : skipSpace [] = [] := by
  rw [skipSpace]

private theorem skipSpace_whitespace (c : Char) (rest : List Char) (h : c.isWhitespace = true) :
    skipSpace (c :: rest) = skipSpace rest := by
  rw [skipSpace]
  simp [h]

private theorem skipSpace_other (c : Char) (rest : List Char) (h1 : c.isWhitespace = false) (h2 : c ≠ ';') :
    skipSpace (c :: rest) = c :: rest := by
  rw [skipSpace]
  simp [h1, h2]

/-- Skipped input is always a suffix of the input, and starts with a significant character. -/
theorem skipSpace_suffix (input : List Char) : skipSpace input <:+ input := by
  induction h : input.length using Nat.strongRecOn generalizing input with
  | ind n ih =>
    cases input with
    | nil => simp [skipSpace]
    | cons c rest =>
      subst h
      rw [skipSpace]
      split
      · exact (ih _ (by simp) rest rfl).trans (List.suffix_cons _ _)
      · split
        · have hle := dropComment_length_le rest
          exact (ih _ (by simp; omega) _ rfl).trans
            ((dropComment_suffix rest).trans (List.suffix_cons _ _))
        · exact List.suffix_refl _

theorem skipSpace_head {input : List Char} {c : Char} {rest : List Char}
    (h : skipSpace input = c :: rest) : c.isWhitespace = false ∧ c ≠ ';' := by
  induction hn : input.length using Nat.strongRecOn generalizing input with
  | ind n ih =>
    cases input with
    | nil => simp [skipSpace] at h
    | cons d tail =>
      subst hn
      rw [skipSpace] at h
      split at h
      · exact ih _ (by simp) h rfl
      · split at h
        · have hle := dropComment_length_le tail
          exact ih _ (by simp; omega) h rfl
        · simp only [List.cons.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          rename_i h1 h2
          exact ⟨by simpa using h1, h2⟩

private def size : Sexp → Nat
  | .atom _ => 1
  | .list items => 1 + sizeList items
where
  sizeList : List Sexp → Nat
    | [] => 1
    | item :: rest => 1 + size item + sizeList rest

private def renderChars (value : Sexp) : List Char := (render value).toList

private def renderItems (items : List Sexp) : List Char :=
  (String.intercalate " " (items.map render)).toList

private theorem renderChars_list (items : List Sexp) :
    renderChars (.list items) = '(' :: (renderItems items ++ [')']) := by
  simp [renderChars, renderItems, render]

private theorem renderItems_nil : renderItems [] = [] := by
  simp [renderItems]

private theorem renderItems_single (item : Sexp) : renderItems [item] = renderChars item := by
  simp [renderItems, renderChars]

private theorem renderItems_cons_cons (first second : Sexp) (rest : List Sexp) :
    renderItems (first :: second :: rest) = renderChars first ++ ' ' :: renderItems (second :: rest) := by
  simp [renderItems, renderChars, String.intercalate_cons_cons]

private theorem renderChars_atom_quoted {value : String} (h : needsQuotes value = true) :
    renderChars (.atom value) = '"' :: (value.toList.flatMap escape ++ ['"']) := by
  simp [renderChars, render, h]

private theorem renderChars_atom_plain {value : String} (h : needsQuotes value = false) :
    renderChars (.atom value) = value.toList := by
  simp [renderChars, render, h]

/-- First character of a rendering: never whitespace, comment or closing parenthesis. -/
private theorem renderChars_head (value : Sexp) :
    ∃ c tail, renderChars value = c :: tail ∧ c.isWhitespace = false ∧ c ≠ ';' ∧ c ≠ ')' := by
  cases value with
  | list items =>
    rw [renderChars_list]
    exact ⟨_, _, rfl, by decide, by decide, by decide⟩
  | atom name =>
    cases hq : needsQuotes name with
    | true =>
      rw [renderChars_atom_quoted hq]
      exact ⟨_, _, rfl, by decide, by decide, by decide⟩
    | false =>
      rw [renderChars_atom_plain hq]
      obtain ⟨hne, _, hgood⟩ := (needsQuotes_false_iff name).mp hq
      cases hl : name.toList with
      | nil => exact absurd hl hne
      | cons c tail =>
        have := hgood c (by simp [hl])
        exact ⟨c, tail, rfl, this.1, this.2.2.2.1, this.2.2.1⟩

private theorem length_le_escape (chars : List Char) :
    chars.length ≤ (chars.flatMap escape).length := by
  induction chars with
  | nil => simp
  | cons c tail ih =>
    have : 1 ≤ (escape c).length := by
      simp only [escape]
      split <;> simp
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    omega

private theorem parseList_space (fuel : Nat) (rest : List Char) :
    parseList fuel (' ' :: rest) = parseList fuel rest := by
  cases fuel with
  | zero => simp [parseList]
  | succ f => simp only [parseList, skipSpace_whitespace ' ' rest (by decide)]

private theorem parseList_item {c : Char} (h1 : c.isWhitespace = false) (h2 : c ≠ ';')
    (h3 : c ≠ ')') (tail : List Char) (f : Nat) :
    parseList (f + 1) (c :: tail) = (do
      let (item, rest) ← parseOne f (c :: tail)
      let (items, remaining) ← parseList f rest
      .ok (item :: items, remaining)) := by
  rw [parseList, skipSpace_other c tail h1 h2]
  split <;> simp_all

mutual
  private theorem parseOne_render :
      (value : Sexp) → (fuel : Nat) → size value ≤ fuel → (rest : List Char) →
      (∀ c, rest.head? = some c → Unquoted c = false) →
      parseOne fuel (renderChars value ++ rest) = .ok (value, rest)
    | .atom name, fuel, hf, rest, hr => by
      cases fuel with
      | zero => simp [size] at hf
      | succ f =>
        cases hq : needsQuotes name with
        | true =>
          rw [renderChars_atom_quoted hq]
          have hskip := skipSpace_other '"' ((name.toList.flatMap escape ++ ['"']) ++ rest) (by decide) (by decide)
          have hq2 := parseQuoted_escape
            (((name.toList.flatMap escape ++ ['"']) ++ rest).length + 1) name.toList rest (by
              have := length_le_escape name.toList
              simp only [List.length_append, List.length_cons, List.length_nil]
              omega)
          simp only [List.append_assoc, List.cons_append, List.nil_append] at hskip hq2 ⊢
          rw [parseOne, hskip]
          simp only [bind, Except.bind, hq2]
          simp
        | false =>
          rw [renderChars_atom_plain hq]
          obtain ⟨hne, hhead, hgood⟩ := (needsQuotes_false_iff name).mp hq
          cases hl : name.toList with
          | nil => exact absurd hl hne
          | cons c tail =>
            have hc := hgood c (by simp [hl])
            have hc' : c ≠ '\'' := fun e => hhead (by simp [hl, e])
            have hskip := skipSpace_other c (tail ++ rest) hc.1 hc.2.2.2.1
            have hatom := parseAtom_delimited (c :: tail) rest (by
              intro d hd
              have := hgood d (by simpa [hl] using hd)
              simp [Unquoted, this.1, this.2.1, this.2.2.1, this.2.2.2.1]) hr
            have hname : String.ofList (c :: tail) = name := by rw [← hl]; simp
            rw [hname] at hatom
            simp only [List.cons_append] at hatom ⊢
            rw [parseOne, hskip]
            split <;> simp_all
    | .list items, fuel, hf, rest, _ => by
      cases fuel with
      | zero => simp [size] at hf
      | succ f =>
        have hsize : size.sizeList items ≤ f := by simp [size] at hf; omega
        rw [renderChars_list]
        have hskip := skipSpace_other '(' ((renderItems items ++ [')']) ++ rest) (by decide) (by decide)
        have hl := parseList_render items f hsize rest
        simp only [List.append_assoc, List.cons_append, List.nil_append] at hskip hl ⊢
        rw [parseOne, hskip]
        simp [hl, bind, Except.bind]

  private theorem parseList_render :
      (items : List Sexp) → (fuel : Nat) → size.sizeList items ≤ fuel →
      (rest : List Char) →
      parseList fuel (renderItems items ++ ')' :: rest) = .ok (items, rest)
    | [], fuel, hf, rest => by
      cases fuel with
      | zero => simp [size.sizeList] at hf
      | succ f =>
        rw [renderItems_nil, List.nil_append, parseList, skipSpace_other ')' rest (by decide) (by decide)]
        rfl
    | [item], fuel, hf, rest => by
      cases fuel with
      | zero => simp [size.sizeList] at hf
      | succ f =>
        have hsize : size item ≤ f := by simp [size.sizeList] at hf; omega
        have hnil : size.sizeList [] ≤ f := by simp [size.sizeList] at hf ⊢; omega
        obtain ⟨c, tail, hc, h1, h2, h3⟩ := renderChars_head item
        have hone := parseOne_render item f hsize (')' :: rest) (by
          intro d hd
          simp only [List.head?_cons, Option.some.injEq] at hd
          subst hd
          decide)
        have hnext := parseList_render [] f hnil rest
        rw [renderItems_nil, List.nil_append] at hnext
        rw [renderItems_single]
        rw [hc, List.cons_append] at hone ⊢
        rw [parseList_item h1 h2 h3]
        simp [hone, hnext, bind, Except.bind]
    | first :: second :: more, fuel, hf, rest => by
      cases fuel with
      | zero => simp [size.sizeList] at hf
      | succ f =>
        have hsize : size first ≤ f := by simp [size.sizeList] at hf ⊢; omega
        have hnext : size.sizeList (second :: more) ≤ f := by simp [size.sizeList] at hf ⊢; omega
        obtain ⟨c, tail, hc, h1, h2, h3⟩ := renderChars_head first
        have hone := parseOne_render first f hsize
          (' ' :: (renderItems (second :: more) ++ ')' :: rest)) (by
          intro d hd
          simp only [List.head?_cons, Option.some.injEq] at hd
          subst hd
          decide)
        have hl := parseList_render (second :: more) f hnext rest
        rw [renderItems_cons_cons, List.append_assoc]
        rw [hc, List.cons_append] at hone ⊢
        simp only [List.cons_append]
        rw [parseList_item h1 h2 h3]
        simp [hone, parseList_space, hl, bind, Except.bind]
end

private theorem size_le_render :
    (value : Sexp) → size value + 1 ≤ 2 * (renderChars value).length
  | .atom name => by
    have : 1 ≤ (renderChars (.atom name)).length := by
      obtain ⟨c, tail, hc, _⟩ := renderChars_head (.atom name)
      simp [hc]
    simp only [size]
    omega
  | .list items => by
    have := sizeList_le_render items
    rw [renderChars_list]
    simp only [size, List.length_cons, List.length_append, List.length_nil]
    omega
where
  sizeList_le_render : (items : List Sexp) → size.sizeList items ≤ 2 * (renderItems items).length + 1
    | [] => by simp [size.sizeList, renderItems_nil]
    | [item] => by
      have := size_le_render item
      rw [renderItems_single]
      simp only [size.sizeList]
      omega
    | first :: second :: more => by
      have h1 := size_le_render first
      have h2 := sizeList_le_render (second :: more)
      rw [renderItems_cons_cons]
      simp only [size.sizeList] at h2 ⊢
      simp only [List.length_append, List.length_cons]
      omega

/-- Printer/parser round-trip: every S-expression, including atoms that are empty or that start
with a quote or contain delimiters, parses back to itself. -/
theorem parse_render (value : Sexp) : parse (render value) = .ok value := by
  have hsize := size_le_render value
  have hone := parseOne_render value ((render value).toList.length * 2 + 2) (by
    simp only [renderChars] at hsize
    omega) [] (by simp)
  simp only [renderChars, List.append_nil] at hone
  simp [parse, hone, skipSpace_nil, bind, Except.bind]

/-- `toString` on S-expressions is therefore injective. -/
theorem render_injective {left right : Sexp} (h : render left = render right) : left = right := by
  have := parse_render left
  rw [h, parse_render right] at this
  simpa [eq_comm] using this

end SexpLaws

end Bap.Proofs.Core
