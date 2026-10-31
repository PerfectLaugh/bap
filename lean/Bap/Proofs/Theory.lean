import Lean.Elab.Command
import Bap.Theory.Effect
import Bap.Theory.Value
import Bap.Theory.Target
import Bap.Theory.IEEE754

/-- Brings a private production definition into scope under a local alias. -/
local elab "open_private " mod:ident p:ident " as " a:ident : command => do
  let priv := Lean.mkPrivateNameCore mod.getId p.getId
  unless (← Lean.getEnv).contains priv do Lean.throwError "no private name {priv}"
  Lean.modifyEnv (Lean.addAlias · ((← Lean.getCurrNamespace) ++ a.getId) priv)

namespace Bap.Proofs.Theory

private theorem nodup_eraseDups [BEq α] [LawfulBEq α] (values : List α) : values.eraseDups.Nodup := by
  generalize hn : values.length = n
  induction n using Nat.strongRecOn generalizing values with
  | _ n ih =>
    cases values with
    | nil => simp
    | cons head tail =>
      rw [List.eraseDups_cons]
      have hlen : (tail.filter (· != head)).length < n := by
        have := List.length_filter_le (· != head) tail
        simp at hn
        omega
      refine List.nodup_cons.mpr ⟨?_, ih _ hlen _ rfl⟩
      simp [List.mem_eraseDups]

/-! ## Effect sorts -/

namespace EffectLaws

open Bap.Theory.Effect
open Bap.Theory.Effect.EffectSort

open_private Bap.Theory.Effect Bap.Theory.Effect.EffectSort.subset as subset

theorem isTop_both (left right : EffectSort) :
    (both left right).isTop = (left.isTop || right.isTop) := rfl

theorem mem_atoms_both (atom : Atom) (left right : EffectSort) :
    atom ∈ (both left right).atoms ↔ atom ∈ left.atoms ∨ atom ∈ right.atoms := by
  simp [atoms, List.mem_eraseDups]

/-- Inclusion of denotations: `right` is everything, or `left` is a set of atoms all in `right`. -/
def Le (left right : EffectSort) : Prop :=
  right.isTop = true ∨ (left.isTop = false ∧ ∀ atom ∈ left.atoms, atom ∈ right.atoms)

/-- Two effect sorts have the same denotation. -/
def Same (left right : EffectSort) : Prop := Le left right ∧ Le right left

theorem Le.refl (sort : EffectSort) : Le sort sort := by
  cases h : sort.isTop with
  | true => exact Or.inl h
  | false => exact Or.inr ⟨h, fun _ ha => ha⟩

theorem Le.trans {a b c : EffectSort} (hab : Le a b) (hbc : Le b c) : Le a c := by
  rcases hbc with hc | ⟨hb, hbc⟩
  · exact Or.inl hc
  · rcases hab with hb' | ⟨ha, hab⟩
    · rw [hb] at hb'
      cases hb'
    · exact Or.inr ⟨ha, fun atom hm => hbc atom (hab atom hm)⟩

theorem Same.refl (sort : EffectSort) : Same sort sort := ⟨Le.refl _, Le.refl _⟩
theorem Same.symm {left right : EffectSort} (h : Same left right) : Same right left := ⟨h.2, h.1⟩
theorem Same.trans {a b c : EffectSort} (h₁ : Same a b) (h₂ : Same b c) : Same a c :=
  ⟨h₁.1.trans h₂.1, h₂.2.trans h₁.2⟩

theorem bot_le (sort : EffectSort) : Le .bot sort := by
  refine Or.inr ⟨rfl, ?_⟩
  simp [atoms]

theorem le_top (sort : EffectSort) : Le sort .top := Or.inl rfl

theorem top_le_iff (sort : EffectSort) : Le .top sort ↔ sort.isTop = true := by
  simp [Le, isTop]

/-- `both` is the least upper bound of the denotation order. -/
theorem both_le_iff (a b c : EffectSort) : Le (both a b) c ↔ Le a c ∧ Le b c := by
  simp only [Le, isTop_both, Bool.or_eq_false_iff, mem_atoms_both]
  cases hc : c.isTop with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, false_or]
    constructor
    · rintro ⟨⟨ha, hb⟩, h⟩
      exact ⟨⟨ha, fun atom hm => h atom (Or.inl hm)⟩, ⟨hb, fun atom hm => h atom (Or.inr hm)⟩⟩
    · rintro ⟨⟨ha, hac⟩, hb, hbc⟩
      exact ⟨⟨ha, hb⟩, fun atom hm => hm.elim (hac atom) (hbc atom)⟩

theorem le_both_left (a b : EffectSort) : Le a (both a b) := ((both_le_iff a b _).1 (Le.refl _)).1
theorem le_both_right (a b : EffectSort) : Le b (both a b) := ((both_le_iff a b _).1 (Le.refl _)).2

theorem both_mono {a a' b b' : EffectSort} (ha : Le a a') (hb : Le b b') : Le (both a b) (both a' b') :=
  (both_le_iff _ _ _).2 ⟨ha.trans (le_both_left _ _), hb.trans (le_both_right _ _)⟩

theorem both_comm (left right : EffectSort) : Same (both left right) (both right left) :=
  ⟨(both_le_iff _ _ _).2 ⟨le_both_right _ _, le_both_left _ _⟩,
    (both_le_iff _ _ _).2 ⟨le_both_right _ _, le_both_left _ _⟩⟩

theorem both_assoc (a b c : EffectSort) : Same (both (both a b) c) (both a (both b c)) := by
  constructor
  · exact (both_le_iff _ _ _).2 ⟨both_mono (Le.refl _) (le_both_left _ _), (le_both_right _ _).trans (le_both_right _ _)⟩
  · exact (both_le_iff _ _ _).2 ⟨(le_both_left _ _).trans (le_both_left _ _), both_mono (le_both_right _ _) (Le.refl _)⟩

theorem both_idem (sort : EffectSort) : Same (both sort sort) sort :=
  ⟨(both_le_iff _ _ _).2 ⟨Le.refl _, Le.refl _⟩, le_both_left _ _⟩

theorem both_bot_left (sort : EffectSort) : Same (both .bot sort) sort :=
  ⟨(both_le_iff _ _ _).2 ⟨bot_le _, Le.refl _⟩, le_both_right _ _⟩

theorem both_bot_right (sort : EffectSort) : Same (both sort .bot) sort :=
  ⟨(both_le_iff _ _ _).2 ⟨Le.refl _, bot_le _⟩, le_both_left _ _⟩

/-- `top` absorbs on the left, and hence, by commutativity, on the right. -/
theorem both_top_left (sort : EffectSort) : Same (both .top sort) .top :=
  ⟨le_top _, le_both_left _ _⟩

theorem both_top_right (sort : EffectSort) : Same (both sort .top) .top :=
  ⟨le_top _, le_both_right _ _⟩

theorem both_congr {a a' b b' : EffectSort} (ha : Same a a') (hb : Same b b') :
    Same (both a b) (both a' b') :=
  ⟨both_mono ha.1 hb.1, both_mono ha.2 hb.2⟩

private theorem foldl_both_le (sorts : List EffectSort) (init c : EffectSort) :
    Le (sorts.foldl both init) c ↔ Le init c ∧ ∀ sort ∈ sorts, Le sort c := by
  induction sorts generalizing init with
  | nil => simp
  | cons head tail ih =>
    simp only [List.foldl_cons, ih, both_le_iff, List.mem_cons, forall_eq_or_imp, and_assoc]

/-- `union` is the least upper bound of a list. -/
theorem union_le_iff (sorts : List EffectSort) (c : EffectSort) :
    Le (union sorts) c ↔ ∀ sort ∈ sorts, Le sort c := by
  simp [union, foldl_both_le, bot_le]

theorem join_le_iff (left right : List EffectSort) (c : EffectSort) :
    Le (join left right) c ↔ ∀ sort ∈ left ++ right, Le sort c := by
  simp only [join, both_le_iff, union_le_iff, List.mem_append]
  constructor
  · rintro ⟨hl, hr⟩ sort (hs | hs)
    · exact hl sort hs
    · exact hr sort hs
  · intro h
    exact ⟨fun sort hs => h sort (Or.inl hs), fun sort hs => h sort (Or.inr hs)⟩

theorem same_of_le_iff {a b : EffectSort} (h : ∀ c, Le a c ↔ Le b c) : Same a b :=
  ⟨(h b).2 (Le.refl _), (h a).1 (Le.refl _)⟩

theorem mem_atoms_union (atom : Atom) (sorts : List EffectSort) :
    atom ∈ (union sorts).atoms ↔ ∃ sort ∈ sorts, atom ∈ sort.atoms := by
  have key : ∀ init : EffectSort, atom ∈ (sorts.foldl both init).atoms ↔
      atom ∈ init.atoms ∨ ∃ sort ∈ sorts, atom ∈ sort.atoms := by
    induction sorts with
    | nil => simp
    | cons head tail ih =>
      intro init
      simp only [List.foldl_cons, ih, mem_atoms_both, List.mem_cons, exists_eq_or_imp, or_assoc]
  simp [union, key, atoms]

theorem union_perm {left right : List EffectSort} (h : left.Perm right) :
    Same (union left) (union right) :=
  same_of_le_iff fun c => by simp only [union_le_iff, h.mem_iff]

theorem join_comm (left right : List EffectSort) : Same (join left right) (join right left) :=
  both_comm _ _

theorem join_assoc (a b c : List EffectSort) : Same (join (a ++ b) c) (join a (b ++ c)) :=
  same_of_le_iff fun d => by simp only [join_le_iff, List.append_assoc]

theorem join_nil_nil : Same (join [] []) .bot :=
  same_of_le_iff fun c => by simp [join_le_iff, bot_le]

theorem atoms_nodup (sort : EffectSort) : sort.atoms.Nodup := by
  cases sort with
  | bot => simp [atoms]
  | top => simp [atoms]
  | atom value => simp [atoms]
  | both left right => exact nodup_eraseDups _

theorem data_ne_ctrl (left right : String) : data left ≠ ctrl right := by
  simp [data, ctrl]

theorem data_injective {left right : String} (h : data left = data right) : left = right := by
  simpa [data] using h

theorem ctrl_injective {left right : String} (h : ctrl left = ctrl right) : left = right := by
  simpa [ctrl] using h

private theorem subset_iff (left right : List Atom) :
    subset left right = true ↔ ∀ atom ∈ left, atom ∈ right := by
  simp [subset]

/-- `order` computes the denotation order exactly, in all four outcomes. -/
theorem order_spec (left right : EffectSort) :
    (order left right = .equal ↔ Le left right ∧ Le right left) ∧
      (order left right = .less ↔ Le left right ∧ ¬Le right left) ∧
      (order left right = .greater ↔ ¬Le left right ∧ Le right left) ∧
      (order left right = .unordered ↔ ¬Le left right ∧ ¬Le right left) := by
  cases hl : left.isTop <;> cases hr : right.isTop <;> simp only [order, hl, hr, Le]
  · by_cases h₁ : subset left.atoms right.atoms = true <;>
      by_cases h₂ : subset right.atoms left.atoms = true <;>
      simp [h₁, h₂, ← subset_iff]
  all_goals simp

theorem order_eq_equal_iff (left right : EffectSort) : order left right = .equal ↔ Same left right :=
  (order_spec left right).1

theorem order_eq_less_iff (left right : EffectSort) :
    order left right = .less ↔ Le left right ∧ ¬Le right left :=
  (order_spec left right).2.1

theorem order_eq_greater_iff (left right : EffectSort) :
    order left right = .greater ↔ ¬Le left right ∧ Le right left :=
  (order_spec left right).2.2.1

theorem order_eq_unordered_iff (left right : EffectSort) :
    order left right = .unordered ↔ ¬Le left right ∧ ¬Le right left :=
  (order_spec left right).2.2.2

theorem order_self (sort : EffectSort) : order sort sort = .equal :=
  (order_eq_equal_iff _ _).2 (Same.refl _)

/-- Exchanging the arguments of `order` exchanges `less` and `greater`. -/
theorem order_swap_less {left right : EffectSort} (h : order left right = .less) :
    order right left = .greater := by
  rw [order_eq_less_iff] at h
  exact (order_eq_greater_iff _ _).2 ⟨h.2, h.1⟩

theorem order_swap_greater {left right : EffectSort} (h : order left right = .greater) :
    order right left = .less := by
  rw [order_eq_greater_iff] at h
  exact (order_eq_less_iff _ _).2 ⟨h.2, h.1⟩

theorem order_swap_equal {left right : EffectSort} (h : order left right = .equal) :
    order right left = .equal := by
  rw [order_eq_equal_iff] at *
  exact h.symm

theorem order_swap_unordered {left right : EffectSort} (h : order left right = .unordered) :
    order right left = .unordered := by
  rw [order_eq_unordered_iff] at *
  exact ⟨h.2, h.1⟩

/-- Antisymmetry modulo denotation: mutual `less` is impossible. -/
theorem order_antisymm {left right : EffectSort} (h : order left right = .less) :
    order right left ≠ .less := by
  rw [order_swap_less h]
  simp

theorem order_trans_less {a b c : EffectSort} (hab : order a b = .less) (hbc : order b c = .less) :
    order a c = .less := by
  rw [order_eq_less_iff] at *
  exact ⟨hab.1.trans hbc.1, fun hca => hbc.2 (hca.trans hab.1)⟩

/-- Sorts of the same denotation compare alike against everything. -/
theorem order_congr {a a' b b' : EffectSort} (ha : Same a a') (hb : Same b b') :
    order a b = order a' b' := by
  have hle : ∀ {x x' y y' : EffectSort}, Same x x' → Same y y' → (Le x y ↔ Le x' y') :=
    fun hx hy => ⟨fun h => hx.2.trans (h.trans hy.1), fun h => hx.1.trans (h.trans hy.2)⟩
  have h₁ := hle ha hb
  have h₂ := hle hb ha
  cases hab : order a b
  · symm; rw [order_eq_less_iff] at *; simpa [h₁, h₂] using hab
  · symm; rw [order_eq_equal_iff] at *; exact ⟨h₁.1 hab.1, h₂.1 hab.2⟩
  · symm; rw [order_eq_greater_iff] at *; simpa [h₁, h₂] using hab
  · symm; rw [order_eq_unordered_iff] at *; simpa [h₁, h₂] using hab

/-- The empty join is `bot`, as a comparison rather than only as a denotation. -/
theorem order_empty_join_bot : order (join [] []) .bot = .equal :=
  (order_eq_equal_iff _ _).2 join_nil_nil

theorem order_both_comm (left right : EffectSort) : order (both left right) (both right left) = .equal :=
  (order_eq_equal_iff _ _).2 (both_comm _ _)

theorem order_top_absorbs (sort : EffectSort) : order (both .top sort) .top = .equal :=
  (order_eq_equal_iff _ _).2 (both_top_left _)

theorem order_top_right {sort : EffectSort} (h : sort.isTop = false) : order sort .top = .less := by
  simp [order, isTop, h]

theorem order_top_left {sort : EffectSort} (h : sort.isTop = false) : order .top sort = .greater := by
  simp [order, isTop, h]

end EffectLaws

/-! ## Value sorts -/

namespace SortLaws

open Bap.Theory

theorem refine_eq_some_iff (expected actual result : ValueSort) :
    ValueSort.refine expected actual = some result ↔ expected = actual ∧ result = actual := by
  unfold ValueSort.refine
  by_cases h : expected = actual <;> simp [h, eq_comm]

theorem refine_self (sort : ValueSort) : ValueSort.refine sort sort = some sort := by
  simp [ValueSort.refine]

theorem refine_comm (left right : ValueSort) :
    ValueSort.refine left right = ValueSort.refine right left := by
  unfold ValueSort.refine
  by_cases h : left = right
  · subst h; rfl
  · simp [h, Ne.symm h]

theorem refine_assoc (a b c : ValueSort) :
    (ValueSort.refine a b).bind (ValueSort.refine · c) =
      (ValueSort.refine b c).bind (ValueSort.refine a ·) := by
  unfold ValueSort.refine
  by_cases hab : a = b <;> by_cases hbc : b = c <;> simp_all

theorem same_iff (left right : ValueSort) : ValueSort.same left right = true ↔ left = right := by
  simp [ValueSort.same]

theorem same_comm (left right : ValueSort) : ValueSort.same left right = ValueSort.same right left := by
  rw [Bool.eq_iff_iff, same_iff, same_iff]
  exact eq_comm

theorem same_trans {a b c : ValueSort} (h₁ : ValueSort.same a b = true)
    (h₂ : ValueSort.same b c = true) : ValueSort.same a c = true := by
  rw [same_iff] at *
  exact h₁.trans h₂

theorem refine_isSome_iff_same (left right : ValueSort) :
    (ValueSort.refine left right).isSome = ValueSort.same left right := by
  unfold ValueSort.refine
  by_cases h : left = right <;> simp [h, ValueSort.same]

theorem bits_eq_some_iff (sort : ValueSort) (width : Nat) :
    sort.bits = some width ↔ sort = .bitv width := by
  cases sort <;> simp [ValueSort.bits]

theorem app_ne_argument (argument result : ValueSort) : ValueSort.app argument result ≠ argument := by
  intro h
  have := congrArg sizeOf h
  simp at this
  omega

theorem app_ne_result (argument result : ValueSort) : ValueSort.app argument result ≠ result := by
  intro h
  have := congrArg sizeOf h
  simp at this

/-- `base` and `version` are the projections of a variable's version index. -/
theorem var_version_laws (var : Bap.Theory.Var) (first second : Nat) :
    (var.version first).version second = var.version second ∧
      (var.version first).base = var.base ∧ var.version var.index = var ∧ var.base.base = var.base ∧
      (var.version first).isMutable = var.isMutable := by
  cases var with
  | mk name sort index isVirtual isLet =>
    cases isLet <;> simp [Bap.Theory.Var.version, Bap.Theory.Var.base, Bap.Theory.Var.isMutable]

/-- Scoped variables are immutable and have no versions, as upstream's `Let`. -/
theorem let_laws {var : Bap.Theory.Var} (h : var.isLet = true) (index : Nat) :
    var.version index = var ∧ var.isMutable = false := by
  simp [Bap.Theory.Var.version, Bap.Theory.Var.isMutable, h]

/-- Registers and temporaries are mutable, whether or not they are virtual. -/
theorem isMutable_iff (var : Bap.Theory.Var) : var.isMutable = true ↔ var.isLet = false := by
  simp [Bap.Theory.Var.isMutable]

/-- Versions of one variable are equal exactly when their indices are. -/
theorem version_injective (var : Bap.Theory.Var) (h : var.isLet = false) {first second : Nat} :
    var.version first = var.version second ↔ first = second := by
  simp [Bap.Theory.Var.version, h]

/-- Two variables agree when their bases and indices do. -/
theorem var_ext_base {left right : Bap.Theory.Var} (hbase : left.base = right.base)
    (hindex : left.index = right.index) : left = right := by
  cases left
  cases right
  simp_all [Bap.Theory.Var.base]

theorem resort_eq_some_iff (expected : ValueSort) (value result : Bap.Theory.Value) :
    value.resort expected = some result ↔ value.sort = expected ∧ result = value := by
  unfold Bap.Theory.Value.resort
  by_cases h : value.sort = expected <;> simp [h, eq_comm]

theorem resort_sort {expected : ValueSort} {value result : Bap.Theory.Value}
    (h : value.resort expected = some result) : result.sort = expected := by
  obtain ⟨hs, rfl⟩ := (resort_eq_some_iff _ _ _).1 h
  exact hs

theorem resort_resort (first second : ValueSort) (value : Bap.Theory.Value) :
    (value.resort first).bind (·.resort second) =
      if first = second then value.resort first else none := by
  unfold Bap.Theory.Value.resort
  by_cases h₁ : value.sort = first <;> by_cases h₂ : first = second <;> simp_all

theorem resort_none_of_ne {expected : ValueSort} {value : Bap.Theory.Value} (h : value.sort ≠ expected) :
    value.resort expected = none := by
  simp [Bap.Theory.Value.resort, h]

theorem forget_eq_of_resort {expected : ValueSort} {value result : Bap.Theory.Value}
    (h : value.resort expected = some result) : result.forget = value.forget := by
  obtain ⟨_, rfl⟩ := (resort_eq_some_iff _ _ _).1 h
  rfl

end SortLaws

/-! ## IEEE 754 -/

namespace IEEE

open Bap.Theory.IEEE754

local notation "FP" => Bap.Theory.IEEE754.Value

open_private Bap.Theory.IEEE754 Bap.Theory.IEEE754.standardBinary as standardBinary
open_private Bap.Theory.IEEE754 Bap.Theory.IEEE754.round4Log2 as round4Log2
open_private Bap.Theory.IEEE754 Bap.Theory.IEEE754.explicitBinary as explicitBinary
open_private Bap.Theory.IEEE754 Bap.Theory.IEEE754.encodeFields as encodeFields

/-- The parameter shape for which the bit-level codec is a bijection onto its image. -/
structure Standard (parameters : Parameters) : Prop where
  base : parameters.base = 2
  precision : parameters.t + 1 = parameters.p
  width : parameters.k = parameters.w + parameters.t + 1
  exponent : 0 < parameters.w

theorem Standard.check {parameters : Parameters} (h : Standard parameters) :
    standardBinary parameters = true := by
  simp [standardBinary, h.base, h.precision, h.width]

theorem encode_unsupported {parameters : Parameters} (h : standardBinary parameters = false)
    (hx : explicitBinary parameters = false) (value : FP) : encode parameters value = none := by
  simp [encode, h, hx]

theorem decode_unsupported {parameters : Parameters} (h : standardBinary parameters = false)
    (hx : explicitBinary parameters = false) (raw : BitVec parameters.k) :
    decode parameters raw = none := by
  simp [decode, h, hx]

/-- The biased-exponent field of an encoding. -/
def exponentField (parameters : Parameters) (raw : BitVec parameters.k) : Nat :=
  raw.toNat / 2 ^ parameters.t % 2 ^ parameters.w

/-- The fraction field of an encoding. -/
def fractionField (parameters : Parameters) (raw : BitVec parameters.k) : Nat :=
  raw.toNat % 2 ^ parameters.t

/-- The sign bit of an encoding. -/
def signField (parameters : Parameters) (raw : BitVec parameters.k) : Bool :=
  decide (raw.toNat / 2 ^ (parameters.k - 1) % 2 = 1)

/-- The classification performed by `decode`, on already-separated fields. -/
def classify (parameters : Parameters) (sign : Bool) (exponent fraction : Nat) : FP :=
  if exponent = 0 then
    if fraction = 0 then .zero sign else .subnormal sign fraction
  else if exponent = 2 ^ parameters.w - 1 then
    if fraction = 0 then .infinity sign else .nan sign fraction
  else
    .normal sign (Int.ofNat exponent - Int.ofNat parameters.bias) fraction

theorem decode_eq_classify {parameters : Parameters} (h : standardBinary parameters = true)
    (raw : BitVec parameters.k) :
    decode parameters raw =
      some (classify parameters (signField parameters raw) (exponentField parameters raw)
        (fractionField parameters raw)) := by
  simp only [decode, h, ↓reduceIte, classify, signField, exponentField, fractionField]
  repeat' split
  all_goals first | rfl | simp_all

private theorem pack_fields (W T s e f : Nat) (hT : 0 < T) (he : e < W) (hf : f < T) (hs : s < 2) :
    let n := s * (W * T) + e * T + f
    n < 2 * (W * T) ∧ n / (W * T) % 2 = s ∧ n / T % W = e ∧ n % T = f := by
  intro n
  have hW : 0 < W := Nat.lt_of_le_of_lt (Nat.zero_le _) he
  have hdecomp : n = f + T * (s * W + e) := by simp only [n]; grind
  have hmodT : n % T = f := by rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hf]
  have hdivT : n / T = s * W + e := by
    rw [hdecomp, Nat.add_mul_div_left _ _ hT, Nat.div_eq_of_lt hf, Nat.zero_add]
  have hmodW : (s * W + e) % W = e := by
    rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt he]
  have hdivWT : n / (W * T) = s := by
    rw [Nat.mul_comm W T, ← Nat.div_div_eq_div_mul, hdivT, Nat.add_comm, Nat.mul_comm,
      Nat.add_mul_div_left _ _ hW, Nat.div_eq_of_lt he, Nat.zero_add]
  refine ⟨?_, by rw [hdivWT, Nat.mod_eq_of_lt hs], by rw [hdivT, hmodW], hmodT⟩
  have hlt : e * T + f < W * T := by
    have : (e + 1) * T ≤ W * T := Nat.mul_le_mul_right _ he
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have hs' : s * (W * T) ≤ 1 * (W * T) := Nat.mul_le_mul_right _ (by omega)
  simp only [n]
  omega

private theorem top_power {parameters : Parameters} (h : Standard parameters) :
    2 ^ (parameters.k - 1) = 2 ^ parameters.w * 2 ^ parameters.t ∧
      2 ^ parameters.k = 2 * (2 ^ parameters.w * 2 ^ parameters.t) := by
  rw [h.width]
  constructor
  · simp [Nat.pow_add]
  · simp [Nat.pow_add, Nat.pow_succ]; grind

private theorem unpack {parameters : Parameters} (h : Standard parameters) (s e f : Nat)
    (hs : s < 2) (he : e < 2 ^ parameters.w) (hf : f < 2 ^ parameters.t) :
    let raw : BitVec parameters.k := BitVec.ofNat parameters.k (s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f)
    raw.toNat = s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f ∧
      signField parameters raw = decide (s = 1) ∧
      exponentField parameters raw = e ∧ fractionField parameters raw = f := by
  intro raw
  obtain ⟨htop, hall⟩ := top_power h
  obtain ⟨hlt, hsign, hexp, hfrac⟩ :=
    pack_fields (2 ^ parameters.w) (2 ^ parameters.t) s e f (Nat.two_pow_pos _) he hf hs
  have hnat : raw.toNat = s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f := by
    simp only [raw, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    rw [htop, hall]
    exact hlt
  refine ⟨hnat, ?_, ?_, ?_⟩
  · simp only [signField, hnat, htop, hsign]
  · simp only [exponentField, hnat, htop, hexp]
  · simp only [fractionField, hnat, htop, hfrac]

private theorem repack {parameters : Parameters} (h : Standard parameters)
    (raw : BitVec parameters.k) :
    raw = BitVec.ofNat parameters.k
      ((signField parameters raw).toNat * 2 ^ (parameters.k - 1) +
        exponentField parameters raw * 2 ^ parameters.t + fractionField parameters raw) := by
  obtain ⟨htop, hall⟩ := top_power h
  apply BitVec.eq_of_toNat_eq
  have hlt : raw.toNat < 2 * (2 ^ parameters.w * 2 ^ parameters.t) := hall ▸ raw.isLt
  have hsn : (signField parameters raw).toNat = raw.toNat / 2 ^ (parameters.k - 1) % 2 := by
    simp only [signField]
    have := Nat.mod_lt (raw.toNat / 2 ^ (parameters.k - 1)) (by decide : 2 > 0)
    by_cases hb : raw.toNat / 2 ^ (parameters.k - 1) % 2 = 1
    · simp [hb]
    · have h0 : raw.toNat / 2 ^ (parameters.k - 1) % 2 = 0 := by omega
      simp [h0]
  have hT : 0 < 2 ^ parameters.t := Nat.two_pow_pos _
  have hW : 0 < 2 ^ parameters.w := Nat.two_pow_pos _
  have hsum : (signField parameters raw).toNat * 2 ^ (parameters.k - 1) +
      exponentField parameters raw * 2 ^ parameters.t + fractionField parameters raw = raw.toNat := by
    rw [hsn, htop]
    simp only [exponentField, fractionField]
    generalize raw.toNat = n at hlt
    generalize 2 ^ parameters.w = W at *
    generalize 2 ^ parameters.t = T at *
    have h₁ : T * (n / T) + n % T = n := Nat.div_add_mod n T
    have h₂ : W * (n / T / W) + n / T % W = n / T := Nat.div_add_mod (n / T) W
    have h₃ : n / T / W = n / (W * T) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have h₄ : n / (W * T) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      exact hlt
    rw [Nat.mod_eq_of_lt h₄]
    rw [h₃] at h₂
    calc n / (W * T) * (W * T) + n / T % W * T + n % T
        = T * (W * (n / (W * T)) + n / T % W) + n % T := by grind
      _ = n := by rw [h₂, h₁]
  simp only [BitVec.toNat_ofNat]
  rw [hsum]
  exact (Nat.mod_eq_of_lt raw.isLt).symm

private theorem bool_decide_toNat (sign : Bool) : decide (sign.toNat = 1) = sign := by
  cases sign <;> rfl

private theorem one_lt_all_ones {w : Nat} (h : 0 < w) : 2 ^ w - 1 ≠ 0 := by
  have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) h
  omega

/-- The exponent and fraction fields `encode` writes, when the value is representable. -/
def fields (parameters : Parameters) : FP → Option (Nat × Nat)
  | .zero _ => some (0, 0)
  | .subnormal _ fraction =>
    if fraction > 0 && fraction < 2 ^ parameters.t then some (0, fraction) else none
  | .normal _ exponent fraction =>
    let biased := exponent + Int.ofNat parameters.bias
    if biased ≥ 1 && biased < Int.ofNat (2 ^ parameters.w - 1) && fraction < 2 ^ parameters.t then
      some (biased.toNat, fraction)
    else
      none
  | .infinity _ => some (2 ^ parameters.w - 1, 0)
  | .nan _ payload =>
    if payload > 0 && payload < 2 ^ parameters.t then some (2 ^ parameters.w - 1, payload) else none

private theorem encodeFields_standard (parameters : Parameters) (value : FP) :
    encodeFields parameters 0 parameters.t value = fields parameters value := by
  cases value <;> simp [encodeFields, fields]

theorem encode_eq_fields {parameters : Parameters} (h : standardBinary parameters = true) (value : FP) :
    encode parameters value = (fields parameters value).map fun field =>
      BitVec.ofNat parameters.k
        (value.sign.toNat * 2 ^ (parameters.k - 1) + field.1 * 2 ^ parameters.t + field.2) := by
  simp only [encode, h, ↓reduceIte, encodeFields_standard, Option.bind_eq_bind]
  cases fields parameters value <;> rfl

private theorem fields_spec {parameters : Parameters} (h : Standard parameters) {value : FP}
    {e f : Nat} (hf : fields parameters value = some (e, f)) :
    e < 2 ^ parameters.w ∧ f < 2 ^ parameters.t ∧ classify parameters value.sign e f = value := by
  have hW : 0 < 2 ^ parameters.w := Nat.two_pow_pos _
  have hT : 0 < 2 ^ parameters.t := Nat.two_pow_pos _
  have hone := one_lt_all_ones h.exponent
  cases value with
  | zero sign =>
    simp only [fields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨hW, hT, by simp [classify, Value.sign]⟩
  | subnormal sign fraction =>
    simp only [fields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have : fraction ≠ 0 := by omega
      exact ⟨hW, hc.2, by simp [classify, Value.sign, this]⟩
    · cases hf
  | normal sign exponent fraction =>
    simp only [fields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hc
      simp only [Int.ofNat_eq_natCast] at h₁ h₂ ⊢
      have he₀ : (exponent + (parameters.bias : Int)).toNat ≠ 0 := by omega
      have he₁ : (exponent + (parameters.bias : Int)).toNat ≠ 2 ^ parameters.w - 1 := by omega
      refine ⟨by omega, h₃, ?_⟩
      simp only [classify, Value.sign, he₀, he₁, ↓reduceIte, Int.ofNat_eq_natCast]
      congr 1
      omega
    · cases hf
  | infinity sign =>
    simp only [fields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨by omega, hT, by simp [classify, Value.sign, hone]⟩
  | nan sign payload =>
    simp only [fields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have : payload ≠ 0 := by omega
      exact ⟨by omega, hc.2, by simp [classify, Value.sign, this, hone]⟩
    · cases hf

/-- Everything `encode` produces decodes back to the same value. -/
theorem decode_encode {parameters : Parameters} (h : Standard parameters) {value : FP}
    {raw : BitVec parameters.k} (henc : encode parameters value = some raw) :
    decode parameters raw = some value := by
  rw [encode_eq_fields h.check, Option.map_eq_some_iff] at henc
  obtain ⟨⟨e, f⟩, hf, rfl⟩ := henc
  obtain ⟨he, hfr, hcl⟩ := fields_spec h hf
  have hs : value.sign.toNat < 2 := by cases value.sign <;> decide
  obtain ⟨_, hsign, hexp, hfrac⟩ := unpack h value.sign.toNat e f hs he hfr
  rw [decode_eq_classify h.check]
  simp only at hsign hexp hfrac ⊢
  rw [hsign, hexp, hfrac, bool_decide_toNat, hcl]

/-- Everything `decode` produces re-encodes to the original bits, NaN payloads included. -/
theorem encode_decode {parameters : Parameters} (h : Standard parameters)
    {raw : BitVec parameters.k} {value : FP} (hdec : decode parameters raw = some value) :
    encode parameters value = some raw := by
  rw [decode_eq_classify h.check, Option.some.injEq] at hdec
  have hsign : value.sign = signField parameters raw := by
    subst hdec
    simp only [classify]
    repeat' split
    all_goals rfl
  have hE : exponentField parameters raw < 2 ^ parameters.w := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hF : fractionField parameters raw < 2 ^ parameters.t := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hf : fields parameters value =
      some (exponentField parameters raw, fractionField parameters raw) := by
    subst hdec
    generalize exponentField parameters raw = e at *
    generalize fractionField parameters raw = f at *
    generalize signField parameters raw = s
    simp only [classify]
    by_cases he₀ : e = 0
    · by_cases hf₀ : f = 0
      · simp [fields, he₀, hf₀]
      · have : 0 < f := by omega
        simp [fields, he₀, hf₀, this, hF]
    · by_cases he₁ : e = 2 ^ parameters.w - 1
      · by_cases hf₀ : f = 0
        · simp [fields, he₀, ← he₁, hf₀]
        · have : 0 < f := by omega
          simp [fields, he₀, ← he₁, hf₀, this, hF]
      · have h₂ : e < 2 ^ parameters.w - 1 := by omega
        simp [fields, he₀, he₁, hF]
        omega
  rw [encode_eq_fields h.check, hf, hsign]
  exact congrArg some (repack h raw).symm

/-- `encode` and `decode` are mutually inverse relations on standard formats. -/
theorem encode_eq_some_iff {parameters : Parameters} (h : Standard parameters) (value : FP)
    (raw : BitVec parameters.k) :
    encode parameters value = some raw ↔ decode parameters raw = some value :=
  ⟨decode_encode h, encode_decode h⟩

theorem decode_isSome {parameters : Parameters} (h : standardBinary parameters = true)
    (raw : BitVec parameters.k) : (decode parameters raw).isSome = true := by
  rw [decode_eq_classify h]
  rfl

theorem encode_injective {parameters : Parameters} (h : Standard parameters) {left right : FP}
    {raw : BitVec parameters.k} (hl : encode parameters left = some raw)
    (hr : encode parameters right = some raw) : left = right := by
  have := decode_encode h hl
  rw [decode_encode h hr] at this
  exact (Option.some.inj this).symm

theorem decode_injective {parameters : Parameters} (h : Standard parameters) {left right : BitVec parameters.k}
    {value : FP} (hl : decode parameters left = some value)
    (hr : decode parameters right = some value) : left = right := by
  have := encode_decode h hl
  rw [encode_decode h hr] at this
  exact (Option.some.inj this).symm

theorem decodeEncoded_encode {parameters : Parameters} (h : Standard parameters) {value : FP}
    (hsome : (encode parameters value).isSome = true) :
    decodeEncoded parameters (encode parameters value) = some value := by
  obtain ⟨raw, hraw⟩ := Option.isSome_iff_exists.1 hsome
  rw [hraw]
  exact decode_encode h hraw

/-- Representable values: finite fields in range, with nonzero fractions where required. -/
def Representable (parameters : Parameters) : FP → Prop
  | .zero _ | .infinity _ => True
  | .subnormal _ fraction | .nan _ fraction => 0 < fraction ∧ fraction < 2 ^ parameters.t
  | .normal _ exponent fraction =>
    1 ≤ exponent + parameters.bias ∧ exponent + parameters.bias < ((2 ^ parameters.w - 1 : Nat) : Int) ∧
      fraction < 2 ^ parameters.t

theorem encode_isSome_iff {parameters : Parameters} (h : standardBinary parameters = true) (value : FP) :
    (encode parameters value).isSome = true ↔ Representable parameters value := by
  rw [encode_eq_fields h, Option.isSome_map]
  cases value <;> simp only [fields, Representable, Option.isSome_some] <;>
    (split <;> simp_all <;> try omega) <;> grind

/-! ### Classification on raw bits -/

section Classification

variable {parameters : Parameters} {raw : BitVec parameters.k} {value : FP}

private theorem classify_of_decode (h : Standard parameters) (hd : decode parameters raw = some value) :
    value = classify parameters (signField parameters raw) (exponentField parameters raw)
      (fractionField parameters raw) := by
  rw [decode_eq_classify h.check] at hd
  exact (Option.some.inj hd).symm

theorem isZero_iff (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.isZero = true ↔ exponentField parameters raw = 0 ∧ fractionField parameters raw = 0 := by
  rw [classify_of_decode h hd]
  simp only [classify]
  repeat' split
  all_goals simp_all [Value.isZero]

theorem isSubnormal_iff (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.isSubnormal = true ↔ exponentField parameters raw = 0 ∧ fractionField parameters raw ≠ 0 := by
  rw [classify_of_decode h hd]
  simp only [classify]
  repeat' split
  all_goals simp_all [Value.isSubnormal]

theorem isInf_iff (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.isInf = true ↔
      exponentField parameters raw = 2 ^ parameters.w - 1 ∧ fractionField parameters raw = 0 := by
  have hone := Ne.symm (one_lt_all_ones h.exponent)
  rw [classify_of_decode h hd]
  simp only [classify]
  repeat' split
  all_goals simp_all [Value.isInf]

theorem isNan_iff (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.isNan = true ↔
      exponentField parameters raw = 2 ^ parameters.w - 1 ∧ fractionField parameters raw ≠ 0 := by
  have hone := Ne.symm (one_lt_all_ones h.exponent)
  rw [classify_of_decode h hd]
  simp only [classify]
  repeat' split
  all_goals simp_all [Value.isNan]

theorem isNormal_iff (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.isNormal = true ↔
      exponentField parameters raw ≠ 0 ∧ exponentField parameters raw ≠ 2 ^ parameters.w - 1 := by
  have hone := Ne.symm (one_lt_all_ones h.exponent)
  rw [classify_of_decode h hd]
  simp only [classify]
  repeat' split
  all_goals simp_all [Value.isNormal]

theorem sign_decode (h : Standard parameters) (hd : decode parameters raw = some value) :
    value.sign = raw.msb := by
  rw [classify_of_decode h hd]
  have hsign : signField parameters raw = raw.msb := by
    have hk : 0 < parameters.k := by have := h.width; omega
    rw [BitVec.msb_eq_decide, signField]
    obtain ⟨htop, hall⟩ := top_power h
    have hlt : raw.toNat / 2 ^ (parameters.k - 1) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [htop, Nat.mul_comm, ← hall]
      exact raw.isLt
    rw [Nat.mod_eq_of_lt hlt]
    have hdiv : (2 ^ (parameters.k - 1) ≤ raw.toNat) ↔ raw.toNat / 2 ^ (parameters.k - 1) = 1 := by
      constructor
      · intro hle
        have := Nat.div_pos hle (Nat.two_pow_pos (parameters.k - 1))
        omega
      · intro heq
        have := Nat.div_add_mod raw.toNat (2 ^ (parameters.k - 1))
        rw [heq] at this
        omega
    simp only [hdiv]
  rw [← hsign]
  simp only [classify]
  repeat' split
  all_goals rfl

end Classification

theorem classes_exclusive (value : FP) :
    [value.isZero, value.isSubnormal, value.isNormal, value.isInf, value.isNan].count true = 1 := by
  cases value <;> rfl

theorem isFinite_iff (value : FP) :
    value.isFinite = true ↔ value.isZero = true ∨ value.isSubnormal = true ∨ value.isNormal = true := by
  cases value <;> simp [Value.isFinite, Value.isZero, Value.isSubnormal, Value.isNormal, Value.isInf,
    Value.isNan]

/-! ### Sign negation -/

/-- Sign flip on decoded values, acting on every class including NaN. -/
def negate : FP → FP
  | .zero sign => .zero !sign
  | .subnormal sign fraction => .subnormal (!sign) fraction
  | .normal sign exponent fraction => .normal (!sign) exponent fraction
  | .infinity sign => .infinity !sign
  | .nan sign payload => .nan (!sign) payload

theorem negate_negate (value : FP) : negate (negate value) = value := by
  cases value <;> simp [negate]

theorem sign_negate (value : FP) : (negate value).sign = !value.sign := by
  cases value <;> rfl

theorem negate_ne (value : FP) : negate value ≠ value := by
  intro h
  have := congrArg Value.sign h
  rw [sign_negate] at this
  cases hs : value.sign <;> simp [hs] at this

theorem classes_negate (value : FP) :
    (negate value).isZero = value.isZero ∧ (negate value).isSubnormal = value.isSubnormal ∧
      (negate value).isNormal = value.isNormal ∧ (negate value).isInf = value.isInf ∧
      (negate value).isNan = value.isNan := by
  cases value <;> simp [negate, Value.isZero, Value.isSubnormal, Value.isNormal, Value.isInf, Value.isNan]

theorem fields_negate (parameters : Parameters) (value : FP) :
    fields parameters (negate value) = fields parameters value := by
  cases value <;> rfl

private theorem xor_two_pow_top (x m : Nat) (hx : x < 2 ^ (m + 1)) :
    x ^^^ 2 ^ m = (x + 2 ^ m) % 2 ^ (m + 1) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor, Nat.testBit_two_pow, Nat.testBit_mod_two_pow, Nat.add_comm x]
  by_cases hj : j = m
  · subst hj
    simp [Nat.testBit_two_pow_add_eq]
  by_cases hlt : j < m
  · have hne : m ≠ j := by omega
    simp [hne, show j < m + 1 by omega, Nat.testBit_two_pow_add_gt hlt]
  · have hne : m ≠ j := by omega
    have hge : ¬ j < m + 1 := by omega
    have hsmall : x.testBit j = false := by
      apply Nat.testBit_lt_two_pow
      exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))
    simp [hne, hge, hsmall]

/-- The mask holding only the sign bit. -/
def signMask (parameters : Parameters) : BitVec parameters.k :=
  BitVec.ofNat parameters.k (2 ^ (parameters.k - 1))

/-- Negation at the value level is exactly a flip of the top bit of the encoding. -/
theorem encode_negate {parameters : Parameters} (h : Standard parameters) (value : FP) :
    encode parameters (negate value) = (encode parameters value).map (· ^^^ signMask parameters) := by
  obtain ⟨htop, hall⟩ := top_power h
  have hk : parameters.k = (parameters.k - 1) + 1 := by have := h.width; omega
  rw [encode_eq_fields h.check, encode_eq_fields h.check, fields_negate, Option.map_map]
  cases hf : fields parameters value with
  | none => rfl
  | some field =>
    obtain ⟨e, f⟩ := field
    obtain ⟨he, hfr, -⟩ := fields_spec h hf
    simp only [Option.map_some, Function.comp, Option.some.injEq]
    apply BitVec.eq_of_toNat_eq
    have hs₀ : e * 2 ^ parameters.t + f < 2 ^ (parameters.k - 1) := by
      rw [htop]
      have hmul : (e + 1) * 2 ^ parameters.t ≤ 2 ^ parameters.w * 2 ^ parameters.t :=
        Nat.mul_le_mul_right _ he
      rw [Nat.add_mul, Nat.one_mul] at hmul
      omega
    have hpow : 2 ^ parameters.k = 2 * 2 ^ (parameters.k - 1) := by
      conv => lhs; rw [hk]
      rw [Nat.pow_succ, Nat.mul_comm]
    simp only [BitVec.toNat_ofNat, BitVec.toNat_xor, signMask]
    generalize hbody : e * 2 ^ parameters.t + f = body at hs₀
    have hassoc (s : Nat) : s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f =
        s * 2 ^ (parameters.k - 1) + body := by omega
    rw [hassoc, hassoc]
    generalize hP : 2 ^ (parameters.k - 1) = P at *
    have hmask : P % 2 ^ parameters.k = P := Nat.mod_eq_of_lt (by omega)
    rw [hmask]
    have hsign : value.sign = true ∨ value.sign = false := by cases value.sign <;> simp
    rw [sign_negate]
    rcases hsign with hs | hs <;> rw [hs] <;> simp only [Bool.not_true, Bool.not_false, Bool.toNat_true,
      Bool.toNat_false, Nat.zero_mul, Nat.one_mul, Nat.zero_add]
    · have h₁ : (P + body) % 2 ^ parameters.k = P + body := Nat.mod_eq_of_lt (by omega)
      have h₂ : body % 2 ^ parameters.k = body := Nat.mod_eq_of_lt (by omega)
      rw [h₁, h₂]
      have hx : P + body < 2 ^ (parameters.k - 1 + 1) := by rw [← hk]; omega
      rw [← hP, xor_two_pow_top _ _ (by rw [hP]; exact hx), hP, ← hk]
      have heq : P + body + P = body + 2 ^ parameters.k := by omega
      rw [heq, Nat.add_mod_right]
      exact h₂.symm
    · have h₂ : body % 2 ^ parameters.k = body := Nat.mod_eq_of_lt (by omega)
      have h₁ : (P + body) % 2 ^ parameters.k = P + body := Nat.mod_eq_of_lt (by omega)
      rw [h₁, h₂]
      have hx : body < 2 ^ (parameters.k - 1 + 1) := by rw [← hk]; omega
      rw [← hP, xor_two_pow_top _ _ hx, hP, ← hk]
      rw [Nat.add_comm body P]
      exact (Nat.mod_eq_of_lt (by omega)).symm

/-- Flipping the top bit of an encoding twice restores it; decoded, this is `negate`. -/
theorem decode_xor_signMask {parameters : Parameters} (h : Standard parameters) (raw : BitVec parameters.k) :
    decode parameters (raw ^^^ signMask parameters) = (decode parameters raw).map negate := by
  obtain ⟨value, hvalue⟩ := Option.isSome_iff_exists.1 (decode_isSome h.check raw)
  rw [hvalue, Option.map_some, ← encode_eq_some_iff h]
  rw [encode_negate h, encode_decode h hvalue]
  rfl

/-! ### Formats -/

private theorem pow4_bound (k : Nat) (hk : 64 ≤ k) : k ^ 4 < 2 ^ k := by
  induction hk with
  | refl => decide
  | @step n hn ih =>
    replace hn : 64 ≤ n := hn
    show (n + 1) ^ 4 < 2 ^ (n + 1)
    rw [Nat.pow_succ 2 n]
    have : (n + 1) ^ 4 ≤ 2 * n ^ 4 := by
      have h₁ : (n + 1) ^ 4 = n ^ 4 + 4 * n ^ 3 + 6 * n ^ 2 + 4 * n + 1 := by grind
      have h₄ : n ^ 4 = n * n ^ 3 := by grind
      have h₃ : n ^ 3 = n * n ^ 2 := by grind
      have h₂ : n ^ 2 = n * n := by grind
      have a₃ : 64 * n ^ 3 ≤ n * n ^ 3 := Nat.mul_le_mul_right _ hn
      have a₂ : 64 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right _ hn
      have a₁ : 64 * n ≤ n * n := Nat.mul_le_mul_right _ hn
      omega
    omega

private theorem log2_pow4_bounds (k : Nat) (hk : 64 ≤ k) :
    24 ≤ Nat.log2 (k ^ 4) ∧ Nat.log2 (k ^ 4) < k := by
  have hpos : k ^ 4 ≠ 0 := by
    have := Nat.pow_pos (n := 4) (show 0 < k by omega)
    omega
  constructor
  · apply (Nat.le_log2 hpos).2
    calc 2 ^ 24 ≤ 64 ^ 4 := by decide
      _ ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
  · exact (Nat.log2_lt hpos).2 (pow4_bound k hk)

theorem binary_standard {k : Nat} (hk : 64 ≤ k) : Standard (binary k) := by
  obtain ⟨hlo, hhi⟩ := log2_pow4_bounds k hk
  simp only [binary]
  generalize hr : round4Log2 k = rounded
  have hrounded : 24 ≤ rounded ∧ rounded ≤ k := by
    rw [← hr, round4Log2]
    split <;> omega
  exact ⟨rfl, by simp only; omega, by simp only; omega, by simp only; omega⟩

/-- Every parameter set offered by `binaryFormat`, other than x87 `binary80`, drives the codec. -/
theorem binaryFormat_standard {k : Nat} {parameters : Parameters} (hne : k ≠ 80)
    (h : binaryFormat k = some parameters) : Standard parameters ∧ parameters.k = k := by
  by_cases h16 : k = 16
  · subst h16
    cases h
    exact ⟨⟨rfl, rfl, rfl, by decide⟩, rfl⟩
  by_cases h32 : k = 32
  · subst h32
    cases h
    exact ⟨⟨rfl, rfl, rfl, by decide⟩, rfl⟩
  simp only [binaryFormat, h16, h32, hne, ↓reduceIte] at h
  split at h
  · rename_i hmul
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hmul
    exact ⟨binary_standard (by omega), rfl⟩
  · cases h

theorem binaryFormat_isSome_iff (k : Nat) :
    (binaryFormat k).isSome = true ↔ k = 16 ∨ k = 80 ∨ (0 < k ∧ k % 32 = 0) := by
  unfold binaryFormat
  repeat' split
  all_goals simp_all

theorem decimalFormat_isSome_iff (k : Nat) :
    (decimalFormat k).isSome = true ↔ 0 < k ∧ k % 32 = 0 := by
  unfold decimalFormat
  split <;> simp_all

/-- Decimal interchange formats partition their width into sign, combination and trailing fields. -/
theorem decimalFormat_width {k : Nat} {parameters : Parameters} (h : decimalFormat k = some parameters) :
    parameters.k = k ∧ parameters.base = 10 ∧ parameters.w + parameters.t + 1 = k := by
  unfold decimalFormat at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    refine ⟨rfl, rfl, ?_⟩
    show k / 16 + 9 + (15 * k / 16 - 10) + 1 = k
    omega
  · cases h

/-- The bit-level codec is binary-only: decimal formats never encode or decode. -/
theorem decimal_codec_none (k : Nat) (value : FP) : encode (decimal k) value = none := by
  apply encode_unsupported <;> simp [standardBinary, explicitBinary, decimal]

/-! ### Explicit integer bit -/

/-- The parameter shape of x87 extended precision: the significand field holds the integer bit. -/
structure Explicit (parameters : Parameters) : Prop where
  base : parameters.base = 2
  precision : parameters.t = parameters.p
  positive : 0 < parameters.t
  width : parameters.k = parameters.w + parameters.t + 1
  exponent : 0 < parameters.w

theorem binary80_explicit : Explicit binary80 := ⟨rfl, rfl, by decide, rfl, by decide⟩

theorem Explicit.check {parameters : Parameters} (h : Explicit parameters) :
    explicitBinary parameters = true := by
  simp only [explicitBinary, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨h.base, h.precision⟩, h.positive⟩, h.width⟩

theorem Explicit.not_standard {parameters : Parameters} (h : Explicit parameters) :
    standardBinary parameters = false := by
  have hp := h.precision
  simp [standardBinary]
  omega

/-- A canonical explicit-integer encoding: the integer bit says what the exponent implies. These are
the only encodings x87 itself produces. -/
def Canonical (parameters : Parameters) (raw : BitVec parameters.k) : Prop :=
  if exponentField parameters raw = 0 then
    fractionField parameters raw < 2 ^ (parameters.t - 1)
  else
    2 ^ (parameters.t - 1) ≤ fractionField parameters raw

/-- `decode` on explicit-integer formats, on already-separated fields. -/
def classifyExplicit (parameters : Parameters) (sign : Bool) (exponent fraction : Nat) : FP :=
  let low := fraction % 2 ^ (parameters.t - 1)
  if exponent = 0 then
    if fraction = 0 then .zero sign else .subnormal sign fraction
  else if exponent = 2 ^ parameters.w - 1 then
    if low = 0 then .infinity sign else .nan sign low
  else if fraction < 2 ^ (parameters.t - 1) then
    .nan sign low
  else
    .normal sign (Int.ofNat exponent - Int.ofNat parameters.bias) low

theorem decode_explicit {parameters : Parameters} (h : Explicit parameters) (raw : BitVec parameters.k) :
    decode parameters raw =
      some (classifyExplicit parameters (signField parameters raw) (exponentField parameters raw)
        (fractionField parameters raw)) := by
  simp only [decode, h.not_standard, h.check, Bool.false_eq_true, ↓reduceIte, classifyExplicit, signField,
    exponentField, fractionField]
  by_cases hlt : raw.toNat % 2 ^ parameters.t < 2 ^ (parameters.t - 1) <;> simp only [hlt, ↓reduceIte]
  all_goals
    repeat' split
    all_goals first | rfl | simp_all

/-- Decoding is total on explicit-integer formats, non-canonical encodings included. -/
theorem decode_explicit_isSome {parameters : Parameters} (h : Explicit parameters)
    (raw : BitVec parameters.k) : (decode parameters raw).isSome = true := by
  rw [decode_explicit h]
  rfl

private theorem top_power_explicit {parameters : Parameters} (h : Explicit parameters) :
    2 ^ (parameters.k - 1) = 2 ^ parameters.w * 2 ^ parameters.t ∧
      2 ^ parameters.k = 2 * (2 ^ parameters.w * 2 ^ parameters.t) := by
  rw [h.width]
  constructor
  · simp [Nat.pow_add]
  · simp [Nat.pow_add, Nat.pow_succ]; grind

private theorem unpack_explicit {parameters : Parameters} (h : Explicit parameters) (s e f : Nat)
    (hs : s < 2) (he : e < 2 ^ parameters.w) (hf : f < 2 ^ parameters.t) :
    let raw : BitVec parameters.k :=
      BitVec.ofNat parameters.k (s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f)
    signField parameters raw = decide (s = 1) ∧
      exponentField parameters raw = e ∧ fractionField parameters raw = f := by
  intro raw
  obtain ⟨htop, hall⟩ := top_power_explicit h
  obtain ⟨hlt, hsign, hexp, hfrac⟩ :=
    pack_fields (2 ^ parameters.w) (2 ^ parameters.t) s e f (Nat.two_pow_pos _) he hf hs
  have hnat : raw.toNat = s * 2 ^ (parameters.k - 1) + e * 2 ^ parameters.t + f := by
    simp only [raw, BitVec.toNat_ofNat]
    apply Nat.mod_eq_of_lt
    rw [htop, hall]
    exact hlt
  refine ⟨?_, ?_, ?_⟩
  · simp only [signField, hnat, htop, hsign]
  · simp only [exponentField, hnat, htop, hexp]
  · simp only [fractionField, hnat, htop, hfrac]

private theorem repack_explicit {parameters : Parameters} (h : Explicit parameters)
    (raw : BitVec parameters.k) :
    raw = BitVec.ofNat parameters.k
      ((signField parameters raw).toNat * 2 ^ (parameters.k - 1) +
        exponentField parameters raw * 2 ^ parameters.t + fractionField parameters raw) := by
  obtain ⟨htop, hall⟩ := top_power_explicit h
  apply BitVec.eq_of_toNat_eq
  have hlt : raw.toNat < 2 * (2 ^ parameters.w * 2 ^ parameters.t) := hall ▸ raw.isLt
  have hsn : (signField parameters raw).toNat = raw.toNat / 2 ^ (parameters.k - 1) % 2 := by
    simp only [signField]
    have := Nat.mod_lt (raw.toNat / 2 ^ (parameters.k - 1)) (by decide : 2 > 0)
    by_cases hb : raw.toNat / 2 ^ (parameters.k - 1) % 2 = 1
    · simp [hb]
    · have h0 : raw.toNat / 2 ^ (parameters.k - 1) % 2 = 0 := by omega
      simp [h0]
  have hsum : (signField parameters raw).toNat * 2 ^ (parameters.k - 1) +
      exponentField parameters raw * 2 ^ parameters.t + fractionField parameters raw = raw.toNat := by
    rw [hsn, htop]
    simp only [exponentField, fractionField]
    generalize raw.toNat = n at hlt
    generalize 2 ^ parameters.w = W at *
    generalize 2 ^ parameters.t = T at *
    have h₁ : T * (n / T) + n % T = n := Nat.div_add_mod n T
    have h₂ : W * (n / T / W) + n / T % W = n / T := Nat.div_add_mod (n / T) W
    have h₃ : n / T / W = n / (W * T) := by
      rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
    have h₄ : n / (W * T) < 2 := by
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      exact hlt
    rw [Nat.mod_eq_of_lt h₄]
    rw [h₃] at h₂
    calc n / (W * T) * (W * T) + n / T % W * T + n % T
        = T * (W * (n / (W * T)) + n / T % W) + n % T := by grind
      _ = n := by rw [h₂, h₁]
  simp only [BitVec.toNat_ofNat]
  rw [hsum]
  exact (Nat.mod_eq_of_lt raw.isLt).symm

private theorem encode_explicit {parameters : Parameters} (h : Explicit parameters) (value : FP) :
    encode parameters value =
      (encodeFields parameters (2 ^ (parameters.t - 1)) (parameters.t - 1) value).map fun field =>
        BitVec.ofNat parameters.k
          (value.sign.toNat * 2 ^ (parameters.k - 1) + field.1 * 2 ^ parameters.t + field.2) := by
  simp only [encode, h.not_standard, h.check, Bool.false_eq_true, ↓reduceIte, Option.bind_eq_bind]
  cases encodeFields parameters (2 ^ (parameters.t - 1)) (parameters.t - 1) value <;> rfl

private theorem half_power {parameters : Parameters} (h : Explicit parameters) :
    2 ^ parameters.t = 2 * 2 ^ (parameters.t - 1) := by
  have hpos := h.positive
  conv => lhs; rw [show parameters.t = (parameters.t - 1) + 1 by omega]
  rw [Nat.pow_succ, Nat.mul_comm]

private theorem encodeFields_explicit_spec {parameters : Parameters} (h : Explicit parameters) {value : FP}
    {e f : Nat} (hf : encodeFields parameters (2 ^ (parameters.t - 1)) (parameters.t - 1) value = some (e, f)) :
    e < 2 ^ parameters.w ∧ f < 2 ^ parameters.t ∧ classifyExplicit parameters value.sign e f = value := by
  have hW : 0 < 2 ^ parameters.w := Nat.two_pow_pos _
  have hone := one_lt_all_ones h.exponent
  have hhalf := half_power h
  have hH : 0 < 2 ^ (parameters.t - 1) := Nat.two_pow_pos _
  generalize hH' : 2 ^ (parameters.t - 1) = H at *
  have hmod : ∀ x, x < H → (H + x) % H = x := by
    intro x hx
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hx]
  cases value with
  | zero sign =>
    simp only [encodeFields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    exact ⟨hW, by omega, by simp [classifyExplicit, Value.sign]⟩
  | subnormal sign fraction =>
    simp only [encodeFields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      have : fraction ≠ 0 := by omega
      exact ⟨hW, by omega, by simp [classifyExplicit, Value.sign, this]⟩
    · cases hf
  | normal sign exponent fraction =>
    simp only [encodeFields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq, hH'] at hc
      obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hc
      simp only [Int.ofNat_eq_natCast] at h₁ h₂ ⊢
      have he₀ : (exponent + (parameters.bias : Int)).toNat ≠ 0 := by omega
      have he₁ : (exponent + (parameters.bias : Int)).toNat ≠ 2 ^ parameters.w - 1 := by omega
      have hge : ¬ H + fraction < H := by omega
      refine ⟨by omega, by omega, ?_⟩
      simp only [classifyExplicit, Value.sign, he₀, he₁, ↓reduceIte, hH', hge, hmod _ h₃]
      congr 1
      simp only [Int.ofNat_eq_natCast]
      omega
    · cases hf
  | infinity sign =>
    simp only [encodeFields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    refine ⟨by omega, by omega, ?_⟩
    simp [classifyExplicit, Value.sign, hone, hH']
  | nan sign payload =>
    simp only [encodeFields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq, hH'] at hc
      have hp : payload ≠ 0 := by omega
      refine ⟨by omega, by omega, ?_⟩
      simp [classifyExplicit, Value.sign, hone, hH', hmod _ hc.2, hp]
    · cases hf

/-- Everything an explicit-integer format encodes decodes back to the same value. -/
theorem decode_encode_explicit {parameters : Parameters} (h : Explicit parameters) {value : FP}
    {raw : BitVec parameters.k} (henc : encode parameters value = some raw) :
    decode parameters raw = some value := by
  rw [encode_explicit h, Option.map_eq_some_iff] at henc
  obtain ⟨⟨e, f⟩, hf, rfl⟩ := henc
  obtain ⟨he, hfr, hcl⟩ := encodeFields_explicit_spec h hf
  have hs : value.sign.toNat < 2 := by cases value.sign <;> decide
  obtain ⟨hsign, hexp, hfrac⟩ := unpack_explicit h value.sign.toNat e f hs he hfr
  rw [decode_explicit h]
  simp only at hsign hexp hfrac ⊢
  rw [hsign, hexp, hfrac, bool_decide_toNat, hcl]

/-- What `encode` writes is canonical. -/
theorem encode_explicit_canonical {parameters : Parameters} (h : Explicit parameters) {value : FP}
    {raw : BitVec parameters.k} (henc : encode parameters value = some raw) : Canonical parameters raw := by
  rw [encode_explicit h, Option.map_eq_some_iff] at henc
  obtain ⟨⟨e, f⟩, hf, rfl⟩ := henc
  obtain ⟨he, hfr, _⟩ := encodeFields_explicit_spec h hf
  have hs : value.sign.toNat < 2 := by cases value.sign <;> decide
  obtain ⟨_, hexp, hfrac⟩ := unpack_explicit h value.sign.toNat e f hs he hfr
  simp only [Canonical, hexp, hfrac]
  have hone := one_lt_all_ones h.exponent
  cases value with
  | zero sign =>
    simp only [encodeFields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simpa using Nat.two_pow_pos _
  | subnormal sign fraction =>
    simp only [encodeFields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      simpa using hc.2
    · cases hf
  | normal sign exponent fraction =>
    simp only [encodeFields] at hf
    split at hf
    · rename_i hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [Bool.and_eq_true, decide_eq_true_eq, Int.ofNat_eq_natCast] at hc
      have he₀ : (exponent + (parameters.bias : Int)).toNat ≠ 0 := by omega
      simp only [Int.ofNat_eq_natCast, he₀, ↓reduceIte]
      omega
    · cases hf
  | infinity sign =>
    simp only [encodeFields, Option.some.injEq, Prod.mk.injEq] at hf
    obtain ⟨rfl, rfl⟩ := hf
    simp [hone]
  | nan sign payload =>
    simp only [encodeFields] at hf
    split at hf
    · simp only [Option.some.injEq, Prod.mk.injEq] at hf
      obtain ⟨rfl, rfl⟩ := hf
      simp only [hone, ↓reduceIte]
      omega
    · cases hf

private theorem encodeFields_classifyExplicit {parameters : Parameters} (h : Explicit parameters) (sign : Bool)
    {e f : Nat} (he : e < 2 ^ parameters.w) (hf : f < 2 ^ parameters.t)
    (hcan : if e = 0 then f < 2 ^ (parameters.t - 1) else 2 ^ (parameters.t - 1) ≤ f) :
    encodeFields parameters (2 ^ (parameters.t - 1)) (parameters.t - 1)
      (classifyExplicit parameters sign e f) = some (e, f) := by
  have hhalf := half_power h
  have hH : 0 < 2 ^ (parameters.t - 1) := Nat.two_pow_pos _
  simp only [classifyExplicit]
  by_cases he₀ : e = 0
  · subst he₀
    simp only [↓reduceIte] at hcan ⊢
    by_cases hf₀ : f = 0
    · simp [hf₀, encodeFields]
    · have hpos : 0 < f := by omega
      simp [hf₀, encodeFields, hpos, hcan]
  simp only [he₀, ↓reduceIte] at hcan ⊢
  generalize hH' : 2 ^ (parameters.t - 1) = H at *
  have hlow : H + f % H = f := by
    rw [Nat.mod_eq_sub_mod hcan, Nat.mod_eq_of_lt (by omega)]
    omega
  have hlt : f % H < H := Nat.mod_lt _ hH
  by_cases he₁ : e = 2 ^ parameters.w - 1
  · simp only [he₁, ↓reduceIte]
    by_cases hl : f % H = 0
    · have : f = H := by omega
      simp [encodeFields, this]
    · have hpos : 0 < f % H := by omega
      simp [hl, encodeFields, hH', hpos, hlt, hlow]
  · have hge : ¬ f < H := by omega
    have h₂ : e < 2 ^ parameters.w - 1 := by omega
    simp only [he₁, ↓reduceIte, hge, encodeFields, hH', hlt]
    have h₁ : (1 : Int) ≤ e := by omega
    simp [hlow, h₁, Int.ofNat_eq_natCast]
    omega

/-- Round trip on bits, exactly for the canonical encodings: non-canonical ones have a meaning but
are never written back. -/
theorem encode_decode_explicit_iff {parameters : Parameters} (h : Explicit parameters)
    (raw : BitVec parameters.k) :
    (decode parameters raw).bind (encode parameters) = some raw ↔ Canonical parameters raw := by
  constructor
  · intro hrt
    obtain ⟨value, _, henc⟩ := Option.bind_eq_some_iff.1 hrt
    exact encode_explicit_canonical h henc
  · intro hcan
    have hfields := encodeFields_classifyExplicit h (signField parameters raw)
      (e := exponentField parameters raw) (f := fractionField parameters raw)
      (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.mod_lt _ (Nat.two_pow_pos _)) hcan
    rw [decode_explicit h, Option.bind_some, encode_explicit h, hfields]
    have hsign : ∀ e f, (classifyExplicit parameters (signField parameters raw) e f).sign =
        signField parameters raw := by
      intro e f
      simp only [classifyExplicit]
      repeat' split
      all_goals rfl
    simp only [Option.map_some, hsign]
    exact congrArg some (repack_explicit h raw).symm

/-- Sign negation is the same top-bit flip as in the standard formats. -/
theorem decode_explicit_sign {parameters : Parameters} (h : Explicit parameters) (raw : BitVec parameters.k)
    {value : FP} (hd : decode parameters raw = some value) : value.sign = signField parameters raw := by
  rw [decode_explicit h, Option.some.injEq] at hd
  subst hd
  simp only [classifyExplicit]
  repeat' split
  all_goals rfl

theorem encode_explicit_injective {parameters : Parameters} (h : Explicit parameters) {left right : FP}
    {raw : BitVec parameters.k} (hl : encode parameters left = some raw)
    (hr : encode parameters right = some raw) : left = right := by
  have := decode_encode_explicit h hl
  rw [decode_encode_explicit h hr] at this
  exact (Option.some.inj this).symm

/-- Every format `binaryFormat` offers now drives the bit codec. -/
theorem binaryFormat_codec {k : Nat} {parameters : Parameters} (h : binaryFormat k = some parameters) :
    parameters.k = k ∧ (Standard parameters ∨ (k = 80 ∧ Explicit parameters)) := by
  by_cases h80 : k = 80
  · subst h80
    cases h
    exact ⟨rfl, Or.inr ⟨rfl, binary80_explicit⟩⟩
  · obtain ⟨hs, hk⟩ := binaryFormat_standard h80 h
    exact ⟨hk, Or.inl hs⟩

/-! ### Rounding -/

section Rounding

variable {mode : RMode} {numerator : Int} {denominator : Nat}

theorem roundRatio_zero (mode : RMode) (numerator : Int) : roundRatio mode numerator 0 = none := by
  simp [roundRatio]

private theorem floor_spec (numerator : Int) {denominator : Nat} (hd : 0 < denominator) :
    let q := numerator.fdiv denominator
    let r := numerator - q * denominator
    0 ≤ r ∧ r < denominator ∧ numerator = q * denominator + r := by
  intro q r
  have hdI : (0 : Int) < denominator := by omega
  have hq : q = numerator / denominator := Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hmod : r = numerator % denominator := by
    have := Int.mul_ediv_add_emod numerator denominator
    simp only [r, hq]
    grind
  refine ⟨?_, ?_, by simp only [r]; omega⟩
  · rw [hmod]; exact Int.emod_nonneg _ (by omega)
  · rw [hmod]; exact Int.emod_lt_of_pos _ hdI

private theorem roundRatio_eq (mode : RMode) (numerator : Int) {denominator : Nat} (hd : 0 < denominator) :
    let floor := numerator.fdiv denominator
    let remainder := numerator - floor * denominator
    roundRatio mode numerator denominator = some
      (match mode with
        | .rtz => Int.tdiv numerator denominator
        | .rtn => floor
        | .rtp => if remainder > 0 then floor + 1 else floor
        | .rne | .rna =>
          if 2 * remainder < denominator then
            floor
          else if 2 * remainder > denominator then
            floor + 1
          else
            match mode with
            | .rne => if floor % 2 = 0 then floor else floor + 1
            | _ => if numerator < 0 then floor else floor + 1) := by
  intro floor remainder
  have hne : denominator ≠ 0 := by omega
  simp only [roundRatio, hne, ↓reduceIte]
  rfl

theorem roundRatio_isSome (mode : RMode) (numerator : Int) (hd : 0 < denominator) :
    (roundRatio mode numerator denominator).isSome = true := by
  rw [roundRatio_eq mode numerator hd]
  rfl

/-- `rtn` computes the floor of the ratio. -/
theorem roundRatio_rtn (hd : 0 < denominator) {result : Int}
    (h : roundRatio .rtn numerator denominator = some result) :
    result * denominator ≤ numerator ∧ numerator < (result + 1) * denominator := by
  rw [roundRatio_eq _ _ hd] at h
  obtain ⟨h₀, h₁, h₂⟩ := floor_spec numerator hd
  simp only [Option.some.injEq] at h
  subst h
  rw [Int.add_mul, Int.one_mul]
  omega

/-- `rtp` computes the ceiling of the ratio. -/
theorem roundRatio_rtp (hd : 0 < denominator) {result : Int}
    (h : roundRatio .rtp numerator denominator = some result) :
    (result - 1) * denominator < numerator ∧ numerator ≤ result * denominator := by
  rw [roundRatio_eq _ _ hd] at h
  obtain ⟨h₀, h₁, h₂⟩ := floor_spec numerator hd
  simp only [Option.some.injEq] at h
  subst h
  split
  · rw [Int.add_sub_cancel, Int.add_mul, Int.one_mul]
    omega
  · rw [Int.sub_mul, Int.one_mul]
    omega

/-- Round-to-nearest modes land within half a unit of the exact ratio. -/
theorem roundRatio_nearest (hmode : mode = .rne ∨ mode = .rna) (hd : 0 < denominator) {result : Int}
    (h : roundRatio mode numerator denominator = some result) :
    -(denominator : Int) ≤ 2 * (numerator - result * denominator) ∧
      2 * (numerator - result * denominator) ≤ denominator := by
  rw [roundRatio_eq _ _ hd] at h
  obtain ⟨h₀, h₁, h₂⟩ := floor_spec numerator hd
  simp only [Option.some.injEq] at h
  generalize hq : numerator.fdiv denominator = q at *
  have hsucc : (q + 1) * (denominator : Int) = q * denominator + denominator := by
    rw [Int.add_mul, Int.one_mul]
  rcases hmode with rfl | rfl <;> simp only at h <;> subst h
  all_goals
    repeat' split
    all_goals first | omega | (rw [hsucc]; omega)

/-- On an exact tie, `rne` returns the even neighbour. -/
theorem roundRatio_rne_tie_even (hd : 0 < denominator) {result : Int}
    (h : roundRatio .rne numerator denominator = some result)
    (htie : 2 * (numerator % denominator) = denominator) : result % 2 = 0 := by
  rw [roundRatio_eq _ _ hd] at h
  simp only [Option.some.injEq] at h
  have hq : numerator.fdiv denominator = numerator / denominator :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hmod := Int.mul_ediv_add_emod numerator denominator
  have hrem : numerator - numerator.fdiv denominator * denominator = numerator % denominator := by
    rw [hq]; grind
  rw [hrem] at h
  have hlt : ¬ 2 * (numerator % (denominator : Int)) < denominator := by omega
  have hgt : ¬ 2 * (numerator % (denominator : Int)) > denominator := by omega
  simp only [hlt, hgt, ↓reduceIte] at h
  subst h
  split <;> omega

/-- On an exact tie, `rna` rounds away from zero. -/
theorem roundRatio_rna_tie_away (hd : 0 < denominator) {result : Int}
    (h : roundRatio .rna numerator denominator = some result)
    (htie : 2 * (numerator % denominator) = denominator) :
    if numerator < 0 then result * denominator < numerator else numerator < result * denominator := by
  rw [roundRatio_eq _ _ hd] at h
  simp only [Option.some.injEq] at h
  obtain ⟨h₀, h₁, h₂⟩ := floor_spec numerator hd
  have hq : numerator.fdiv denominator = numerator / denominator :=
    Int.fdiv_eq_ediv_of_nonneg _ (by omega)
  have hmod := Int.mul_ediv_add_emod numerator denominator
  have hrem : numerator - numerator.fdiv denominator * denominator = numerator % denominator := by
    rw [hq]; grind
  simp only [hrem] at h h₀ h₁ h₂
  have hlt : ¬ 2 * (numerator % (denominator : Int)) < denominator := by omega
  have hgt : ¬ 2 * (numerator % (denominator : Int)) > denominator := by omega
  simp only [hlt, hgt, ↓reduceIte] at h
  generalize hq' : numerator.fdiv denominator = q at *
  have hsucc : (q + 1) * (denominator : Int) = q * denominator + denominator := by
    rw [Int.add_mul, Int.one_mul]
  subst h
  by_cases hn : numerator < 0
  · simp only [hn, ↓reduceIte]
    omega
  · simp only [hn, ↓reduceIte, hsucc]
    omega

/-- Exact ratios are returned unchanged in every rounding mode. -/
theorem roundRatio_exact (mode : RMode) (quotient : Int) (hd : 0 < denominator) :
    roundRatio mode (quotient * denominator) denominator = some quotient := by
  have hdI : (0 : Int) < denominator := by omega
  have hfdiv : (quotient * denominator).fdiv denominator = quotient := by
    rw [Int.fdiv_eq_ediv_of_nonneg _ (by omega), Int.mul_ediv_cancel _ (by omega)]
  have htdiv : (quotient * denominator).tdiv denominator = quotient :=
    Int.mul_tdiv_cancel _ (by omega)
  rw [roundRatio_eq _ _ hd]
  simp only [hfdiv, htdiv, Int.sub_self]
  cases mode <;> simp [hd]

/-- Truncation agrees with the floor on non-negative numerators. -/
theorem roundRatio_rtz_nonneg (hn : 0 ≤ numerator) (hd : 0 < denominator) :
    roundRatio .rtz numerator denominator = roundRatio .rtn numerator denominator := by
  rw [roundRatio_eq _ _ hd, roundRatio_eq _ _ hd]
  simp only
  rw [Int.fdiv_eq_tdiv_of_nonneg hn (by omega)]

/-- Truncation is odd in the numerator. -/
theorem roundRatio_rtz_neg (hd : 0 < denominator) :
    roundRatio .rtz (-numerator) denominator =
      (roundRatio .rtz numerator denominator).map (- ·) := by
  rw [roundRatio_eq _ _ hd, roundRatio_eq _ _ hd]
  simp only [Option.map_some, Int.neg_tdiv]

/-- Floor and ceiling are dual through negation. -/
theorem roundRatio_rtp_neg (hd : 0 < denominator) :
    roundRatio .rtp (-numerator) denominator =
      (roundRatio .rtn numerator denominator).map (- ·) := by
  obtain ⟨result, hresult⟩ := Option.isSome_iff_exists.1 (roundRatio_isSome .rtn numerator hd)
  obtain ⟨dual, hdual⟩ := Option.isSome_iff_exists.1 (roundRatio_isSome .rtp (-numerator) hd)
  rw [hresult, hdual, Option.map_some, Option.some.injEq]
  obtain ⟨l₁, l₂⟩ := roundRatio_rtn hd hresult
  obtain ⟨u₁, u₂⟩ := roundRatio_rtp hd hdual
  have hdI : (0 : Int) < denominator := by omega
  have e₁ : (result + 1) * (denominator : Int) = result * denominator + denominator := by
    rw [Int.add_mul, Int.one_mul]
  have e₂ : (dual - 1) * (denominator : Int) = dual * denominator - denominator := by
    rw [Int.sub_mul, Int.one_mul]
  have e₃ : (-result + 1) * (denominator : Int) = -(result * denominator) + denominator := by
    rw [Int.add_mul, Int.neg_mul, Int.one_mul]
  have e₄ : (-result - 1) * (denominator : Int) = -(result * denominator) - denominator := by
    rw [Int.sub_mul, Int.neg_mul, Int.one_mul]
  have hup : dual * denominator < (-result + 1) * denominator := by omega
  have hlo : (-result - 1) * denominator < dual * denominator := by omega
  have h₁ := Int.lt_of_mul_lt_mul_right hup (by omega)
  have h₂ := Int.lt_of_mul_lt_mul_right hlo (by omega)
  omega

end Rounding

end IEEE

/-! ## Targets -/

namespace TargetLaws

open Bap.Theory

local notation "T" => Bap.Theory.Target
local notation "RV" => Bap.Theory.Var

open_private Bap.Theory.Target Bap.Theory.originOf as originOf
open_private Bap.Theory.Target Bap.Theory.bitRegisters as bitRegisters

/-! ### Declarations -/

/-- The parent a declaration inherits from: the named one, or `unknown`. -/
abbrev parentOf (declaration : Declaration) : T := declaration.parent.getD unknown

theorem declare_family (declaration : Declaration) :
    (declare declaration).family = (parentOf declaration).name :: (parentOf declaration).family ∧
      (declare declaration).parent = some (parentOf declaration).name := by
  simp [declare]

/-- Not naming a parent is the same as naming `unknown`. -/
theorem declare_no_parent {declaration : Declaration} (h : declaration.parent = none) :
    declare declaration = declare { declaration with parent := some unknown } := by
  simp [declare, h]

/-- A parentless declaration descends directly from `unknown`, upstream's default. -/
theorem declare_root_family {declaration : Declaration} (h : declaration.parent = none) :
    (declare declaration).family = ["unknown"] ∧ (declare declaration).parent = some "unknown" := by
  simp [declare, h, unknown]

/-- A declaration that overrides nothing inherits every semantic field from its parent. -/
theorem declare_inherits {declaration : Declaration} {parent : T} (hp : declaration.parent = some parent)
    (hbits : declaration.bits = none) (hbyte : declaration.byte = none)
    (hdataAlignment : declaration.dataAlignment = none) (hcodeAlignment : declaration.codeAlignment = none)
    (hdata : declaration.data = none) (hcode : declaration.code = none)
    (hregs : declaration.regs = none)
    (haliases : declaration.aliases = none) (hendianness : declaration.endianness = none)
    (hsystem : declaration.system = none) (habi : declaration.abi = none) (hfabi : declaration.fabi = none)
    (hfiletype : declaration.filetype = none) (hoptions : declaration.options = none) :
    let child := declare declaration
    child.bits = parent.bits ∧ child.byte = parent.byte ∧ child.dataAlignment = parent.dataAlignment ∧
      child.codeAlignment = parent.codeAlignment ∧ child.data = parent.data ∧ child.code = parent.code ∧
      child.regs = parent.regs ∧ child.aliases = parent.aliases ∧
      child.endianness = parent.endianness ∧ child.system = parent.system ∧ child.abi = parent.abi ∧
      child.fabi = parent.fabi ∧ child.filetype = parent.filetype ∧ child.options = parent.options := by
  simp [declare, hp, hbits, hbyte, hdataAlignment, hcodeAlignment, hdata, hcode, hregs,
    haliases, hendianness, hsystem, habi, hfabi, hfiletype, hoptions]

/-- Explicit fields always win over inheritance, whatever the parent is. -/
theorem declare_overrides (declaration : Declaration) :
    (∀ value, declaration.bits = some value → (declare declaration).bits = value) ∧
      (∀ value, declaration.byte = some value → (declare declaration).byte = value) ∧
      (∀ value, declaration.data = some value → (declare declaration).data = some value) ∧
      (∀ value, declaration.vars = some value → ∀ var ∈ value, var ∈ (declare declaration).vars) ∧
      (∀ value, declaration.endianness = some value → (declare declaration).endianness = value) ∧
      (∀ value, declaration.system = some value → (declare declaration).system = value) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro value h
  · simp [declare, h]
  · simp [declare, h]
  · simp [declare, h]
  · intro var hv
    simp [declare, h, List.mem_eraseDups, hv]
  · simp [declare, h]
  · simp [declare, h]

theorem mem_vars_declare (declaration : Declaration) (var : RV) :
    var ∈ (declare declaration).vars ↔
      var ∈ declaration.vars.getD (parentOf declaration).vars ∨
        (declare declaration).data = some var ∨ (declare declaration).code = some var ∨
        ∃ group ∈ (declare declaration).regs, var ∈ group.2 := by
  simp [declare, List.mem_eraseDups, or_assoc]

/-! ### The hierarchy -/

/-- `Descends child ancestor`: `child` is reachable from `ancestor` by repeated `declare`. -/
inductive Descends : T → T → Prop where
  | refl (target : T) : Descends target target
  | step {declaration : Declaration} {ancestor : T} :
      Descends (parentOf declaration) ancestor → Descends (declare declaration) ancestor

theorem Descends.trans {a b c : T} (hab : Descends a b) (hbc : Descends b c) : Descends a c := by
  induction hab with
  | refl => exact hbc
  | step _ ih => exact .step (ih hbc)

theorem belongs_declare_iff (declaration : Declaration) (ancestor : T) :
    ancestor.belongs (declare declaration) = true ↔
      ancestor.name = declaration.name ∨ ancestor.belongs (parentOf declaration) = true := by
  simp [Target.belongs, declare]

theorem Descends.belongs {child ancestor : T} (h : Descends child ancestor) :
    ancestor.belongs child = true := by
  induction h with
  | refl target => exact Target.belongs_self target
  | step _ ih => exact (belongs_declare_iff _ _).2 (Or.inr ih)

/-- Membership of `ancestor`'s line is inherited by everything below the target it belongs to. -/
theorem belongs_trans {a b c : T} (hab : a.belongs b = true) (hbc : Descends c b) :
    a.belongs c = true := by
  induction hbc with
  | refl => exact hab
  | step _ ih => exact (belongs_declare_iff _ _).2 (Or.inr (ih hab))

/-- Ancestor lists nest: an ancestor's family is a suffix of each descendant's. -/
theorem Descends.family_suffix {child ancestor : T} (h : Descends child ancestor) :
    ancestor.family <:+ child.family := by
  induction h with
  | refl => exact List.suffix_refl _
  | step _ ih =>
    rw [(declare_family _).1]
    exact ih.trans (List.suffix_cons _ _)

/-- Each `declare` step strictly deepens the hierarchy, so descent has no cycles. -/
theorem Descends.depth_lt {child ancestor : T} (h : Descends child ancestor) (hne : child ≠ ancestor) :
    ancestor.family.length < child.family.length := by
  induction h with
  | refl => exact absurd rfl hne
  | @step declaration ancestor hrest _ =>
    rw [(declare_family _).1, List.length_cons]
    have := hrest.family_suffix.length_le
    omega

theorem Descends.antisymm {a b : T} (hab : Descends a b) (hba : Descends b a) : a = b := by
  by_cases hne : a = b
  · exact hne
  · have h₁ := hab.depth_lt hne
    have h₂ := hba.depth_lt (Ne.symm hne)
    omega

theorem Descends.parent_mem {child ancestor : T} (h : Descends child ancestor) (hne : child ≠ ancestor) :
    ancestor.name ∈ child.parents := by
  have hb := h.belongs
  induction h with
  | refl => exact absurd rfl hne
  | @step declaration ancestor hrest ih =>
    simp only [Target.parents, (declare_family _).1, List.mem_cons]
    by_cases hpa : parentOf declaration = ancestor
    · rw [hpa]
      exact Or.inl rfl
    · exact Or.inr (ih hpa hrest.belongs)

/-- Targets built from `unknown` by `declare`. -/
inductive Declared : T → Prop where
  | root : Declared unknown
  | child {declaration : Declaration} : Declared (parentOf declaration) → Declared (declare declaration)

/-- `unknown` is the root of the hierarchy: everything declared descends from it, whether or not
its declaration chain names a parent. -/
theorem Declared.descends_unknown {target : T} (h : Declared target) : Descends target unknown := by
  induction h with
  | root => exact .refl _
  | child _ ih => exact .step ih

theorem Declared.unknown_belongs {target : T} (h : Declared target) : unknown.belongs target = true :=
  h.descends_unknown.belongs

/-- Each target's parents end at `unknown`. -/
theorem Declared.parents_end_unknown {target : T} (h : Declared target) :
    target = unknown ∨ target.parents.getLast? = some "unknown" := by
  induction h with
  | root => exact Or.inl rfl
  | @child declaration _ ih =>
    refine Or.inr ?_
    simp only [Target.parents, (declare_family _).1]
    rcases ih with ih | ih
    · rw [ih]; rfl
    · simp only [Target.parents] at ih
      rw [List.getLast?_cons]
      simp [ih]

/-- A bare declaration has upstream's defaults, by way of `unknown`. -/
theorem declare_bare_defaults (name : String) :
    let target := declare { name := name }
    target.bits = 32 ∧ target.byte = 8 ∧ target.dataAlignment = 8 ∧ target.codeAlignment = 8 ∧
      target.endianness = .eb ∧ target.data = unknown.data ∧ target.code = unknown.code ∧
      target.system = .unknown ∧ target.abi = .unknown ∧ target.fabi = .unknown ∧
      target.filetype = .unknown := by
  simp [declare, unknown]

/-! ### Name matching -/

private theorem char_toLower_idem (c : Char) : c.toLower.toLower = c.toLower := by
  apply Char.ext
  simp only [Char.toLower]
  grind

private theorem toLower_idem (name : String) : name.toLower.toLower = name.toLower := by
  apply String.toList_inj.1
  simp only [String.toLower, String.toList_map, List.map_map]
  apply List.map_congr_left
  intro c _
  exact char_toLower_idem c

theorem matches_iff (target : T) (name : String) :
    target.matches name = true ↔
      ∃ entry ∈ (target.name, target.nicknames) :: target.lineage, namedBy name entry = true := by
  simp only [Target.matches, Target.matching, Option.isSome_map, List.find?_isSome]

theorem namedBy_iff (name : String) (entry : String × List String) :
    namedBy name entry = true ↔
      entry.1.toLower = name.toLower ∨ ∃ nickname ∈ entry.2, nickname.toLower = name.toLower := by
  simp [namedBy]

/-- Matching depends on the query only through its lower-cased form. -/
theorem matches_congr (target : T) {left right : String} (h : left.toLower = right.toLower) :
    target.matches left = target.matches right := by
  have hsame : namedBy left = namedBy right := by
    funext entry
    simp [namedBy, h]
  simp only [Target.matches, Target.matching, hsame]

theorem matches_toLower (target : T) (name : String) :
    target.matches name.toLower = target.matches name :=
  matches_congr target (toLower_idem name)

theorem matches_nickname {target : T} {nickname : String} (h : nickname ∈ target.nicknames) :
    target.matches nickname = true :=
  (matches_iff _ _).2 ⟨_, List.mem_cons_self, (namedBy_iff _ _).2 (Or.inr ⟨nickname, h, rfl⟩)⟩

/-- A declaration matches what its own names match, or whatever its parent matches: upstream's
walk up the hierarchy. -/
theorem matches_declare_iff (declaration : Declaration) (name : String) :
    (declare declaration).matches name = true ↔
      namedBy name (declaration.name, (declare declaration).nicknames) = true ∨
        (parentOf declaration).matches name = true := by
  simp only [matches_iff]
  simp [declare]

theorem Descends.matches {child ancestor : T} {name : String} (h : Descends child ancestor)
    (hm : ancestor.matches name = true) : child.matches name = true := by
  induction h with
  | refl => exact hm
  | step _ ih => exact (matches_declare_iff _ _).2 (Or.inr (ih hm))

/-- Without nicknames of its own, a declaration keeps its parent's. -/
theorem nicknames_inherited {declaration : Declaration} (h : declaration.nicknames = none) :
    (declare declaration).nicknames = (parentOf declaration).nicknames := by
  simp [declare, h]

/-- Everything declared matches every ancestor's name, up to `unknown`. -/
theorem Declared.matches_unknown {target : T} (h : Declared target) : target.matches "unknown" = true := by
  apply h.descends_unknown.matches
  exact (matches_iff _ _).2 ⟨_, List.mem_cons_self, (namedBy_iff _ _).2 (Or.inl rfl)⟩

/-- `matching` prefers the target itself over any ancestor. -/
theorem matching_self {target : T} {name : String} (h : namedBy name (target.name, target.nicknames) = true) :
    target.matching name = some target.name := by
  simp [Target.matching, h]

/-- Otherwise it answers with the closest ancestor. -/
theorem matching_declare {declaration : Declaration} {name : String}
    (h : namedBy name (declaration.name, (declare declaration).nicknames) = false) :
    (declare declaration).matching name = (parentOf declaration).matching name := by
  simp only [Target.matching]
  have hdecl : (declare declaration).name = declaration.name := rfl
  rw [List.find?_cons, hdecl, h]
  simp [declare]

theorem matches_eq_matching_isSome (target : T) (name : String) :
    target.matches name = (target.matching name).isSome := rfl

/-! ### The registry -/

theorem mem_register (candidate target : T) (registry : List T) :
    candidate ∈ register target registry ↔
      candidate = target ∨ (candidate ∈ registry ∧ candidate.name ≠ target.name) := by
  simp [register]

theorem register_names_nodup (target : T) (registry : List T)
    (h : (registry.map Target.name).Nodup) : ((register target registry).map Target.name).Nodup := by
  simp only [register, List.map_cons, List.nodup_cons, List.mem_map, List.mem_filter, not_exists, not_and]
  refine ⟨?_, ?_⟩
  · rintro x ⟨_, hne⟩ heq
    simp [heq] at hne
  · induction registry with
    | nil => simp
    | cons head tail ih =>
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at h
      simp only [List.filter_cons]
      split
      · simp only [List.map_cons, List.nodup_cons, List.mem_map, List.mem_filter]
        exact ⟨fun ⟨x, ⟨hx, _⟩, heq⟩ => h.1 ⟨x, hx, heq⟩, ih h.2⟩
      · exact ih h.2

theorem register_idempotent (target : T) (registry : List T) :
    register target (register target registry) = register target registry := by
  simp only [register, List.filter_cons]
  simp [List.filter_filter]

/-- Registering different names commutes, up to list order. -/
theorem register_comm {left right : T} (h : left.name ≠ right.name) (registry : List T) :
    (register left (register right registry)).Perm (register right (register left registry)) := by
  have hl : (right.name != left.name) = true := by simpa using Ne.symm h
  have hr : (left.name != right.name) = true := by simpa using h
  simp only [register, List.filter_cons, hl, hr, ite_true, List.filter_filter]
  have hcomm : registry.filter (fun x => (x.name != left.name) && (x.name != right.name)) =
      registry.filter (fun x => (x.name != right.name) && (x.name != left.name)) := by
    apply List.filter_congr
    intro x _
    exact Bool.and_comm _ _
  rw [hcomm]
  exact List.Perm.swap _ _ _

theorem get_sound {name : String} {registry : List T} {target : T} (h : get name registry = some target) :
    target ∈ registry ∧ target.name = name := by
  have := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using this⟩

theorem get_isSome_iff (name : String) (registry : List T) :
    (get name registry).isSome = true ↔ ∃ target ∈ registry, target.name = name := by
  simp [Bap.Theory.get, List.find?_isSome]

/-- On a registry with unique names, `get` finds exactly the named target. -/
theorem get_eq_some_iff {registry : List T} (hnames : (registry.map Target.name).Nodup) (name : String)
    (target : T) : get name registry = some target ↔ target ∈ registry ∧ target.name = name := by
  refine ⟨get_sound, ?_⟩
  rintro ⟨hmem, rfl⟩
  induction registry with
  | nil => cases hmem
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnames
    simp only [Bap.Theory.get, List.find?_cons]
    rcases List.mem_cons.1 hmem with rfl | hmem
    · simp
    · have hne : head.name ≠ target.name := fun h => hnames.1 target hmem h.symm
      simp only [hne, decide_false]
      exact ih hnames.2 hmem

/-- `get` is by name only: a nickname, or an ancestor's name, is not a name. -/
theorem get_ignores_nicknames (name : String) {registry : List T} (h : ∀ target ∈ registry, target.name ≠ name) :
    get name registry = none := by
  simp only [Bap.Theory.get, List.find?_eq_none, decide_eq_true_eq]
  exact h

theorem get_register_self (target : T) (registry : List T) :
    get target.name (register target registry) = some target := by
  simp [Bap.Theory.get, register]

private theorem find?_filter_of_false {p q : T → Bool} (values : List T)
    (h : ∀ value ∈ values, q value = false → p value = false) :
    (values.filter q).find? p = values.find? p := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    have htail := ih fun value hmem => h value (List.mem_cons_of_mem _ hmem)
    simp only [List.filter_cons]
    cases hq : q head with
    | true => simp [List.find?_cons, htail]
    | false =>
      have hp := h head List.mem_cons_self hq
      simp [hp, htail]

/-- Registering a target leaves every other name's lookup alone. -/
theorem get_register_frame {target : T} {name : String} (registry : List T) (hne : target.name ≠ name) :
    get name (register target registry) = get name registry := by
  simp only [Bap.Theory.get, register, List.find?_cons, hne, decide_false]
  apply find?_filter_of_false
  intro value _ hq
  have : value.name = target.name := by simpa using hq
  simp [this, hne]

/-! ### Selection -/

theorem fieldMatches_iff [DecidableEq α] (strict : Bool) (none actual wanted : α) :
    fieldMatches strict none actual wanted = true ↔
      actual = wanted ∨ (strict = false ∧ wanted = none) := by
  cases strict <;> simp [fieldMatches, or_comm]

/-- An unknown requirement accepts anything, unless strict. -/
theorem fieldMatches_unknown [DecidableEq α] (none actual : α) : fieldMatches false none actual none = true := by
  simp [fieldMatches]

/-- An unknown property satisfies no specific requirement, as in upstream's flat domain. -/
theorem fieldMatches_unknown_actual [DecidableEq α] (strict : Bool) {none wanted : α} (h : wanted ≠ none) :
    fieldMatches strict none none wanted = false := by
  cases strict <;> simp [fieldMatches, Ne.symm h, h]

/-- The conditions `filter` imposes on one target. -/
def Selected (selection : Selection) (target : T) : Prop :=
  target.name ≠ unknown.name ∧ selection.parent.belongs target = true ∧
    fieldMatches selection.strict .unknown target.system selection.system = true ∧
    fieldMatches selection.strict .unknown target.abi selection.abi = true ∧
    fieldMatches selection.strict .unknown target.fabi selection.fabi = true ∧
    fieldMatches selection.strict .unknown target.filetype selection.filetype = true ∧
    fieldMatches selection.strict "" target.options selection.options = true

theorem mem_filter (selection : Selection) (targets : List T) (target : T) :
    target ∈ filter selection targets ↔ target ∈ targets ∧ Selected selection target := by
  simp [filter, Selected, and_assoc]

/-- The default selection keeps every declared target, and never `unknown` itself. -/
theorem filter_default {targets : List T} (h : ∀ target ∈ targets, Declared target ∧ target.name ≠ unknown.name) :
    filter {} targets = targets := by
  apply List.filter_eq_self.2
  intro target hmem
  obtain ⟨hd, hn⟩ := h target hmem
  simp [hd.unknown_belongs, fieldMatches, hn]

theorem filter_idempotent (selection : Selection) (targets : List T) :
    filter selection (filter selection targets) = filter selection targets := by
  simp [filter, List.filter_filter]

/-- Tightening a selection to `strict` can only remove candidates. -/
theorem filter_strict_subset (selection : Selection) (targets : List T) {target : T}
    (h : target ∈ filter { selection with strict := true } targets) :
    target ∈ filter { selection with strict := false } targets := by
  rw [mem_filter] at *
  obtain ⟨hmem, h₀, h₁, h₂, h₃, h₄, h₅, h₆⟩ := h
  simp only [fieldMatches_iff] at h₂ h₃ h₄ h₅ h₆ ⊢
  refine ⟨hmem, h₀, h₁, ?_⟩
  simp only [fieldMatches_iff, true_and] at *
  grind

/-- A strict selection demands exactly the requested properties, inherited ones included. -/
theorem filter_strict_iff {selection : Selection} (hstrict : selection.strict = true) (targets : List T)
    (target : T) :
    target ∈ filter selection targets ↔
      target ∈ targets ∧ target.name ≠ unknown.name ∧ selection.parent.belongs target = true ∧
        target.system = selection.system ∧ target.abi = selection.abi ∧ target.fabi = selection.fabi ∧
        target.filetype = selection.filetype ∧ target.options = selection.options := by
  simp [mem_filter, Selected, fieldMatches_iff, hstrict]

/-- A non-strict selection only constrains the properties it names. -/
theorem filter_nonstrict_system {selection : Selection} (hstrict : selection.strict = false) {targets : List T}
    {target : T} (h : target ∈ filter selection targets) :
    selection.system = .unknown ∨ target.system = selection.system := by
  obtain ⟨_, _, _, hs, _⟩ := (mem_filter _ _ _).1 h
  have := (fieldMatches_iff _ _ _ _).1 hs
  simp only [hstrict, true_and] at this
  exact this.symm

/-- Every target passing a selection belongs to its `parent`. -/
theorem filter_belongs {selection : Selection} {targets : List T} {target : T}
    (h : target ∈ filter selection targets) : selection.parent.belongs target = true :=
  ((mem_filter _ _ _).1 h).2.2.1

theorem select_sound {selection : Selection} {targets : List T} {target : T}
    (h : select selection targets = some target) : target ∈ filter selection targets := by
  unfold select at h
  split at h
  · cases h; simp_all
  · split at h
    · cases h
    · cases h; simp_all
  · cases h

/-- A `unique` selection succeeds only when exactly one candidate survives. -/
theorem select_unique_iff {selection : Selection} (hunique : selection.unique = true)
    (targets : List T) (target : T) :
    select selection targets = some target ↔ filter selection targets = [target] := by
  unfold select
  split
  · simp_all
  · simp_all
  · simp_all

theorem select_nonunique_eq_head {selection : Selection} (hunique : selection.unique = false)
    (targets : List T) : select selection targets = (filter selection targets).head? := by
  unfold select
  split <;> simp_all

/-! ### Registers -/

theorem hasRole_iff (target : T) (var : RV) (role : Role) :
    target.hasRole var role = true ↔ ∃ group ∈ target.regs, role ∈ group.1 ∧ var ∈ group.2 := by
  simp [Target.hasRole]

/-- `registers` holds what has all the requested roles and none of the excluded ones, among the
registers that have any role at all. -/
theorem mem_registers (target : T) (roles exclude : List Role) (var : RV) :
    var ∈ target.registers roles exclude ↔
      (∃ group ∈ target.regs, group.1 ≠ [] ∧ var ∈ group.2) ∧
        (∀ role ∈ roles, target.hasRole var role = true) ∧
        ∀ role ∈ exclude, target.hasRole var role = false := by
  simp [Target.registers, List.mem_eraseDups, and_assoc]

theorem registers_nodup (target : T) (roles exclude : List Role) :
    (target.registers roles exclude).Nodup :=
  (nodup_eraseDups _).filter _

theorem registers_exclude_anti (target : T) (roles : List Role) {narrow wide : List Role}
    (h : ∀ role ∈ narrow, role ∈ wide) {var : RV} (hv : var ∈ target.registers roles wide) :
    var ∈ target.registers roles narrow := by
  rw [mem_registers] at *
  exact ⟨hv.1, hv.2.1, fun role hr => hv.2.2 role (h role hr)⟩

/-- Asking for more roles narrows the answer: each register has all of them. -/
theorem registers_roles_anti (target : T) (exclude : List Role) {few many : List Role}
    (h : ∀ role ∈ few, role ∈ many) {var : RV} (hv : var ∈ target.registers many exclude) :
    var ∈ target.registers few exclude := by
  rw [mem_registers] at *
  exact ⟨hv.1, fun role hr => hv.2.1 role (h role hr), hv.2.2⟩

theorem mem_registers_singleton (target : T) (role : Role) (var : RV) :
    var ∈ target.registers [role] ↔ target.hasRole var role = true := by
  rw [mem_registers]
  simp only [List.mem_singleton, forall_eq, List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  obtain ⟨group, hg, hr, hv⟩ := (hasRole_iff _ _ _).1 h
  exact ⟨group, hg, List.ne_nil_of_mem hr, hv⟩

/-- Several roles select the intersection, not the union, of the single-role answers. -/
theorem mem_registers_roles (target : T) {roles : List Role} (hne : roles ≠ []) (var : RV) :
    var ∈ target.registers roles ↔ ∀ role ∈ roles, var ∈ target.registers [role] := by
  simp only [mem_registers_singleton]
  rw [mem_registers]
  simp only [List.not_mem_nil, false_implies, implies_true, and_true]
  refine ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
  cases roles with
  | nil => exact absurd rfl hne
  | cons role rest =>
    obtain ⟨group, hg, hr, hv⟩ := (hasRole_iff _ _ _).1 (h role List.mem_cons_self)
    exact ⟨group, hg, List.ne_nil_of_mem hr, hv⟩

/-- An excluded role removes a register even when another of its groups would keep it. -/
theorem registers_exclude_any_group {target : T} {roles exclude : List Role} {var : RV} {role : Role}
    (hrole : role ∈ exclude) (has : target.hasRole var role = true) :
    var ∉ target.registers roles exclude := by
  intro hv
  have := ((mem_registers _ _ _ _).1 hv).2.2 role hrole
  rw [has] at this
  cases this

theorem reg_sound {target : T} {role : Role} {unique : Bool} {exclude : List Role} {var : RV}
    (h : target.reg role unique exclude = some var) : var ∈ target.registers [role] exclude := by
  cases hr : target.registers [role] exclude with
  | nil => simp [Target.reg, hr] at h
  | cons head tail =>
    cases tail with
    | nil =>
      simp only [Target.reg, hr, Option.some.injEq] at h
      simp [h]
    | cons next rest =>
      simp only [Target.reg, hr] at h
      split at h
      · cases h
      · cases h
        simp

/-- With `unique`, a role resolves only when exactly one register carries it. -/
theorem reg_unique_iff (target : T) (role : Role) (exclude : List Role) (var : RV) :
    target.reg role true exclude = some var ↔ target.registers [role] exclude = [var] := by
  unfold Target.reg
  split <;> simp_all

theorem reg_isSome_iff (target : T) (role : Role) (exclude : List Role) :
    (target.reg role false exclude).isSome = true ↔ target.registers [role] exclude ≠ [] := by
  unfold Target.reg
  split <;> simp_all

/-- `hasRoles` means `var` is registered under each role, as upstream's `has_roles`. -/
theorem hasRoles_iff (target : T) (roles : List Role) (var : RV) :
    target.hasRoles roles var = true ↔ ∀ role ∈ roles, var ∈ target.registers [role] := by
  simp [Target.hasRoles, mem_registers_singleton]

/-- `registers` and `hasRoles` agree for any non-empty role list. -/
theorem mem_registers_iff_hasRoles (target : T) {roles : List Role} (hne : roles ≠ []) (var : RV) :
    var ∈ target.registers roles ↔ target.hasRoles roles var = true := by
  rw [mem_registers_roles target hne, hasRoles_iff]

/-- Intended, as upstream's `List.for_all`: "has all of no roles" holds for any variable. -/
theorem hasRoles_nil (target : T) (var : RV) : target.hasRoles [] var = true := rfl

/-- A variable the target does not register has none of the roles asked for. -/
theorem hasRoles_absent {target : T} {var : RV} {roles : List Role} (hne : roles ≠ [])
    (habsent : ∀ group ∈ target.regs, var ∉ group.2) : target.hasRoles roles var = false := by
  cases roles with
  | nil => exact absurd rfl hne
  | cons role rest =>
    apply Bool.eq_false_iff.2
    intro h
    obtain ⟨group, hg, _, hv⟩ := (hasRole_iff ..).1 ((mem_registers_singleton ..).1
      ((hasRoles_iff ..).1 h role List.mem_cons_self))
    exact habsent group hg hv

/-- Roles accumulate independently of how the register groups are laid out. -/
theorem hasRoles_append (target : T) (first second : List Role) (var : RV) :
    target.hasRoles (first ++ second) var = (target.hasRoles first var && target.hasRoles second var) := by
  simp [Target.hasRoles, List.all_append]

theorem var_sound {target : T} {name : String} {var : RV} (h : target.var name = some var) :
    var ∈ target.vars ∧ var.name = name := by
  have hp := List.find?_some h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using hp⟩

theorem var_isSome_iff (target : T) (name : String) :
    (target.var name).isSome = true ↔ ∃ var ∈ target.vars, var.name = name := by
  simp [Target.var, List.find?_isSome]

/-! ### Aliases -/

/-- A valuation of the bits of the registers satisfies the aliasing equations of a target. -/
def Model (target : T) (value : RV → Nat → Bool) : Prop :=
  ∀ alias ∈ target.aliases, ∀ span ∈ alias.spans.getD [], ∀ index < span.width,
    value span.var index = value alias.target (span.offset + index)

theorem linked_sound {target : T} {value : RV → Nat → Bool} (hm : Model target value) {var other : RV}
    {index at' : Nat} (h : (other, at') ∈ target.linked var index) : value var index = value other at' := by
  obtain ⟨alias, halias, hin⟩ := List.mem_flatMap.1 h
  obtain ⟨span, hspan, hfound⟩ := List.mem_filterMap.1 hin
  have heq := hm alias halias span hspan
  split at hfound
  · rename_i hc
    obtain ⟨rfl, hlo, hhi⟩ := hc
    simp only [Option.some.injEq, Prod.mk.injEq] at hfound
    obtain ⟨rfl, rfl⟩ := hfound
    have hbit := heq (index - span.offset) (by omega)
    rw [Nat.add_sub_cancel' hlo] at hbit
    exact hbit.symm
  · split at hfound
    · rename_i hc
      obtain ⟨rfl, hhi⟩ := hc
      simp only [Option.some.injEq, Prod.mk.injEq] at hfound
      obtain ⟨rfl, rfl⟩ := hfound
      exact heq index hhi
    · cases hfound

/-- A located bit is a bit of a basis register, and the equations make it equal to the bit asked for. -/
theorem locate_sound {target : T} {fuel : Nat} {seen : List (RV × Nat)} {var base : RV} {index at' : Nat}
    (h : target.locate fuel seen var index = some (base, at')) :
    target.isAlias base = false ∧ (∃ width, regWidth base = some width ∧ at' < width) ∧
      ∀ value, Model target value → value var index = value base at' := by
  induction fuel generalizing seen var index with
  | zero => simp [Target.locate] at h
  | succ fuel ih =>
    rw [Target.locate] at h
    split at h
    · obtain ⟨⟨other, at''⟩, hmem, hfound⟩ := List.exists_of_findSome?_eq_some h
      split at hfound
      · cases hfound
      · obtain ⟨hbasis, hwidth, hval⟩ := ih hfound
        exact ⟨hbasis, hwidth, fun value hm => (linked_sound hm hmem).trans (hval value hm)⟩
    · rename_i hbasis
      split at h
      · rename_i hrange
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        refine ⟨by simpa using hbasis, ?_, fun _ _ => rfl⟩
        cases hw : regWidth var with
        | none => simp [hw] at hrange
        | some width => exact ⟨width, rfl, by simpa [hw] using hrange⟩
      · cases h

private theorem mapM_some {f : Nat → Option β} {values : List Nat} {results : List β}
    (h : values.mapM f = some results) :
    results.length = values.length ∧ ∀ i (hi : i < values.length), ∃ result, results[i]? = some result ∧
      f values[i] = some result := by
  induction values generalizing results with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    simp [← h]
  | cons head tail ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨first, hfirst, rest, hrest, rfl⟩ := h
    obtain ⟨hlen, hall⟩ := ih hrest
    refine ⟨by simp [hlen], fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨first, by simp, hfirst⟩
    | succ i => simpa using hall i (by simpa using hi)

private theorem mapM_of_all {f : Nat → Option β} {g : Nat → β} {values : List Nat}
    (h : ∀ value ∈ values, f value = some (g value)) : values.mapM f = some (values.map g) := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.mem_cons, forall_eq_or_imp] at h
    simp [List.mapM_cons, h.1, ih h.2]

private theorem originOf_locations {bits : List (RV × Nat)} {origin : Origin} (h : originOf bits = some origin) :
    origin.locations = bits := by
  unfold originOf at h
  split at h
  · cases h
  · simp only at h
    split at h
    · rename_i hsub
      cases h
      exact hsub
    · split at h
      · rename_i hregs
        split at h
        · cases h
          simpa [Origin.locations] using hregs
        · split at h
          · cases h
            simpa [Origin.locations] using hregs
          · cases h
      · cases h

private theorem originOf_sub {bits : List (RV × Nat)} {reg : RV} {hi lo : Nat} {whole : Bool}
    (h : originOf bits = some (.sub reg hi lo whole)) :
    bits ≠ [] ∧ hi = lo + bits.length - 1 ∧ whole = (regWidth reg == some bits.length) := by
  unfold originOf at h
  split at h
  · cases h
  · simp only at h
    split at h
    · simp only [Option.some.injEq, Origin.sub.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := h
      exact ⟨by simp, rfl, rfl⟩
    · split at h
      · split at h
        · cases h
        · split at h <;> cases h
      · cases h

private theorem mem_bitRegisters {bits : List (RV × Nat)} {reg : RV} (h : reg ∈ bitRegisters bits) :
    ∃ at', (reg, at') ∈ bits := by
  induction bits with
  | nil => cases h
  | cons head tail ih =>
    have hgrow : reg = head.1 ∨ reg ∈ bitRegisters tail := by
      simp only [bitRegisters] at h
      cases hrest : bitRegisters tail with
      | nil =>
        simp only [hrest, List.mem_singleton] at h
        exact .inl h
      | cons first rest =>
        simp only [hrest] at h
        split at h
        · exact .inr h
        · rcases List.mem_cons.1 h with h | h
          · exact .inl h
          · exact .inr h
    rcases hgrow with rfl | hin
    · exact ⟨head.2, List.mem_cons_self⟩
    · obtain ⟨at', hat⟩ := ih hin
      exact ⟨at', List.mem_cons_of_mem _ hat⟩

private theorem originOf_regs {bits : List (RV × Nat)} {origin : Origin} {regs : List RV} (h : originOf bits = some origin)
    (hshape : origin = .sup regs ∨ origin = .set regs) :
    (∀ reg ∈ regs, ∃ at', (reg, at') ∈ bits) ∧ (origin = .sup regs → ∀ reg ∈ regs, reg.sort.bits.isSome = true) ∧
      (origin = .set regs → ∀ reg ∈ regs, reg.sort = .bool) := by
  unfold originOf at h
  split at h
  · cases h
  · simp only at h
    split at h
    · cases h
      rcases hshape with h | h <;> cases h
    · split at h
      · split at h
        · rename_i hall
          cases h
          rcases hshape with h | h
          · cases h
          · simp only [Origin.set.injEq] at h
            subst h
            refine ⟨fun reg hreg => mem_bitRegisters (by simpa using hreg), fun h => (by cases h), fun _ reg hreg => ?_⟩
            simpa using List.all_eq_true.1 hall reg hreg
        · split at h
          · rename_i hall
            cases h
            rcases hshape with h | h
            · simp only [Origin.sup.injEq] at h
              subst h
              refine ⟨fun reg hreg => mem_bitRegisters (by simpa using hreg), fun _ reg hreg => ?_, fun h => (by cases h)⟩
              exact List.all_eq_true.1 hall reg hreg
            · cases h
          · cases h
      · cases h

private theorem unalias_origin {target : T} {var : RV} {origin : Origin} (h : target.unalias var = some origin) :
    ∃ bits, originOf bits = some origin := by
  unfold Target.unalias at h
  by_cases halias : target.isAlias var = true
  · simp only [halias, ↓reduceIte] at h
    cases hw : regWidth var with
    | none => simp [hw] at h
    | some width =>
      simp only [hw] at h
      obtain ⟨bits, _, hor⟩ := Option.bind_eq_some_iff.1 h
      exact ⟨bits, hor⟩
  · simp [halias] at h

/-- What an origin means: it has a bit of a basis register for each bit of the alias, and in every
valuation that satisfies the equations these bits are equal. Whatever the nesting of the definitions. -/
theorem unalias_sound {target : T} {var : RV} {origin : Origin} (h : target.unalias var = some origin) :
    target.isAlias var = true ∧ ∃ width, regWidth var = some width ∧ origin.locations.length = width ∧
      ∀ index, index < width → ∃ base at', origin.locations[index]? = some (base, at') ∧
        target.isAlias base = false ∧ (∃ size, regWidth base = some size ∧ at' < size) ∧
        ∀ value, Model target value → value var index = value base at' := by
  unfold Target.unalias at h
  split at h
  · rename_i halias
    refine ⟨halias, ?_⟩
    split at h
    · rename_i width hw
      obtain ⟨bits, hbits, hor⟩ := Option.bind_eq_some_iff.1 h
      obtain ⟨hlen, hall⟩ := mapM_some hbits
      have hloc := originOf_locations hor
      refine ⟨width, hw, by simpa [hloc] using hlen, fun index hi => ?_⟩
      obtain ⟨⟨base, at'⟩, hget, hfound⟩ := hall index (by simpa using hi)
      rw [List.getElem_range] at hfound
      obtain ⟨hbasis, hsize, hval⟩ := locate_sound hfound
      exact ⟨base, at', by rw [hloc]; exact hget, hbasis, hsize, hval⟩
    · cases h
  · cases h

/-- A sub-register is exactly the bits `hi..lo` of a basis register, where they are in range, and
`hi - lo + 1` is its width: `isAlias` says that these are all the bits of that register. -/
theorem unalias_sub_bits {target : T} {var reg : RV} {hi lo : Nat} {whole : Bool}
    (h : target.unalias var = some (.sub reg hi lo whole)) :
    target.isAlias var = true ∧ target.isAlias reg = false ∧ lo ≤ hi ∧ regWidth var = some (hi - lo + 1) ∧
      (∃ size, regWidth reg = some size ∧ hi < size) ∧ (whole = true ↔ regWidth reg = some (hi - lo + 1)) ∧
      ∀ value, Model target value → ∀ index ≤ hi - lo, value var index = value reg (lo + index) := by
  have hshape : ∃ bits, originOf bits = some (.sub reg hi lo whole) ∧ bits.length = hi - lo + 1 ∧ bits ≠ [] ∧
      hi = lo + bits.length - 1 ∧ whole = (regWidth reg == some bits.length) := by
    obtain ⟨bits, hor⟩ := unalias_origin h
    obtain ⟨hne, hhi, hw⟩ := originOf_sub hor
    have hpos : 0 < bits.length := List.length_pos_iff.2 hne
    exact ⟨bits, hor, by omega, hne, hhi, hw⟩
  obtain ⟨bits, hor, hlen, hne, hhi, hwhole⟩ := hshape
  obtain ⟨halias, width, hw, hl, hall⟩ := unalias_sound h
  have hloc : (Origin.sub reg hi lo whole).locations.length = hi - lo + 1 := by simp [Origin.locations]
  have hwidth : width = hi - lo + 1 := by omega
  subst hwidth
  have hget : ∀ index (hi' : index < hi - lo + 1), ∃ at', (Origin.sub reg hi lo whole).locations[index]? = some (reg, at') ∧
      at' = lo + index := by
    intro index hi'
    exact ⟨lo + index, by simp [Origin.locations, hi'], rfl⟩
  obtain ⟨base, at', hgetLast, hbasis, ⟨size, hsize, hrange⟩, _⟩ := hall (hi - lo) (by omega)
  obtain ⟨at'', hget', hat''⟩ := hget (hi - lo) (by omega)
  rw [hget'] at hgetLast
  simp only [Option.some.injEq, Prod.mk.injEq] at hgetLast
  obtain ⟨rfl, rfl⟩ := hgetLast
  refine ⟨halias, hbasis, by omega, hw, ⟨size, hsize, by omega⟩, ?_, fun value hm index hindex => ?_⟩
  · rw [hwhole, hlen]
    simp
  · obtain ⟨base', at₁, hget₁, _, _, hval⟩ := hall index (by omega)
    obtain ⟨at₂, hget₂, hat₂⟩ := hget index (by omega)
    rw [hget₂] at hget₁
    simp only [Option.some.injEq, Prod.mk.injEq] at hget₁
    obtain ⟨rfl, rfl⟩ := hget₁
    rw [← hat₂]
    exact hval value hm

/-- The registers of a `sup` or `set` are bits of the basis. -/
private theorem unalias_regs_basis {target : T} {var : RV} {origin : Origin} {regs : List RV}
    (h : target.unalias var = some origin) (hshape : origin = .sup regs ∨ origin = .set regs) {reg : RV}
    (hreg : reg ∈ regs) : target.isAlias reg = false := by
  obtain ⟨bits, hor⟩ := unalias_origin h
  obtain ⟨at', hat⟩ := (originOf_regs hor hshape).1 reg hreg
  rw [← originOf_locations hor] at hat
  obtain ⟨_, width, _, hl, hall⟩ := unalias_sound h
  obtain ⟨index, hindex, hget⟩ := List.getElem_of_mem hat
  obtain ⟨base, _, hb, hbasis, _⟩ := hall index (hl ▸ hindex)
  rw [List.getElem?_eq_getElem hindex, hget] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  rw [hb.1]
  exact hbasis

/-- A super-register is the concatenation of its registers, which are bit vector basis registers. -/
theorem unalias_sup_bits {target : T} {var : RV} {regs : List RV} (h : target.unalias var = some (.sup regs)) :
    (∀ reg ∈ regs, target.isAlias reg = false ∧ reg.sort.bits.isSome = true) ∧
      regWidth var = some (regs.reverse.flatMap wholeBits).length ∧
      ∀ value, Model target value → ∀ index bit, (regs.reverse.flatMap wholeBits)[index]? = some bit →
        value var index = value bit.1 bit.2 := by
  obtain ⟨_, width, hw, hl, hall⟩ := unalias_sound h
  obtain ⟨bits, hor⟩ := unalias_origin h
  simp only [Origin.locations] at hl hall
  subst hl
  refine ⟨fun reg hreg => ⟨unalias_regs_basis h (.inl rfl) hreg, (originOf_regs hor (.inl rfl)).2.1 rfl reg hreg⟩, hw,
    fun value hm index bit hbit => ?_⟩
  obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.1 hbit
  obtain ⟨base, at', hb, _, _, hval⟩ := hall index hindex
  rw [hbit] at hb
  rw [Option.some.inj hb]
  exact hval value hm

/-- A set of flags is the concatenation of its one-bit basis registers. -/
theorem unalias_set_bits {target : T} {var : RV} {bits : List RV} (h : target.unalias var = some (.set bits)) :
    (∀ reg ∈ bits, reg.sort = .bool ∧ target.isAlias reg = false) ∧ regWidth var = some bits.length ∧
      ∀ value, Model target value → ∀ index reg, bits.reverse[index]? = some reg → value var index = value reg 0 := by
  obtain ⟨_, width, hw, hl, hall⟩ := unalias_sound h
  obtain ⟨list, hor⟩ := unalias_origin h
  have hsorts := (originOf_regs hor (.inr rfl)).2.2 rfl
  have hwhole : ∀ reg ∈ bits.reverse, wholeBits reg = [(reg, 0)] := by
    intro reg hreg
    simp [wholeBits, regWidth, hsorts reg (by simpa using hreg)]
  have hlocs : (Origin.set bits).locations = bits.reverse.map (·, 0) := by
    simp only [Origin.locations]
    generalize bits.reverse = values at hwhole
    induction values with
    | nil => rfl
    | cons head tail ih =>
      simp only [List.mem_cons, forall_eq_or_imp] at hwhole
      simp [List.flatMap_cons, hwhole.1, ih hwhole.2]
  have hlength : (Origin.set bits).locations.length = bits.length := by simp [hlocs]
  have hwidth : width = bits.length := by omega
  subst hwidth
  refine ⟨fun reg hreg => ⟨hsorts reg hreg, unalias_regs_basis h (.inr rfl) hreg⟩, hw, fun value hm index reg hget => ?_⟩
  obtain ⟨hindex, _⟩ := List.getElem?_eq_some_iff.1 hget
  have hloc : (Origin.set bits).locations[index]? = some (reg, 0) := by rw [hlocs, List.getElem?_map, hget]; rfl
  obtain ⟨base, at', hb, _, _, hval⟩ := hall index (by simpa using hindex)
  rw [hloc] at hb
  simp only [Option.some.injEq, Prod.mk.injEq] at hb
  rw [hb.1, hb.2]
  exact hval value hm

/-- A basis register has no origin: origins do not go in circles. -/
theorem unalias_basis {target : T} {var : RV} (h : target.isAlias var = false) : target.unalias var = none := by
  simp [Target.unalias, h]

/-- Nothing has an origin without equations. -/
theorem unalias_no_aliases {target : T} (h : target.aliases = []) (var : RV) : target.unalias var = none := by
  cases hor : target.unalias var with
  | none => rfl
  | some origin =>
    exfalso
    obtain ⟨halias, width, _, hlen, _⟩ := unalias_sound hor
    have hlocated : ∀ {fuel seen index}, target.locate fuel seen var index = none := by
      intro fuel seen index
      cases fuel with
      | zero => rfl
      | succ fuel => simp [Target.locate, halias, Target.linked, h]
    unfold Target.unalias at hor
    simp only [halias, ↓reduceIte] at hor
    split at hor
    · rename_i size hsize
      obtain ⟨bits, hbits, hbind⟩ := Option.bind_eq_some_iff.1 hor
      obtain ⟨hl, hall⟩ := mapM_some hbits
      have hne := (List.length_pos_iff.2 (show bits ≠ [] by
        rintro rfl
        simp [originOf] at hbind))
      obtain ⟨_, _, hfound⟩ := hall 0 (by simp at hl ⊢; omega)
      rw [hlocated] at hfound
      cases hfound
    · cases hor

/-! ### Completeness on well-formed equations -/

/-- A path through the equations from a bit of an alias to a bit of a basis register. -/
inductive Chain (target : T) : RV × Nat → List (RV × Nat) → RV × Nat → Prop where
  | stop {base : RV} {at' size : Nat} (hbasis : target.isAlias base = false) (hsize : regWidth base = some size)
      (hrange : at' < size) : Chain target (base, at') [] (base, at')
  | link {bit next final : RV × Nat} {rest : List (RV × Nat)} (halias : target.isAlias bit.1 = true)
      (hlinked : next ∈ target.linked bit.1 bit.2) (hrest : Chain target next rest final) :
      Chain target bit (next :: rest) final

/-- The end of a chain is a bit of the basis and equal to its beginning. -/
theorem Chain.sound {target : T} {bit final : RV × Nat} {path : List (RV × Nat)} (h : Chain target bit path final)
    {value : RV → Nat → Bool} (hm : Model target value) : value bit.1 bit.2 = value final.1 final.2 := by
  induction h with
  | stop => rfl
  | link _ hlinked _ ih => exact (linked_sound hm hlinked).trans ih

theorem Chain.final {target : T} {bit final : RV × Nat} {path : List (RV × Nat)} (h : Chain target bit path final) :
    target.isAlias final.1 = false ∧ ∃ size, regWidth final.1 = some size ∧ final.2 < size := by
  induction h with
  | stop hbasis hsize hrange => exact ⟨hbasis, _, hsize, hrange⟩
  | link _ _ _ ih => exact ih

/-- The search finds something if there is a simple path that it is allowed to walk. -/
theorem locate_of_chain {target : T} {bit final : RV × Nat} {path : List (RV × Nat)} (h : Chain target bit path final)
    {fuel : Nat} {seen : List (RV × Nat)} (hfuel : path.length < fuel) (hnodup : (bit :: path).Nodup)
    (hseen : ∀ node ∈ bit :: path, node ∉ seen) : (target.locate fuel seen bit.1 bit.2).isSome = true := by
  induction h generalizing fuel seen with
  | stop hbasis hsize hrange =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel => simp [Target.locate, hbasis, hsize, hrange]
  | @link bit next final rest halias hlinked _ ih =>
    cases fuel with
    | zero => simp at hfuel
    | succ fuel =>
      simp only [List.nodup_cons, List.mem_cons, not_or] at hnodup
      simp only [Target.locate, halias, ↓reduceIte]
      rw [List.findSome?_isSome_iff]
      refine ⟨next, hlinked, ?_⟩
      have hfresh : next ∉ (bit.1, bit.2) :: seen := by
        simp only [List.mem_cons, not_or]
        exact ⟨hnodup.1.1 ∘ Eq.symm, hseen next (by simp)⟩
      simp only [hfresh, ↓reduceIte]
      refine ih (by simpa using hfuel) (by simpa using hnodup.2) ?_
      intro node hnode hin
      rcases List.mem_cons.1 hin with rfl | hin
      · rcases List.mem_cons.1 hnode with rfl | hnode
        · exact hnodup.1.1 rfl
        · exact hnodup.1.2 hnode
      · exact hseen node (List.mem_cons_of_mem _ hnode) hin

/-- The basis bits are independent: the equations do not constrain them. This is upstream's
well-formedness: each alias has a unique definition in terms of the basis. -/
def Free (target : T) : Prop :=
  ∀ basis : RV → Nat → Bool, ∃ value, Model target value ∧
    ∀ base, target.isAlias base = false → ∀ at' size, regWidth base = some size → at' < size →
      value base at' = basis base at'

/-- A map of each bit to a bit of the basis that respects the equations shows the basis independent. -/
theorem Free.of_resolution {target : T} (resolve : RV → Nat → RV × Nat)
    (hbasis : ∀ base, target.isAlias base = false → ∀ at' size, regWidth base = some size → at' < size →
      resolve base at' = (base, at'))
    (hequations : ∀ alias ∈ target.aliases, ∀ span ∈ alias.spans.getD [], ∀ index < span.width,
      resolve span.var index = resolve alias.target (span.offset + index)) : Free target := fun basis =>
  ⟨fun reg index => basis (resolve reg index).1 (resolve reg index).2,
    fun alias halias span hspan index hindex => by simp only [hequations alias halias span hspan index hindex],
    fun base hb at' size hsize hrange => by simp only [hbasis base hb at' size hsize hrange]⟩

/-- On independent basis bits the search can only find the end of any chain. -/
theorem locate_eq_of_chain {target : T} (hfree : Free target) {bit final : RV × Nat} {path : List (RV × Nat)}
    (h : Chain target bit path final) {fuel : Nat} {seen : List (RV × Nat)} {found : RV × Nat}
    (hfound : target.locate fuel seen bit.1 bit.2 = some found) : found = final := by
  obtain ⟨base, at'⟩ := found
  obtain ⟨hb, ⟨size, hsize, hrange⟩, hval⟩ := locate_sound hfound
  obtain ⟨hb', size', hsize', hrange'⟩ := h.final
  refine Classical.byContradiction fun hne => ?_
  obtain ⟨value, hm, hbasis⟩ := hfree fun reg index => decide ((reg, index) = final)
  have h₁ := hbasis _ hb _ _ hsize hrange
  have h₂ := hbasis _ hb' _ _ hsize' hrange'
  have h₃ := (hval value hm).symm.trans (h.sound hm)
  rw [h₁, h₂] at h₃
  simp [hne] at h₃

/-- Completeness for nested sub-registers: when the equations are well-formed and each bit of an
alias has a chain of definitions to the corresponding bit of a basis register, however long, then
`unalias` finds that range. -/
theorem unalias_sub_of_chains {target : T} (hfree : Free target) {var reg : RV} {width lo : Nat}
    (halias : target.isAlias var = true) (hwidth : regWidth var = some width) (hpos : 0 < width)
    (hchains : ∀ index < width, ∃ path, Chain target (var, index) path (reg, lo + index) ∧
      ((var, index) :: path).Nodup ∧ path.length < target.aliasFuel) :
    target.unalias var = some (.sub reg (lo + width - 1) lo (regWidth reg == some width)) := by
  have hlocate : ∀ index ∈ List.range width,
      target.locate target.aliasFuel [] var index = some (reg, lo + index) := by
    intro index hindex
    obtain ⟨path, hchain, hnodup, hfuel⟩ := hchains index (List.mem_range.1 hindex)
    have hsome := locate_of_chain (seen := []) hchain hfuel hnodup (by simp)
    obtain ⟨found, hfound⟩ := Option.isSome_iff_exists.1 hsome
    rw [hfound, locate_eq_of_chain hfree hchain hfound]
  have hmap := mapM_of_all (g := fun index => (reg, lo + index)) hlocate
  have hbits : (List.range width).map (fun index => (reg, lo + index)) =
      (reg, lo) :: ((List.range width).map fun index => (reg, lo + index)).tail := by
    cases width with
    | zero => omega
    | succ width => simp [List.range_succ_eq_map]
  have hlocs : (Origin.sub reg (lo + width - 1) lo (regWidth reg == some width)).locations =
      (List.range width).map fun index => (reg, lo + index) := by
    have : lo + width - 1 - lo + 1 = width := by omega
    simp [Origin.locations, this]
  have horigin : originOf ((List.range width).map fun index => (reg, lo + index)) =
      some (.sub reg (lo + width - 1) lo (regWidth reg == some width)) := by
    rw [hbits]
    simp only [originOf]
    rw [← hbits]
    simp only [List.length_map, List.length_range, hlocs, ↓reduceIte]
  simp only [Target.unalias, halias, ↓reduceIte, hwidth]
  rw [hmap]
  exact horigin

/-! ### Discharging `Free` and the fuel bound

`Free` has one checkable form, for any concrete table: following the equations from either side of each equation gets to
the same bit of the basis. And a chain that doesn't come back to a register fits in the fuel. -/

/-- The bit of the basis the search finds for a bit, or the bit itself. -/
def resolveBit (target : T) (reg : RV) (index : Nat) : RV × Nat :=
  (target.locate target.aliasFuel [] reg index).getD (reg, index)

/-- Both sides of each equation of a table find the same bit of the basis. -/
def Resolves (target : T) : Bool :=
  target.aliases.all fun alias => (alias.spans.getD []).all fun span =>
    (List.range span.width).all fun index =>
      resolveBit target span.var index == resolveBit target alias.target (span.offset + index)

theorem aliasFuel_pos (target : T) : 0 < target.aliasFuel := by
  simp [Target.aliasFuel]

/-- A table on which the search agrees with the equations leaves the basis free. -/
theorem free_of_resolves {target : T} (h : Resolves target = true) : Free target := by
  refine Free.of_resolution (resolveBit target) ?_ ?_
  · intro base hb at' size hsize hrange
    obtain ⟨fuel, hfuel⟩ : ∃ fuel, target.aliasFuel = fuel + 1 :=
      ⟨target.aliasFuel - 1, by have := aliasFuel_pos target; omega⟩
    simp only [resolveBit, hfuel, Target.locate, hb, Bool.false_eq_true, ↓reduceIte, hsize, Option.any_some,
      decide_eq_true_eq, hrange, Option.getD_some]
  · intro alias halias span hspan index hindex
    simp only [Resolves, List.all_eq_true, beq_iff_eq, List.mem_range] at h
    exact h alias halias span hspan index hindex

/-- Without aliases there is nothing to constrain the basis. -/
theorem free_of_no_aliases {target : T} (h : target.aliases = []) : Free target :=
  free_of_resolves (by simp [Resolves, h])

/-- The registers the equations mention. -/
def mentioned (target : T) : List RV :=
  target.aliases.flatMap fun alias => alias.target :: (alias.spans.getD []).map (·.var)

open_private Bap.Theory.Target Bap.Theory.layoutParts as layoutParts

private theorem layoutParts_length (hole : Nat) (parts : List AliasPart) {size : Nat} {spans : List AliasSpan}
    (h : layoutParts hole parts = some (size, spans)) : spans.length ≤ parts.length := by
  induction parts generalizing size spans with
  | nil =>
    simp only [layoutParts, Option.some.injEq, Prod.mk.injEq] at h
    simp [← h.2]
  | cons part rest ih =>
    unfold layoutParts at h
    cases hrest : layoutParts hole rest with
    | none => simp [hrest] at h
    | some inner =>
      obtain ⟨low, inner⟩ := inner
      have := ih hrest
      simp only [hrest, Option.bind_eq_bind, Option.bind_some] at h
      cases part with
      | unknown =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        simp only [List.length_cons, ← h.2]
        omega
      | reg var | bit var =>
        cases hw : regWidth var with
        | none => simp [hw] at h
        | some width =>
          simp only [hw, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at h
          simp only [List.length_cons, ← h.2]
          omega

private theorem spans_length (alias : Alias) : (alias.spans.getD []).length ≤ alias.parts.length := by
  unfold Alias.spans
  cases regWidth alias.target with
  | none => simp
  | some total =>
    simp only [Option.bind_eq_bind, Option.bind_some]
    cases layoutParts 0 alias.parts with
    | none => simp
    | some known =>
      simp only [Option.bind_some]
      cases hs : layoutParts (if alias.parts.countP (fun part => part == .unknown) = 0 then 0
          else (total - known.1) / alias.parts.countP fun part => part == .unknown) alias.parts with
      | none => simp
      | some laid =>
        obtain ⟨size, spans⟩ := laid
        simp only [Option.bind_some]
        split
        · exact layoutParts_length _ _ hs
        · simp

theorem length_mentioned (target : T) : (mentioned target).length < target.aliasFuel := by
  have key : ∀ aliases : List Alias, (aliases.flatMap fun alias => alias.target :: (alias.spans.getD []).map (·.var)).length ≤
      (aliases.map fun alias => alias.parts.length + 1).sum := by
    intro aliases
    induction aliases with
    | nil => simp
    | cons alias rest ih =>
      have := spans_length alias
      simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_map, List.map_cons, List.sum_cons]
      omega
  have := key target.aliases
  simp only [mentioned, Target.aliasFuel]
  omega

/-- The bits a bit is linked to are of registers the equations mention. -/
theorem linked_mentioned {target : T} {var other : RV} {index at' : Nat} (h : (other, at') ∈ target.linked var index) :
    other ∈ mentioned target := by
  simp only [Target.linked, List.mem_flatMap, List.mem_filterMap] at h
  obtain ⟨alias, halias, span, hspan, hif⟩ := h
  simp only [mentioned, List.mem_flatMap, List.mem_cons, List.mem_map]
  refine ⟨alias, halias, ?_⟩
  split at hif
  · simp only [Option.some.injEq, Prod.mk.injEq] at hif
    exact .inr ⟨span, hspan, hif.1⟩
  · split at hif
    · simp only [Option.some.injEq, Prod.mk.injEq] at hif
      exact .inl hif.1.symm
    · cases hif

private theorem length_le_of_subset {l m : List RV} (hl : l.Nodup) (hsub : ∀ x ∈ l, x ∈ m) : l.length ≤ m.length := by
  induction l generalizing m with
  | nil => simp
  | cons a t ih =>
    have ha := hsub a (by simp)
    have hsub' : ∀ x ∈ t, x ∈ m.erase a := fun x hx => by
      have hne : x ≠ a := fun he => (List.nodup_cons.mp hl).1 (he ▸ hx)
      exact (List.mem_erase_of_ne hne).mpr (hsub x (List.mem_cons_of_mem _ hx))
    have := ih (List.nodup_cons.mp hl).2 hsub'
    rw [List.length_erase_of_mem ha] at this
    have hpos : 0 < m.length := List.length_pos_of_mem ha
    simp only [List.length_cons]
    omega

/-- A chain that doesn't come back to a register fits in the fuel of the search. -/
theorem Chain.length_lt_aliasFuel {target : T} {bit final : RV × Nat} {path : List (RV × Nat)}
    (h : Chain target bit path final) (hregs : (path.map Prod.fst).Nodup) : path.length < target.aliasFuel := by
  have hsub : ∀ reg ∈ path.map Prod.fst, reg ∈ mentioned target := by
    clear hregs
    induction h with
    | stop => simp
    | link _ hlinked _ ih =>
      intro reg hreg
      rcases List.mem_cons.mp hreg with rfl | hreg
      · exact linked_mentioned hlinked
      · exact ih reg hreg
  have hlen := length_le_of_subset hregs hsub
  have := length_mentioned target
  simp only [List.length_map] at hlen
  omega

/-- **Completeness for nested sub-registers, on a table that resolves**: `Free` and the fuel bound of
`unalias_sub_of_chains` hold when the table passes the check and the chains don't come back to a register. -/
theorem unalias_sub_of_resolving_chains {target : T} (hresolves : Resolves target = true) {var reg : RV} {width lo : Nat}
    (halias : target.isAlias var = true) (hwidth : regWidth var = some width) (hpos : 0 < width)
    (hchains : ∀ index < width, ∃ path, Chain target (var, index) path (reg, lo + index) ∧
      (((var, index) :: path).map Prod.fst).Nodup) :
    target.unalias var = some (.sub reg (lo + width - 1) lo (regWidth reg == some width)) := by
  refine unalias_sub_of_chains (free_of_resolves hresolves) halias hwidth hpos fun index hindex => ?_
  obtain ⟨path, hchain, hnodup⟩ := hchains index hindex
  have hpath : (path.map Prod.fst).Nodup := by
    simp only [List.map_cons] at hnodup
    exact (List.nodup_cons.mp hnodup).2
  refine ⟨path, hchain, ?_, hchain.length_lt_aliasFuel hpath⟩
  exact (List.pairwise_map.mp hnodup).imp fun hne he => hne (congrArg Prod.fst he)

/-! The x86 general registers. No target of this port declares a table of aliases: the semantics of the lifters know the
sub-registers themselves, see `x86_low_half_aliases` of `Bap.Proofs.Target`. So this is the table of the upstream's
documentation of `Origin`, of RAX, as a concrete instance of the above. -/

namespace X86Table

private def reg (name : String) (width : Nat) : RV := ⟨name, .bitv width, 0, false, false⟩

def rax := reg "RAX" 64
def upper := reg "UPPER" 32
def eax := reg "EAX" 32
def ax := reg "AX" 16
def ah := reg "AH" 8
def al := reg "AL" 8

def table : T := declare {
  name := "x86-rax"
  regs := some [([.general], [rax]), ([.alias], [upper, eax, ax, ah, al])]
  aliases := some [⟨rax, [.reg upper, .reg eax]⟩, ⟨eax, [.unknown, .reg ax]⟩, ⟨ax, [.reg ah, .reg al]⟩]
}

theorem table_resolves : Resolves table = true := by decide +kernel

theorem table_free : Free table := free_of_resolves table_resolves

theorem unalias_eax : table.unalias eax = some (.sub rax 31 0 false) := by decide +kernel
theorem unalias_upper : table.unalias upper = some (.sub rax 63 32 false) := by decide +kernel
theorem unalias_ax : table.unalias ax = some (.sub rax 15 0 false) := by decide +kernel
theorem unalias_ah : table.unalias ah = some (.sub rax 15 8 false) := by decide +kernel
theorem unalias_al : table.unalias al = some (.sub rax 7 0 false) := by decide +kernel
theorem unalias_rax : table.unalias rax = none := by decide +kernel

end X86Table

end TargetLaws

end Bap.Proofs.Theory
