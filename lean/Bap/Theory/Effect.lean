import Std

namespace Bap.Theory.Effect

inductive Kind where
  | data
  | ctrl
  deriving DecidableEq, Repr

inductive Atom where
  | named (kind : Kind) (name : String)
  deriving DecidableEq, Repr

inductive EffectSort where
  | bot
  | top
  | atom (value : Atom)
  | both (left right : EffectSort)
  deriving Repr

inductive PartialOrder where
  | less
  | equal
  | greater
  | unordered
  deriving DecidableEq, Repr

namespace EffectSort

def data (name : String) : EffectSort := .atom (.named .data name)
def ctrl (name : String) : EffectSort := .atom (.named .ctrl name)
def union (sorts : List EffectSort) : EffectSort := sorts.foldl both .bot
def join (left right : List EffectSort) : EffectSort := both (union left) (union right)

/-- Whether a sort denotes the set of all effects: `top` absorbs under `both`, as in upstream's
`both`, so a `both` that mentions `top` anywhere is `top`. -/
def isTop : EffectSort → Bool
  | .top => true
  | .both left right => isTop left || isTop right
  | _ => false

/-- The named effects of a sort. This is the sort's denotation unless it `isTop`. -/
def atoms : EffectSort → List Atom
  | .bot | .top => []
  | .atom value => [value]
  | .both left right => (atoms left ++ atoms right).eraseDups

private def subset (left right : List Atom) : Bool := left.all fun atom => atom ∈ right

def order (left right : EffectSort) : PartialOrder :=
  match left.isTop, right.isTop with
  | true, true => .equal
  | true, false => .greater
  | false, true => .less
  | false, false =>
    let left := left.atoms
    let right := right.atoms
    if subset left right then
      if subset right left then .equal else .less
    else if subset right left then .greater
    else .unordered

private theorem order_equal_iff (left right : EffectSort) :
    order left right = .equal ↔ left.isTop = right.isTop ∧ (left.isTop = false → ∀ atom, atom ∈ left.atoms ↔ atom ∈ right.atoms) := by
  cases hl : left.isTop <;> cases hr : right.isTop <;> simp only [order, hl, hr, reduceCtorEq, Bool.false_eq_true, Bool.true_eq_false, false_and, true_and, false_implies]
  have key : (∀ atom, atom ∈ left.atoms ↔ atom ∈ right.atoms) ↔ subset left.atoms right.atoms = true ∧ subset right.atoms left.atoms = true := by
    simp only [subset, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h => ⟨fun atom ha => (h atom).1 ha, fun atom ha => (h atom).2 ha⟩, fun h atom => ⟨h.1 atom, h.2 atom⟩⟩
  simp only [forall_const, key]
  cases subset left.atoms right.atoms <;> cases subset right.atoms left.atoms <;> simp

instance setoid : Setoid EffectSort where
  r left right := order left right = .equal
  iseqv := {
    refl := fun sort => (order_equal_iff sort sort).2 ⟨rfl, fun _ _ => Iff.rfl⟩
    symm := fun h =>
      have h := (order_equal_iff _ _).1 h
      (order_equal_iff _ _).2 ⟨h.1.symm, fun hr atom => (h.2 (h.1.trans hr) atom).symm⟩
    trans := fun h₁ h₂ =>
      have h₁ := (order_equal_iff _ _).1 h₁
      have h₂ := (order_equal_iff _ _).1 h₂
      (order_equal_iff _ _).2 ⟨h₁.1.trans h₂.1, fun hl atom =>
        (h₁.2 hl atom).trans (h₂.2 (h₁.1.symm.trans hl) atom)⟩ }

instance (left right : EffectSort) : Decidable (left ≈ right) :=
  inferInstanceAs (Decidable (order left right = .equal))

private theorem isTop_both_eq (left right : EffectSort) : (both left right).isTop = (left.isTop || right.isTop) := rfl

private theorem mem_atoms_both (atom : Atom) (left right : EffectSort) :
    atom ∈ (both left right).atoms ↔ atom ∈ left.atoms ∨ atom ∈ right.atoms := by
  simp [atoms, List.mem_eraseDups]

private theorem order_sound {a b a' b' : EffectSort} (ha : a ≈ a') (hb : b ≈ b') : order a b = order a' b' := by
  have ha := (order_equal_iff _ _).1 ha
  have hb := (order_equal_iff _ _).1 hb
  have subset_congr {x y x' y' : List Atom} (hx : ∀ atom, atom ∈ x ↔ atom ∈ x') (hy : ∀ atom, atom ∈ y ↔ atom ∈ y') :
      subset x y = subset x' y' := by
    refine Bool.eq_iff_iff.2 ?_
    simp only [subset, List.all_eq_true, decide_eq_true_eq]
    exact ⟨fun h atom hm => (hy atom).1 (h atom ((hx atom).2 hm)), fun h atom hm => (hy atom).2 (h atom ((hx atom).1 hm))⟩
  unfold order
  rw [← ha.1, ← hb.1]
  cases hl : a.isTop <;> cases hr : b.isTop <;> try rfl
  simp only
  rw [subset_congr (ha.2 hl) (hb.2 hr), subset_congr (hb.2 hr) (ha.2 hl)]

private theorem both_sound {a b a' b' : EffectSort} (ha : a ≈ a') (hb : b ≈ b') : both a b ≈ both a' b' := by
  have ha := (order_equal_iff _ _).1 ha
  have hb := (order_equal_iff _ _).1 hb
  refine (order_equal_iff _ _).2 ⟨by simp only [isTop_both_eq, ha.1, hb.1], fun h atom => ?_⟩
  simp only [isTop_both_eq, Bool.or_eq_false_iff] at h
  rw [mem_atoms_both, mem_atoms_both, ha.2 h.1, hb.2 h.2]

end EffectSort

/-- A sort of effects as what it denotes: a set of named effects, or all of them. Upstream's `Sort` is a `Set` of names, so that
two sorts of the same effects are equal however they were put together: `Effects.both_comm` says so of `=` here. -/
def Effects := Quotient EffectSort.setoid

namespace Effects

instance : DecidableEq Effects := inferInstanceAs (DecidableEq (Quotient EffectSort.setoid))

def ofSort (sort : EffectSort) : Effects := Quotient.mk _ sort

def both : Effects → Effects → Effects :=
  Quotient.lift₂ (fun left right => ofSort (EffectSort.both left right))
    fun _ _ _ _ ha hb => Quotient.sound (EffectSort.both_sound ha hb)

def order : Effects → Effects → PartialOrder :=
  Quotient.lift₂ EffectSort.order fun _ _ _ _ ha hb => EffectSort.order_sound ha hb

end Effects

structure Value where
  sort : Effects
  deriving DecidableEq

def rreg : EffectSort := .data "rreg"
def wreg : EffectSort := .data "wreg"
def rmem : EffectSort := .data "rmem"
def wmem : EffectSort := .data "wmem"
def barr : EffectSort := .data "barr"
def fall : EffectSort := .ctrl "fall"
def jump : EffectSort := .ctrl "jump"
def cjmp : EffectSort := .ctrl "cjmp"

theorem order_bot_ne (sort : EffectSort) (h : sort.isTop = true ∨ sort.atoms ≠ []) :
    EffectSort.order .bot sort = .less := by
  cases htop : sort.isTop with
  | true => simp [EffectSort.order, EffectSort.isTop, htop]
  | false =>
    have hne : sort.atoms ≠ [] := by simpa [htop] using h
    cases hatoms : sort.atoms with
    | nil => exact absurd hatoms hne
    | cons head tail =>
      simp [EffectSort.order, EffectSort.isTop, EffectSort.atoms, EffectSort.subset, htop, hatoms]

end Bap.Theory.Effect
