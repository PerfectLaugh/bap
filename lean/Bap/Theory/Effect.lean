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
  deriving DecidableEq, Repr

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

end EffectSort

structure Value where
  sort : EffectSort
  deriving DecidableEq, Repr

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
