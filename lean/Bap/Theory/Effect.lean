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

def atoms : EffectSort → List Atom
  | .bot | .top => []
  | .atom value => [value]
  | .both left right => (atoms left ++ atoms right).eraseDups

private def subset (left right : List Atom) : Bool := left.all fun atom => atom ∈ right

def order (left right : EffectSort) : PartialOrder :=
  if left = right then
    .equal
  else
    match left, right with
    | .bot, _ => .less
    | _, .top => .less
    | .top, _ => .greater
    | _, .bot => .greater
    | _, _ =>
      let left := left.atoms
      let right := right.atoms
      if left = right then .equal
      else if subset left right then .less
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

@[simp] theorem order_bot_ne (sort : EffectSort) (h : sort ≠ .bot) :
    EffectSort.order .bot sort = .less := by
  cases sort <;> simp_all [EffectSort.order]

end Bap.Theory.Effect
