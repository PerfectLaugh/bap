import Std

namespace Bap

inductive Endian where
  | little
  | big
  deriving DecidableEq, Repr

inductive Typ where
  | unknown
  | unit
  | mem (addressWidth valueWidth : Nat)
  | imm (width : Nat)
  deriving DecidableEq, Repr

structure Var where
  name : String
  typ : Typ
  index : Nat := 0
  isVirtual : Bool := false
  deriving DecidableEq, Repr

/-- Whether two variables are the same, by what is cheap first: most are not, and lookups compare them one by one. -/
def Var.decEqFast (left right : Var) : Decidable (left = right) :=
  match left, right with
  | ⟨name, typ, index, isVirtual⟩, ⟨name', typ', index', isVirtual'⟩ =>
    if hi : index = index' then
      if hv : isVirtual = isVirtual' then
        if hn : name = name' then
          if ht : typ = typ' then isTrue (by subst hi hv hn ht; rfl)
          else isFalse (fun h => ht (Var.mk.inj h).2.1)
        else isFalse (fun h => hn (Var.mk.inj h).1)
      else isFalse (fun h => hv (Var.mk.inj h).2.2.2)
    else isFalse (fun h => hi (Var.mk.inj h).2.2.1)

@[csimp] theorem Var.decEq_eq_fast : @instDecidableEqVar = @Var.decEqFast := by
  funext left right
  exact Subsingleton.elim _ _

instance : Hashable Var where
  hash var := mixHash (hash var.name) (hash var.index)

namespace Var

def base (var : Var) : Var := { var with index := 0 }
def version (var : Var) (index : Nat) : Var := { var with index := index }

end Var
end Bap
