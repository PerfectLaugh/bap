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

/-- The name of a variable, with a key of it that two names that differ almost never share, so that most comparisons of variables,
which a lookup in an environment makes one after another, are of one number. It is made from a `String`, which it is wherever one is
wanted. -/
structure VarName where
  private mk ::
  str : String
  key : UInt64
  key_eq : key = hash str

namespace VarName

def ofString (str : String) : VarName := ⟨str, hash str, rfl⟩

instance : Coe String VarName := ⟨ofString⟩
instance : Coe VarName String := ⟨str⟩
instance : ToString VarName := ⟨str⟩
instance : Repr VarName := ⟨fun name precedence => reprPrec name.str precedence⟩
instance : Inhabited VarName := ⟨ofString ""⟩

theorem ext_str {left right : VarName} (h : left.str = right.str) : left = right := by
  cases left; cases right
  simp only at h
  subst h
  simp_all

/-- Names are the same when their strings are, which is what proofs see. -/
instance decEq : DecidableEq VarName := fun left right =>
  if h : left.str = right.str then isTrue (ext_str h) else isFalse fun e => h (e ▸ rfl)

/-- `decEq`, by the keys first: names whose keys differ differ. -/
def decEqFast (left right : VarName) : Decidable (left = right) :=
  if hk : left.key = right.key then
    if h : left.str = right.str then isTrue (ext_str h) else isFalse fun e => h (e ▸ rfl)
  else isFalse fun e => hk (e ▸ rfl)

@[csimp] theorem decEq_eq_fast : @decEq = @decEqFast := by
  funext left right
  exact Subsingleton.elim _ _

instance : Hashable VarName := ⟨key⟩

@[simp] theorem str_ofString (str : String) : (ofString str).str = str := rfl

@[simp] theorem ofString_str (name : VarName) : ofString name.str = name := ext_str rfl

theorem str_injective : Function.Injective str := fun _ _ => ext_str

@[simp] theorem str_inj {left right : VarName} : left.str = right.str ↔ left = right := ⟨ext_str, (· ▸ rfl)⟩

@[simp] theorem ofString_inj {left right : String} : ofString left = ofString right ↔ left = right :=
  ⟨fun h => by simpa using congrArg str h, (· ▸ rfl)⟩

end VarName

structure Var where
  name : VarName
  typ : Typ
  index : Nat := 0
  isVirtual : Bool := false
  deriving DecidableEq, Repr

/-- Whether two variables are the same, by what is cheap first, the keys of their names: most are not, and lookups compare them one
by one. -/
def Var.decEqFast (left right : Var) : Decidable (left = right) :=
  match left, right with
  | ⟨name, typ, index, isVirtual⟩, ⟨name', typ', index', isVirtual'⟩ =>
    if hk : name.key = name'.key then
      if hi : index = index' then
        if hv : isVirtual = isVirtual' then
          if hn : name.str = name'.str then
            if ht : typ = typ' then isTrue (by have := VarName.ext_str hn; subst hi hv this ht; rfl)
            else isFalse (fun h => ht (Var.mk.inj h).2.1)
          else isFalse (fun h => hn (congrArg VarName.str (Var.mk.inj h).1))
        else isFalse (fun h => hv (Var.mk.inj h).2.2.2)
      else isFalse (fun h => hi (Var.mk.inj h).2.2.1)
    else isFalse (fun h => hk (congrArg VarName.key (Var.mk.inj h).1))

@[csimp] theorem Var.decEq_eq_fast : @instDecidableEqVar = @Var.decEqFast := by
  funext left right
  exact Subsingleton.elim _ _

instance : Hashable Var where
  hash var := mixHash var.name.key (hash var.index)

namespace Var

def base (var : Var) : Var := { var with index := 0 }
def version (var : Var) (index : Nat) : Var := { var with index := index }

end Var
end Bap
