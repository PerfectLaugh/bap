import Bap.Core.Word
import Bap.Core.Memory

namespace Bap.Theory

inductive ValueSort where
  | top
  | bool
  | bitv (width : Nat)
  | mem (addressWidth valueWidth : Nat)
  /-- The format of a floating point number, as `Float.Format` upstream: its representation, here the parameters of
  `Bap.Theory.IEEE754` that tell formats apart (a decimal format and a binary format can have the same widths), and its
  bits in storage (an 80-bit format has an explicit integer bit, and pads to 96 or 128 where it is kept). -/
  | float (base exponentWidth significandWidth storage : Nat)
  | rmode
  | sym (name : String)
  | app (argument result : ValueSort)
  deriving DecidableEq, Repr

namespace ValueSort

def refine (expected actual : ValueSort) : Option ValueSort :=
  if expected = actual then some actual else none

def same (left right : ValueSort) : Bool := left == right

def bits : ValueSort → Option Nat
  | .bitv width => some width
  | _ => none

/-- The bits that a value of the sort takes, which for a float are not those of its parameters. -/
def storage : ValueSort → Option Nat
  | .bitv width => some width
  | .float _ _ _ storage => some storage
  | _ => none

end ValueSort

structure Var where
  name : String
  sort : ValueSort
  index : Nat := 0
  isVirtual : Bool := false
  /-- Bound by a scope, as upstream's `Var.scoped`: virtual, immutable and never versioned. -/
  isLet : Bool := false
  deriving DecidableEq, Repr

namespace Var

def base (var : Var) : Var := { var with index := 0 }

/-- Whether two variables are the same register, whatever sorts they were given: upstream's `Var.Top` compares the
`Ident` of a variable alone (`bap_core_theory_var.ml`, `Comparable.Inherit (Ident)`, whose component is `snd`), so that a set of
registers has one element for a name and version. -/
def sameReg (left right : Var) : Bool :=
  left.name == right.name && left.index == right.index && left.isVirtual == right.isVirtual && left.isLet == right.isLet

def version (var : Var) (index : Nat) : Var := if var.isLet then var else { var with index := index }
def isMutable (var : Var) : Bool := !var.isLet

end Var

inductive Value where
  | empty (sort : ValueSort)
  | bool (value : Bool)
  | bits {width : Nat} (value : BitVec width)
  | memory {addressWidth : Nat} (valueWidth : Nat) (memory : Memory addressWidth)
  | unknown (sort : ValueSort)

namespace Value

def sort : Value → ValueSort
  | .empty sort | .unknown sort => sort
  | .bool _ => .bool
  | @Value.bits width _ => .bitv width
  | @Value.memory addressWidth valueWidth _ => .mem addressWidth valueWidth

def forget (value : Value) : ValueSort := value.sort

def resort (expected : ValueSort) (value : Value) : Option Value :=
  if value.sort = expected then some value else none

@[simp] theorem resort_same (value : Value) : resort value.sort value = some value := by
  simp [resort]

end Value
end Bap.Theory
