import Bap.Core.Word
import Bap.Core.Memory

namespace Bap.Theory

inductive ValueSort where
  | top
  | bool
  | bitv (width : Nat)
  | mem (addressWidth valueWidth : Nat)
  | float (exponentWidth significandWidth : Nat)
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

end ValueSort

structure Var where
  name : String
  sort : ValueSort
  index : Nat := 0
  isVirtual : Bool := false
  deriving DecidableEq, Repr

namespace Var

def base (var : Var) : Var := { var with index := 0 }
def version (var : Var) (index : Nat) : Var := { var with index := index }
def isMutable (var : Var) : Bool := !var.isVirtual

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
