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

namespace Var

def base (var : Var) : Var := { var with index := 0 }
def version (var : Var) (index : Nat) : Var := { var with index := index }

end Var
end Bap
