import Bap.Symbolic.Expr

namespace Bap.FFI.Z3

@[extern "bap_z3_check_sat"]
opaque checkSat (script : String) : IO Bool

def isSat (constraints : List Symbolic.Expr) : IO Bool :=
  checkSat (Symbolic.renderScript constraints)

def isUnsat (constraints : List Symbolic.Expr) : IO Bool := do
  return !(← isSat constraints)

end Bap.FFI.Z3
