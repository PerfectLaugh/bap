import Bap.Symbolic.Expr

namespace Bap.FFI.Z3

@[extern "bap_z3_check_sat"]
opaque checkSat (script : @& String) : IO Bool

def isSat (constraints : List Symbolic.Expr) : IO Bool :=
  checkSat (Symbolic.renderScript constraints)

def isUnsat (constraints : List Symbolic.Expr) : IO Bool := do
  return !(← isSat constraints)

@[extern "bap_z3_check_within"]
opaque checkWithin (script : @& String) (millis : UInt32) : IO UInt8

/-- Whether some input meets the conditions, of what Z3 says within `millis` milliseconds: nothing of what it doesn't say by
then, as of a product that is to be a prime. -/
def isSatWithin (constraints : List Symbolic.Expr) (millis : Nat) : IO (Option Bool) := do
  match ← checkWithin (Symbolic.renderScript constraints) (UInt32.ofNat (min millis (2 ^ 31))) with
  | 0 => pure (some false)
  | 1 => pure (some true)
  | _ => pure none

end Bap.FFI.Z3
