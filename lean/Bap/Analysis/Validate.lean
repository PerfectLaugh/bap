import Bap.Bil.Eval

namespace Bap.Analysis.Validate

structure Result where
  effects : Bool
  registers : Bool
  memory : Bool
  continuation : Bool
  deriving Repr

private def cellsEqual (left right : List (BitVec width × UInt8)) : Bool :=
  left.length = right.length && left.all fun cell =>
    (right.find? fun other => other.1 == cell.1).map (fun other => other.2 == cell.2) |>.getD false

private def valueEq : Value → Value → Bool
  | @Value.bits leftWidth left, @Value.bits rightWidth right =>
    leftWidth = rightWidth && left.toNat = right.toNat
  | @Value.memory leftWidth left, @Value.memory rightWidth right =>
    if h : leftWidth = rightWidth then
      let right : Memory leftWidth := h ▸ right
      cellsEqual left.cells right.cells
    else
      false
  | .undefined, .undefined => true
  | _, _ => false

private def lookupEqual (var : Bap.Var) (left right : Bil.Env) : Bool :=
  match Bil.lookup left var, Bil.lookup right var with
  | .ok left, .ok right => valueEq left right
  | .error _, .error _ => true
  | _, _ => false

private def effectEq : Bil.Effect → Bil.Effect → Bool
  | .normal, .normal => true
  | @Bil.Effect.jump leftWidth left, @Bil.Effect.jump rightWidth right =>
    leftWidth = rightWidth && left.toNat = right.toNat
  | .special left, .special right => left = right
  | .cpuExn left, .cpuExn right => left = right
  | _, _ => false

private def memoryVars (state : Bil.State) : List Bap.Var :=
  (state.env.filter fun binding => binding.1.typ matches .mem _ _).map Prod.fst |>.eraseDups

def compare (registers : List Bap.Var) (original simplified : Bil.Program)
    (initial : Bil.State := {}) (fuel : Nat := 100000) : Except String Result := do
  let (originalState, originalEffect) ← Bil.run original initial fuel
  let (simplifiedState, simplifiedEffect) ← Bil.run simplified initial fuel
  let registers := registers ++ memoryVars originalState ++ memoryVars simplifiedState |>.eraseDups
  .ok {
    effects := effectEq originalEffect simplifiedEffect
    registers := registers.all fun var => lookupEqual var originalState.env simplifiedState.env
    memory := (memoryVars originalState ++ memoryVars simplifiedState).eraseDups.all fun var =>
      lookupEqual var originalState.env simplifiedState.env
    continuation := effectEq originalEffect simplifiedEffect
  }

def ok (result : Result) : Bool := result.effects && result.registers && result.memory && result.continuation

end Bap.Analysis.Validate
