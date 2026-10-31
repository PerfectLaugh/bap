import Bap.Bil.Eval

namespace Bap.Analysis.Validate

structure Result where
  effects : Bool
  registers : Bool
  memory : Bool
  continuation : Bool
  deriving Repr

/-- Equal contents: every address either side holds reads the same byte from both. -/
private def memoryEqual (left right : Memory width) : Bool :=
  (Memory.cells left ++ Memory.cells right).all fun cell =>
    Memory.readByte left cell.1 == Memory.readByte right cell.1

private def valueEq : Value → Value → Bool
  | @Value.bits leftWidth left, @Value.bits rightWidth right =>
    leftWidth = rightWidth && left.toNat = right.toNat
  | @Value.memory leftWidth left, @Value.memory rightWidth right =>
    if h : leftWidth = rightWidth then
      let right : Memory leftWidth := h ▸ right
      memoryEqual left right
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
