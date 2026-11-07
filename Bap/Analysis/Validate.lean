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

/-- Whether two outcomes are of one kind: both go on, both jump, wherever to, or both raise the same special or exception. -/
private def effectKindEq : Bil.Effect → Bil.Effect → Bool
  | .normal, .normal => true
  | .jump _, .jump _ => true
  | .special left, .special right => left = right
  | .cpuExn left, .cpuExn right => left = right
  | _, _ => false

/-- Whether two outcomes go on at the same place: a jump to the same target on both sides, or a jump on neither. -/
private def targetEq : Bil.Effect → Bil.Effect → Bool
  | @Bil.Effect.jump leftWidth left, @Bil.Effect.jump rightWidth right =>
    leftWidth = rightWidth && left.toNat = right.toNat
  | .jump _, _ => false
  | _, .jump _ => false
  | _, _ => true

/-- Whether two values read the same bytes from `first` up to `last`, where they are memories, and are equal where they aren't. -/
private def bytesEqual (first last : Nat) : Value → Value → Bool
  | @Value.memory leftWidth left, @Value.memory rightWidth right =>
    leftWidth == rightWidth && (List.range (last - first)).all fun offset =>
      Memory.readByte left (BitVec.ofNat leftWidth (first + offset)) ==
        Memory.readByte right (BitVec.ofNat rightWidth (first + offset))
  | left, right => valueEq left right

private def memoryVars (state : Bil.State) : List Bap.Var :=
  (state.env.filter fun binding => binding.1.typ matches .mem _ _).map Prod.fst |>.eraseDups

/-- Whether each memory of either side reads the same bytes in each range `[first, last)` that what comes next consumes. -/
private def rangesEqual (ranges : List (Nat × Nat)) (left right : Bil.State) : Bool :=
  ranges.all fun (first, last) => (memoryVars left ++ memoryVars right).eraseDups.all fun var =>
    match Bil.lookup left.env var, Bil.lookup right.env var with
    | .ok left, .ok right => bytesEqual first last left right
    | .error _, .error _ => true
    | _, _ => false

/-- Runs both programs from `initial` and says what of them agrees: the kind of their outcome (`effects`), the registers given and
every memory, and where they go on (`continuation`): the target of a jump, and the bytes of the ranges `[first, last)` that what comes
next consumes, which a difference of memory elsewhere doesn't touch. -/
def compare (registers : List Bap.Var) (original simplified : Bil.Program)
    (initial : Bil.State := {}) (fuel : Nat := 100000) (continuationRanges : List (Nat × Nat) := []) :
    Except String Result := do
  let (originalState, originalEffect) ← Bil.run original initial fuel
  let (simplifiedState, simplifiedEffect) ← Bil.run simplified initial fuel
  let registers := registers ++ memoryVars originalState ++ memoryVars simplifiedState |>.eraseDups
  .ok {
    effects := effectKindEq originalEffect simplifiedEffect
    registers := registers.all fun var => lookupEqual var originalState.env simplifiedState.env
    memory := (memoryVars originalState ++ memoryVars simplifiedState).eraseDups.all fun var =>
      lookupEqual var originalState.env simplifiedState.env
    continuation := targetEq originalEffect simplifiedEffect && rangesEqual continuationRanges originalState simplifiedState
  }

def ok (result : Result) : Bool := result.effects && result.registers && result.memory && result.continuation

end Bap.Analysis.Validate
