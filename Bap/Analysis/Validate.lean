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

/-- What a disagreement of a comparison is, so that a real one stands out. -/
inductive Diagnosis where
  /-- A run read a variable that the initial state doesn't give, on the side named: until it does, the comparison says nothing. -/
  | unresolvedInput (side : String) (name : String)
  /-- What comes next would consume a byte that the memory has on neither side, as of code or data that wasn't captured. -/
  | missingBytes (memory : String) (address : Nat)
  /-- A byte that the original stored and the simplified left as it was, outside what comes next consumes: a store taken as dead. -/
  | deadStore (memory : String) (address : Nat)
  | mismatch (what : String)
  deriving DecidableEq, Repr

/-- Whether a memory has the byte at an address at all, which a write gives the page of. -/
private def holds (memory : Memory width) (address : Nat) : Bool :=
  memory.pages.contains (address / Memory.pageSize)

private def memoryOf (state : Bil.State) (var : Bap.Var) : Option (Σ width, Memory width) :=
  match Bil.lookup state.env var with
  | .ok (@Value.memory width memory) => some ⟨width, memory⟩
  | _ => none

/-- `compare`, as what each disagreement is: of input that a run needed and wasn't given, of bytes that what comes next consumes and
neither side has, of a store that the simplified dropped, or a real mismatch. Nothing is what `ok` of `compare` is. -/
def diagnose (registers : List Bap.Var) (original simplified : Bil.Program)
    (initial : Bil.State := {}) (fuel : Nat := 100000) (continuationRanges : List (Nat × Nat) := []) :
    Except String (List Diagnosis) := do
  let unbound := "unbound variable "
  -- A run, or the input that it needed and wasn't given.
  let run (side : String) (program : Bil.Program) : Except String (Except Diagnosis (Bil.State × Bil.Effect)) :=
    match Bil.run program initial fuel with
    | .ok result => .ok (.ok result)
    | .error message =>
      if message.startsWith unbound then .ok (.error (.unresolvedInput side (message.drop unbound.length).toString))
      else .error s!"{side}: {message}"
  let (originalState, originalEffect, simplifiedState, simplifiedEffect) ←
    match ← run "original" original, ← run "simplified" simplified with
    | .ok (originalState, originalEffect), .ok (simplifiedState, simplifiedEffect) =>
      pure (originalState, originalEffect, simplifiedState, simplifiedEffect)
    | left, right => return [left, right].filterMap fun | .error diagnosis => some diagnosis | .ok _ => none
  let inRanges (address : Nat) := continuationRanges.any fun (first, last) => first ≤ address && address < last
  let mut found : Array Diagnosis := #[]
  if !effectKindEq originalEffect simplifiedEffect then
    found := found.push (.mismatch s!"the original ends {repr originalEffect} and the simplified {repr simplifiedEffect}")
  else if !targetEq originalEffect simplifiedEffect then
    found := found.push (.mismatch s!"the original goes on at {repr originalEffect} and the simplified at {repr simplifiedEffect}")
  for var in registers.eraseDups do
    if !(var.typ matches .mem _ _) && !lookupEqual var originalState.env simplifiedState.env then
      found := found.push (.mismatch s!"{var.name} differs")
  for var in (memoryVars originalState ++ memoryVars simplifiedState).eraseDups do
    match memoryOf originalState var, memoryOf simplifiedState var with
    | some ⟨width, left⟩, some ⟨rightWidth, right⟩ =>
      if h : rightWidth = width then
        let right : Memory width := h ▸ right
        let before : Option (Memory width) := match memoryOf initial var with
          | some ⟨initialWidth, memory⟩ => if h : initialWidth = width then some (h ▸ memory) else none
          | none => none
        let readBefore (address : BitVec width) : UInt8 := (before.map (Memory.readByte · address)).getD 0
        let addresses := ((Memory.cells left ++ Memory.cells right).map (·.1)).eraseDups
        for address in addresses do
          let leftByte := Memory.readByte left address
          let rightByte := Memory.readByte right address
          if leftByte != rightByte then
            if !inRanges address.toNat && rightByte == readBefore address && leftByte != readBefore address then
              found := found.push (.deadStore var.name address.toNat)
            else
              found := found.push (.mismatch s!"{var.name} at {address.toNat} holds {leftByte} and not {rightByte}")
        for (first, last) in continuationRanges do
          for offset in List.range (last - first) do
            let address := first + offset
            if !holds left address && !holds right address then found := found.push (.missingBytes var.name address)
      else found := found.push (.mismatch s!"{var.name} is of {width} bits and of {rightWidth}")
    | _, _ => found := found.push (.mismatch s!"{var.name} is a memory on one side only")
  pure found.toList

end Bap.Analysis.Validate
