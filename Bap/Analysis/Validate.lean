import Bap.Bil.Eval
import Bap.Bil.Transform

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
  /-- A run that failed, on the side named, may read a variable before anything gives it, on some way through it: neither the initial
  state nor the program before it on that way. Until it is given, the comparison says nothing. -/
  | unresolvedInput (side : String) (name : String)
  /-- A run that failed, on the side named, with what it said. -/
  | failed (side : String) (message : String)
  /-- What comes next would consume a byte that the memory has on neither side, as of code or data that wasn't captured. -/
  | missingBytes (memory : String) (address : Nat)
  /-- A byte that the original stored and the simplified left as it was, outside what comes next consumes and the memory that is said
  to be live after: a store that is dead. -/
  | deadStore (memory : String) (address : Nat)
  /-- A byte that the original stored and the simplified left as it was, outside what comes next consumes, where nothing says what
  memory is live after: whether the store was dead isn't known. -/
  | droppedStore (memory : String) (address : Nat)
  | mismatch (what : String)
  deriving DecidableEq, Repr

/-- Whether a memory has the byte at an address at all, which a write gives the page of. -/
private def holds (memory : Memory width) (address : Nat) : Bool :=
  memory.pages.contains (address / Memory.pageSize)

private def memoryOf (state : Bil.State) (var : Bap.Var) : Option (Σ width, Memory width) :=
  match Bil.lookup state.env var with
  | .ok (@Value.memory width memory) => some ⟨width, memory⟩
  | _ => none

/-- The variables that a program may read on some way through it before it has assigned them, given those assigned before it, in the
order read; those that it has assigned on every way through it that goes on after it; and whether any does. A jump, a special or an
exception ends a way, as a run ends there, so that what comes after one isn't read on it: what an `if` assigns counts after it where
each side that goes on does, and nothing comes after one of which neither does, and what a loop does counts where it doesn't run. -/
private partial def readsUnassigned (assigned : List Bap.Var) : Bil.Program → List Bap.Var × List Bap.Var × Bool
  | [] => ([], assigned, true)
  | stmt :: rest =>
    let unassigned (exp : Bil.Exp) := (Bil.freeVars exp).filter (!assigned.contains ·)
    let (here, after, goesOn) : List Bap.Var × List Bap.Var × Bool := match stmt with
      | .move var value => (unassigned value, var :: assigned, true)
      | .jmp target => (unassigned target, assigned, false)
      | .ifElse condition yes no =>
        let (yesReads, yesAssigned, yesGoesOn) := readsUnassigned assigned yes
        let (noReads, noAssigned, noGoesOn) := readsUnassigned assigned no
        let after := match yesGoesOn, noGoesOn with
          | true, true => yesAssigned.filter noAssigned.contains
          | true, false => yesAssigned
          | false, _ => noAssigned
        (unassigned condition ++ yesReads ++ noReads, after, yesGoesOn || noGoesOn)
      | .while condition body => (unassigned condition ++ (readsUnassigned assigned body).1, assigned, true)
      | .special _ | .cpuExn _ => ([], assigned, false)
    if !goesOn then (here, after, false)
    else
      let (later, final, last) := readsUnassigned after rest
      (here ++ later, final, last)

/-- `compare`, as what each disagreement is: of a run that failed, with the input that it reads and nothing gives, of bytes that what
comes next consumes and neither side has, of a store that the simplified dropped, which is dead where `liveRanges` say what memory is live
after and it is outside them, or a real mismatch. A side that failed doesn't hide what the other is. Nothing is what `ok` of `compare` is. -/
def diagnose (registers : List Bap.Var) (original simplified : Bil.Program)
    (initial : Bil.State := {}) (fuel : Nat := 100000) (continuationRanges : List (Nat × Nat) := [])
    (liveRanges : Option (List (Nat × Nat)) := none) : List Diagnosis := Id.run do
  -- A run, or why it failed: what it said, with each variable that it reads and nothing gives, which is known of the program and not
  -- of what the message says.
  let run (side : String) (program : Bil.Program) : Except (List Diagnosis) (Bil.State × Bil.Effect) :=
    match Bil.run program initial fuel with
    | .ok result => .ok result
    | .error message =>
      let ungiven := (readsUnassigned [] program).1.eraseDups.filter fun var => (Bil.lookup initial.env var).toOption.isNone
      .error (ungiven.map (.unresolvedInput side ·.name) ++ [.failed side message])
  let (originalState, originalEffect, simplifiedState, simplifiedEffect) ←
    match run "original" original, run "simplified" simplified with
    | .ok (originalState, originalEffect), .ok (simplifiedState, simplifiedEffect) =>
      pure (originalState, originalEffect, simplifiedState, simplifiedEffect)
    | left, right => return [left, right].flatMap fun | .error diagnoses => diagnoses | .ok _ => []
  let within (ranges : List (Nat × Nat)) (address : Nat) := ranges.any fun (first, last) => first ≤ address && address < last
  let inRanges := within continuationRanges
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
            let dropped := rightByte == readBefore address && leftByte != readBefore address
            if dropped && !inRanges address.toNat && liveRanges.all (!within · address.toNat) then
              found := found.push (if liveRanges.isSome then .deadStore var.name address.toNat else .droppedStore var.name address.toNat)
            else
              found := found.push (.mismatch s!"{var.name} at {address.toNat} holds {leftByte} and not {rightByte}")
        for (first, last) in continuationRanges do
          for offset in List.range (last - first) do
            let address := first + offset
            if !holds left address && !holds right address then found := found.push (.missingBytes var.name address)
      else found := found.push (.mismatch s!"{var.name} is of {width} bits and of {rightWidth}")
    | _, _ => found := found.push (.mismatch s!"{var.name} is a memory on one side only")
  pure found.toList

/-- A comparison with what each of its disagreements is: what `compare` says, none where a run failed, and why it isn't `ok`. -/
structure Verdict where
  result : Option Result
  diagnoses : List Diagnosis
  deriving Repr

/-- Whether both ran and agree in all that `compare` asks. -/
def Verdict.ok (verdict : Verdict) : Bool := verdict.result.any Validate.ok

/-- The disagreements that may be real ones: each mismatch, and each store that the simplified dropped that nothing says is dead, as
`liveRanges` would, as what comes after may read it. Input or bytes that weren't given, and a store that is dead, aren't. -/
def Verdict.mismatches (verdict : Verdict) : List String :=
  verdict.diagnoses.filterMap fun
    | .mismatch what => some what
    | .droppedStore memory address => some s!"{memory} at {address} isn't stored by the simplified, and nothing says that it is dead"
    | _ => none

/-- `compare` and `diagnose` at once. -/
def check (registers : List Bap.Var) (original simplified : Bil.Program)
    (initial : Bil.State := {}) (fuel : Nat := 100000) (continuationRanges : List (Nat × Nat) := [])
    (liveRanges : Option (List (Nat × Nat)) := none) : Verdict :=
  { result := (compare registers original simplified initial fuel continuationRanges).toOption
    diagnoses := diagnose registers original simplified initial fuel continuationRanges liveRanges }

end Bap.Analysis.Validate
