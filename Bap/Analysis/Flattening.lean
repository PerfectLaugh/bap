import Bap.Analysis.Checker
import Bap.Analysis.Cff

/-! # Flattened control flow, without running it

What `Cff` finds of a flattened machine as it runs, found of its code: the dispatcher, where the state is kept, the handler of each
state, and the graph of the states, as a `Cff.Cfg`, so that the two can be compared and the profile that `Cff` runs with is had of
the code rather than given. And a partition with the flow that the machine hides: each way back to the dispatcher goes to the
handlers of the states it sets, which `Frame`, `Values` and `Checker` then go over as the program's own flow.

The dispatcher of a function is one of the two instructions that most of its own go to, of a jump straight on where it goes. What
it keeps its state in is what the first choice it makes from there is of, when nothing is known of the registers or the memory: a
register, or bytes at a constant from one, at the address the lifter makes of it, or at an address. Of each that may be the
dispatcher and the state, the one of the most states that are known is the machine.

The machine is run symbolically from the entry of the function, a round at a time: each time it comes back to the dispatcher the
state is what it set, a constant or a choice of constants, and a round goes on for each state that no round has gone on for. A
handler starts where the last choice that the dispatcher made of the state went. What a register held that changed from a time at
the dispatcher to the next is kept as a choice of all the constants that it held, of a condition new to the round: a compiler hoists
a choice of the next state out of a handler with conditional moves or a branch before the dispatcher, and what changes together, as
the two halves of a constant of RISC-V or PowerPC, is chosen together. What held more constants in each of two runs one after the
other is a counter, and what held what isn't a constant is new to each round; it is run again until nothing more is found. A function
whose first state isn't a constant, whose states run a few places of code, as the counts of a loop do, or that has fewer than three
states, isn't a machine. -/

namespace Bap.Analysis.Flattening

open Bap.Analysis.Partition (Partition)
open Bap.Symbolic (Expr)

/-! ## Values of expressions -/

/-- How many parts an expression has, as far as `limit`, but of the conditions of its choices. -/
partial def armsSize (limit : Nat) (expr : Expr) : Nat :=
  let rec go (left : Nat) (expr : Expr) : Nat :=
    if left == 0 then 0 else
    let left := left - 1
    match expr with
    | .app _ _ args => args.foldl go left
    | .extract _ _ value | .select _ value => go left value
    | .concat first second => go (go left first) second
    | .ite _ yes no => go (go left yes) no
    | _ => left
  limit + 1 - go (limit + 1) expr

/-- The constants that an expression can be, of a choice of constants as conditional moves make: by its conditions, each way. -/
partial def choices (expr : Expr) (most : Nat := 16) : Option (List Nat) :=
  -- what is chosen, which a condition isn't of: a conditional move of what a load of the stack decided has a big condition
  if armsSize Checker.maxQuestion expr > Checker.maxQuestion then none else
  let rec go : Expr → Option (List Nat)
    | .const value => some [value.toNat]
    | .ite _ yes no => do
      let yes ← go yes
      let no ← go no
      pure (Partition.dedup (yes ++ no))
    | .extract high low value => do
      let values ← go value
      pure (Partition.dedup (values.map fun value => (value / 2 ^ low) % 2 ^ (high + 1 - low)))
    | .concat left right => do
      let lefts ← go left
      let rights ← go right
      if lefts.length * rights.length > most then none
      else pure (Partition.dedup (lefts.flatMap fun l => rights.map fun r => l * 2 ^ right.width + r))
    | .app name width args => do
      -- an operation of choices, of each of them, as far as there are few; of operands that are the same, each the same, as
      -- PowerPC's `mr` is an `or` of a register with itself
      let distinct := args.foldl (init := ([] : List Expr)) fun seen arg =>
        if seen.any (Expr.structuralEq · arg) then seen else seen ++ [arg]
      let values ← distinct.mapM go
      let combinations := values.foldr (init := [[]]) fun options rest =>
        options.flatMap fun option => rest.map (option :: ·)
      if combinations.length > most then none
      let results := combinations.filterMap fun picked =>
        let valueOf (arg : Expr) : Nat :=
          ((distinct.zip picked).find? (Expr.structuralEq ·.1 arg)).map (·.2) |>.getD 0
        let closed := Expr.app name width (args.map fun arg => Expr.const (BitVec.ofNat arg.width (valueOf arg)))
        match Partition.simplify closed with
        | .const value => some value.toNat
        | _ => none
      if results.length != combinations.length || width == 0 then none else pure (Partition.dedup results)
    | _ => none
  if Checker.sizeOf Checker.maxQuestion expr > Checker.maxQuestion then
    match go expr with
    | some values => if values.length ≤ most then some values else none
    | none => none
  else
  let simple := Partition.simplify expr
  -- of the choices of rounds alone, each way they go, which keeps what the same choice makes of two registers together
  let names := Partition.varsOf simple
  if !names.isEmpty && names.length ≤ 4 && names.all (·.startsWith "choice@") && (Partition.selectsOf simple).isEmpty then
    let widths := simple.vars
    let assignments := names.foldr (init := [([] : List (String × Nat))]) fun name rest =>
      let width := ((widths.find? (·.1 == name)).map (·.2)).getD 1
      (List.range (min (2 ^ width) most)).flatMap fun value => rest.map ((name, value) :: ·)
    let values := Partition.dedup (assignments.map fun assignment =>
      let σ : Proofs.Symbolic.Assignment :=
        { var := fun name width => BitVec.ofNat width (((assignment.find? (·.1 == name)).map (·.2)).getD 0)
          memory := fun _ _ _ => 0 }
      Partition.valueOf σ simple)
    if values.length ≤ most && assignments.length ≤ 4096 then some values else none
  else
  match go simple with
  | some values => if values.length ≤ most then some values else none
  | none => none

/-- The value of an expression that is of nothing but the bytes of the image, at addresses that are constants. -/
def imageValue (image : Image.Image) (expr : Expr) : Option Nat :=
  if Checker.sizeOf Checker.maxQuestion expr > Checker.maxQuestion then none
  else
    let simple := Partition.simplify expr
    if !(Partition.varsOf simple).isEmpty then none
    else
      let σ := Partition.assignment image "" 0
      if Partition.readsMapped image σ simple then some (Partition.valueOf σ simple) else none

/-! ## The state -/

/-- An address without what doesn't change it, as an `extract` of all its bits that a cast of the lifter makes, where it is small
enough to look at. -/
def simpler (address : Expr) : Expr :=
  if Checker.sizeOf 256 address > 256 then address else Partition.simplify address

/-- Two addresses that are the same location under every assignment: of the same base, at the same offset. -/
def sameAddress (left right : Expr) : Bool :=
  let (leftBase, leftOffset) := Symbolic.Memory.baseOffset (simpler left)
  let (rightBase, rightOffset) := Symbolic.Memory.baseOffset (simpler right)
  left.width == right.width && leftOffset == rightOffset && Expr.structuralEq leftBase rightBase

/-- The variable of memory that a function's code reads. -/
def memoryVar (instructions : List Disasm.Insn) : Option Bap.Var :=
  let rec ofExp : Bil.Exp → Option Bap.Var
    | .var var => if var.typ matches .mem _ _ then some var else none
    | .load memory _ _ _ => ofExp memory
    | .store memory _ _ _ _ => ofExp memory
    | _ => none
  instructions.findSome? fun insn => insn.bil.findSome? fun stmt =>
    match stmt with
    | .move var value => if var.typ matches .mem _ _ then some var else ofExp value
    | _ => none

/-- What a register holds in a state: what it was given, or what it held where the state started. -/
def registerValue (state : Symbolic.State) (name : String) (width : Nat) : Expr :=
  let var : Bap.Var := ⟨name, .imm width, 0, false⟩
  (Bap.Assoc.get var state.env).getD (.var (Symbolic.inputName var) width)

/-- Where the state is kept, and of a state at a constant from a register, the address that the dispatcher reads it at, of the
input of that register: the lifter's own, which is what its writes of the state are at too, as the executor reads a write only
at an address that is the same as it. -/
structure Place where
  location : Cff.StateLocation
  shape : Option (Expr × Expr) := none
  deriving Inhabited

/-- The address of the state, in a state, of where it is. -/
def stateAddress (state : Symbolic.State) (width : Nat) (place : Place) : Option Expr :=
  match place.location, place.shape with
  | .register .., _ => none
  | .memory address _, _ => some (.const (BitVec.ofNat width address))
  | .relative register _ _, some (base, address) => some (Partition.replace base (registerValue state register width) address)
  | .relative register offset _, none =>
    some (.app "bvadd" width [registerValue state register width, .const (BitVec.ofNat width (offset % 2 ^ width).toNat)])

/-- The byte at an address of cells of memory, newest first: of the newest write of it, or of the image, of an address that nothing
wrote; none where a write may or may not be of it. -/
def byteAt (image : Image.Image) (cells : List (Expr × Expr)) (address : Expr) : Option Expr :=
  match cells with
  | [] => match address with
    | .const value => (Partition.imageByte image value.toNat).map fun byte => Expr.const (BitVec.ofNat 8 byte)
    | _ => none
  | (cell, value) :: rest =>
    if sameAddress cell address then some value
    else if Symbolic.Memory.definitelyDistinct (simpler cell) (simpler address) then byteAt image rest address
    else none

/-- What the state is, in a state: a register, or bytes of memory, of the newest writes of them, or of the image, of a state at an
address that nothing wrote. -/
def readState (image : Image.Image) (memory : Option Bap.Var) (state : Symbolic.State) (width : Nat)
    (place : Place) : Option Expr := do
  match place.location with
  | .register name registerWidth => pure (registerValue state name registerWidth)
  | .memory _ size | .relative _ _ size =>
    let address ← stateAddress state width place
    let memory ← memory
    let cells := (Symbolic.memoryOf state memory).cells
    let bytes ← (List.range size).mapM fun offset =>
      byteAt image cells (Partition.simplify (.app "bvadd" width [address, .const (BitVec.ofNat width offset)]))
    let ordered := if image.endian == .little then bytes.reverse else bytes
    -- bytes that are the pieces of one value, most significant first, are that value, which a choice keeps as one
    let pieces := ordered.filterMap fun byte => match byte with
      | .extract high low value => some (high, low, value)
      | _ => none
    let whole : Option Expr := match pieces with
      | (high, _, value) :: _ =>
        let contiguous := pieces.length == ordered.length &&
          (pieces.zip (pieces.drop 1)).all (fun ((_, low, _), (high', _, _)) => high' + 1 == low) &&
          pieces.all fun (_, _, other) => Expr.structuralEq other value
        let low := (pieces.getLast?.map (·.2.1)).getD 0
        if contiguous then some (if low == 0 && high + 1 == value.width then value else .extract high low value) else none
      | [] => none
    if let some value := whole then pure value else
    let first ← ordered.head?
    pure (ordered.tail.foldl (fun result byte => .concat result byte) first)

/-- A state with the state set to a constant. -/
def setState (memory : Option Bap.Var) (state : Symbolic.State) (width : Nat) (endian : Bap.Endian)
    (place : Place) (value : Nat) : Symbolic.State :=
  match place.location with
  | .register name registerWidth =>
    { state with env := ((⟨name, .imm registerWidth, 0, false⟩ : Bap.Var), Expr.const (BitVec.ofNat registerWidth value)) ::
        state.env }
  | .memory _ size | .relative _ _ size =>
    match memory, stateAddress state width place with
    | some memory, some address =>
      let written := (Symbolic.memoryOf state memory).write address (.const (BitVec.ofNat (size * 8) value)) endian size
      { state with memories := (memory, written) :: state.memories }
    | _, _ => state

/-- Where the state is kept, of the first choice that the code at the dispatcher makes when nothing is known: of the register it is
of, or of the bytes of memory, at a constant from a register or at an address. -/
def locate (function : Checker.Function) (dispatcher : Nat) (steps : Nat := 64) : IO (List Place) := do
  let mut way : Checker.Way := { state := {}, path := [], visits := {} }
  let mut address := dispatcher
  for _ in List.range steps do
    let some insn := function.instructions[address]? | return []
    -- what is chosen: the condition of a branch, or the target of a jump that isn't a constant
    let chosen : Option Expr ←
      if insn.flow == .indirectJump then
        match Symbolic.run insn.bil way.state 4000 with
        | .ok (result :: _) => match result.outcome with
          | .jump target => pure (if (Checker.constOf target).isSome then none else some target)
          | _ => pure none
        | _ => pure none
      else pure none
    let steps ← Checker.stepWay function way insn
    let condition := if steps.length > 1 then steps.head?.bind (·.way.state.constraints.getLast?) else none
    match chosen <|> condition with
    | some expr => return ofChoice expr
    | none =>
      let some step := steps.head? | return []
      let some next := step.next | return []
      way := step.way
      address := next
  return []
where
  /-- What a choice is of: bytes of memory, or each register it reads, as a compiler that keeps the constants of the cases in
  registers compares two. -/
  ofChoice (raw : Expr) : List Place :=
    if Checker.sizeOf Checker.maxQuestion raw > Checker.maxQuestion then [] else
    let expr := Partition.simplify raw
    let width := function.width
    let reads := (Partition.selectsOf expr).filter fun address => !Partition.closed address
    let constant := (Partition.selectsOf expr).filter fun address =>
      Partition.closed address && !Partition.inCode function.image (Partition.valueOf (Partition.assignment function.image "" 0) address)
    let registerOf (name : String) : String := (name.splitOn "#").headD name
    if !reads.isEmpty then
      -- bytes at a constant from what a register held: their offsets, of a register as zero
      let bases := Partition.dedup (reads.flatMap Partition.varsOf) |>.filter fun name => (name.splitOn "#").length == 4
      match bases with
      | [base] =>
        let σ := Partition.assignment function.image base 0
        let offsets := Partition.dedup (reads.map fun address => Frame.signed width (Partition.valueOf σ address))
        let low := offsets.foldl min (offsets.headD 0)
        let baseWidth := ((reads.flatMap (·.vars)).find? (·.1 == base)).map (·.2) |>.getD width
        -- the address as the lifter makes it, which the executor's writes of the state are at
        let first := ((Partition.selectsOf raw).filter (!Partition.closed ·)).find? fun address =>
          Frame.signed width (Partition.valueOf σ address) == low
        [{ location := .relative (registerOf base) low offsets.length, shape := first.map (Expr.var base baseWidth, ·) }]
      | _ => []
    else if !constant.isEmpty then
      let σ := Partition.assignment function.image "" 0
      let addresses := Partition.dedup (constant.map (Partition.valueOf σ))
      [{ location := .memory (addresses.foldl min (addresses.headD 0)) addresses.length }]
    else
      -- of what a register held where the run started, not of what a call left, which is new to the run
      ((Partition.varsOf expr).filter fun name => (name.splitOn "#").length == 4).map fun name =>
        let width := ((expr.vars.find? (·.1 == name)).map (·.2)).getD width
        { location := .register (registerOf name) width }

/-- What may be the dispatcher of a function: the instructions of it that most of its own instructions go to, of at least three
each, most first: the dispatcher, and where the dispatcher's own code goes back to when no case is of the state; of a jump straight
on, where it goes. -/
def dispatchersOf (function : Checker.Function) (most : Nat := 2) : List Nat :=
  let counts : Std.HashMap Nat Nat := function.instructions.fold (init := {}) fun table address _ =>
    (function.successors address).foldl (init := table) fun table target => table.insert target (table.getD target 0 + 1)
  let ranked := (counts.toList.filter (·.2 ≥ 3)).mergeSort fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)
  -- of a jump straight on, as the end of a loop that the code of each case goes to, where it goes
  let onward (address : Nat) : Nat :=
    match function.instructions[address]? with
    | some insn => match insn.flow, insn.target with
      | .jump, some target => if function.instructions.contains target then target else address
      | _, _ => address
    | none => address
  Partition.dedup ((ranked.take most).map (onward ·.1))

/-! ## The machine -/

/-- A round that came back to the dispatcher, or ended: of what state, from which instruction, to which states, and whether it chose
by a branch of its own or a choice of constants. -/
structure Arrival where
  state : Option Nat
  /-- The last instruction of the round, before the dispatcher. -/
  last : Option Nat
  /-- The states it went to, or none where the state isn't a constant or a choice of constants; none of a round that ended. -/
  nexts : Option (List Nat)
  ended : Bool := false
  deriving Repr

/-- A choice of constants of `width` bits, of conditions new to the round, named of `fresh`. -/
def choiceOf (fresh : String) (width : Nat) : List Nat → Expr
  | [] => .var s!"value@{fresh}" width
  | first :: rest =>
    let (chosen, _) := rest.foldl (init := (Expr.const (BitVec.ofNat width first), 0)) fun (others, index) option =>
      (.ite (.app "=" 1 [.var s!"choice@{fresh}#{index}" 1, .const (BitVec.ofNat 1 1)]) (.const (BitVec.ofNat width option)) others,
        index + 1)
    chosen

/-- What a run of the machine found: the rounds, the instructions of each state's rounds, and what changes between times at the
dispatcher, which a run after it makes new to each round. -/
structure Run where
  arrivals : Array Arrival := #[]
  paths : Std.HashMap Nat (List Nat) := {}
  varying : Std.HashSet String := {}
  /-- Of what changes, the constants it held at the dispatcher, where it held only constants, as a choice that a handler hoisted
  out of it, or a branch before the dispatcher, makes; and what changes otherwise, as a counter does, of each round more. -/
  constants : Std.HashMap String (List Nat) := {}
  derived : Std.HashSet String := {}
  /-- The constants that what changes held together at the dispatcher, of each time. -/
  tuples : List (List (String × Nat)) := []
  /-- Of each state, where the last choice that the dispatcher made of it went. -/
  entries : Std.HashMap Nat Nat := {}
  /-- What each register and cell held the first time at the dispatcher. -/
  first : Std.HashMap String Expr := {}

structure Config where
  maxSteps : Nat := 20000
  maxRound : Nat := 512
  maxRuns : Nat := 10
  /-- How many instructions the ways from the entry of a function to its dispatcher go. -/
  maxBefore : Nat := 256
  /-- How long the runs of a function go, in milliseconds, of all that may be its dispatcher and its state. -/
  maxMillis : Nat := 250

/-- A run of the machine from the entry of its function, a round for each state, of what is known to change between rounds. -/
partial def runMachine (function : Checker.Function) (memory : Option Bap.Var) (dispatcher : Nat) (place : Place)
    (previous : Run) (config : Config) (deadline : Nat := 0) : IO Run := do
  let image := function.image
  let width := function.width
  let result ← IO.mkRef ({ previous with arrivals := #[], paths := {}, entries := {}, first := {} } : Run)
  let expanded ← IO.mkRef ({} : Std.HashSet Nat)
  let steps ← IO.mkRef 0
  let arrivals ← IO.mkRef 0
  let keyOf (var : Bap.Var) : String := s!"{var.name}"
  let locationRegister := match place.location with
    | .register name _ => some name
    | _ => none
  -- of a time at the dispatcher: what changed since the first, and what is kept of each value
  let arrive (state : Symbolic.State) : IO Symbolic.State := do
    let tag ← arrivals.modifyGet fun count => (count, count + 1)
    let run ← result.get
    let mut first := run.first
    let mut varying := run.varying
    for (var, value) in state.env do
      let key := keyOf var
      if some key == locationRegister then continue
      match first[key]? with
      | some before => if !Expr.structuralEq before value then varying := varying.insert key
      | none => first := first.insert key value
    result.modify fun run => { run with first, varying }
    -- what changes is a choice of the constants it held, of those that change together, as two halves of a constant that a branch
    -- before the dispatcher chooses do; or else new to the round
    let run ← result.get
    let choosing (key : String) (value : Expr) : Bool :=
      !run.derived.contains key && Checker.sizeOf Checker.maxQuestion value ≤ Checker.maxQuestion &&
        (Partition.selectsOf (Partition.simplify value)).isEmpty &&
        (Partition.varsOf (Partition.simplify value)).all (·.startsWith "choice@")
    let changing := state.env.filter fun (var, _) => varying.contains (keyOf var) && some (keyOf var) != locationRegister
    let chosen := changing.filter fun (var, value) => choosing (keyOf var) value
    let names := Partition.dedup (chosen.flatMap fun (_, value) => Partition.varsOf (Partition.simplify value))
    -- of more conditions than are gone over together, each is a choice of its own
    -- the constants of each way the conditions go, of all of them at once
    let tuples : Option (List (List (String × Nat))) :=
      let widths := chosen.flatMap fun (_, value) => (Partition.simplify value).vars
      let assignments := names.foldr (init := [([] : List (String × Nat))]) fun name rest =>
        let width := ((widths.find? (·.1 == name)).map (·.2)).getD 1
        (List.range (min (2 ^ width) 17)).flatMap fun value => rest.map ((name, value) :: ·)
      if assignments.length > 512 then none else
      some <| assignments.map fun assignment =>
        let σ : Proofs.Symbolic.Assignment :=
          { var := fun name width => BitVec.ofNat width (((assignment.find? (·.1 == name)).map (·.2)).getD 0)
            memory := fun _ _ _ => 0 }
        chosen.map fun (var, value) => (keyOf var, Partition.valueOf σ value)
    let keys := chosen.map (keyOf ·.1)
    let union : Option (List (List (String × Nat))) := match tuples with
      | some now =>
        let before := (run.tuples.filter fun (tuple : List (String × Nat)) => keys.all fun key => tuple.any (·.1 == key)).map fun tuple =>
          keys.map fun key => (key, ((tuple.find? (·.1 == key)).map (·.2)).getD 0)
        let joint := Partition.dedup (before ++ now)
        -- and each constant that one held before, which the tuples of other registers lost, with the others as the first has them
        let lost := keys.flatMap fun key =>
          let had := joint.filterMap fun tuple => (tuple.find? (·.1 == key)).map (·.2)
          ((run.constants.getD key []).filter (!had.contains ·)).filterMap fun value =>
            joint.head?.map fun tuple => tuple.map fun (other, held) => (other, if other == key then value else held)
        some (Partition.dedup (joint ++ lost))
      | none => none
    let fresh := s!"{tag}"
    match union with
    | some all =>
      let projections := keys.map fun key => (key, Partition.dedup (all.filterMap fun (tuple : List (String × Nat)) => (tuple.find? (·.1 == key)).map (·.2)))
      result.modify fun run => { run with tuples := all
                                          constants := projections.foldl (init := run.constants) fun table (key, values) =>
                                            table.insert key (Partition.dedup (table.getD key [] ++ values) |>.mergeSort (· ≤ ·)) }
    | none => pure ()
    let selector : Expr := .var s!"choice@{fresh}" 8
    -- a choice of constants on a condition of what is new to the round, as a conditional move of the machine's input makes, is a
    -- choice of its own of all the constants it took
    let mut own : List (String × List Nat) := []
    for (var, value) in changing do
      let key := keyOf var
      if (union.isSome && keys.contains key) || run.derived.contains key then continue
      if let some values := choices value then
        let all := Partition.dedup (run.constants.getD key [] ++ values) |>.mergeSort (· ≤ ·)
        if all.length ≤ 16 then
          own := (key, all) :: own
          result.modify fun run => { run with constants := run.constants.insert key all }
    let kept := state.env.map fun (var, value) =>
      let key := keyOf var
      if !varying.contains key || some key == locationRegister then (var, value)
      else if let some (_, all) := own.find? (·.1 == key) then (var, choiceOf s!"{key}{fresh}" value.width all)
      else match union with
        | some all =>
          if keys.contains key && all.length ≤ 256 then
            let options := all.map fun (tuple : List (String × Nat)) => ((tuple.find? (·.1 == key)).map (·.2)).getD 0
            let (chosen, _) := options.tail.foldl (init := (Expr.const (BitVec.ofNat value.width (options.headD 0)), 1))
              fun (others, index) option =>
                (.ite (.app "=" 1 [selector, .const (BitVec.ofNat 8 index)]) (.const (BitVec.ofNat value.width option)) others,
                  index + 1)
            (var, chosen)
          else (var, .var s!"value@{key}{fresh}" value.width)
        | none => (var, .var s!"value@{key}{fresh}" value.width)
    -- what changes otherwise is what a round makes of what isn't a constant
    for (var, value) in changing do
      if !choosing (keyOf var) value && !own.any (·.1 == keyOf var) then
        result.modify fun run => { run with derived := run.derived.insert (keyOf var) }
    let env := kept
    -- what the rounds write to memory but the state is of the round that wrote it
    let memories := match memory with
      | some var =>
        let kept := (Symbolic.memoryOf state var).cells.filter fun (address, _) =>
          match stateAddress state width place with
          | some at_ => (List.range 8).any fun offset =>
            sameAddress address (Partition.simplify (.app "bvadd" width [at_, .const (BitVec.ofNat width offset)]))
          | none => false
        [(var, { Symbolic.memoryOf state var with cells := kept })]
      | none => state.memories
    pure { state with env, memories }
  -- `decided` is where the last choice of a constant went, of a round that hasn't forked, which is the dispatcher's of the state
  let rec go (way : Checker.Way) (address : Nat) (current : Option Nat) (round : Nat) (decided : Option Nat) : IO Unit := do
    if (← steps.get) ≥ config.maxSteps || round ≥ config.maxRound then return
    if deadline > 0 && (← steps.get) % 64 == 0 && (← IO.monoMsNow) > deadline then return
    -- what is before the dispatcher is little of a flattened function, which is all rounds
    if current.isNone && (← steps.get) ≥ config.maxBefore then
      steps.set config.maxSteps
      return
    if way.visits.getD address 0 ≥ 2 || Checker.oversized way.state then return
    let some insn := function.instructions[address]? | return
    steps.modify (· + 1)
    if let some state := current then
      result.modify fun run => { run with paths := run.paths.insert state (address :: run.paths.getD state []) }
    let mut nexts ← Checker.stepWay function way insn
    -- a jump through a table of the image goes where the table says
    if insn.flow == .indirectJump then
      if let .ok results := Symbolic.run insn.bil way.state 4000 then
        let targets := results.filterMap fun result => match result.outcome with
          | .jump target => imageValue image target
          | _ => none
        if !targets.isEmpty then nexts := nexts.filter fun step => step.next.any targets.contains
    -- a choice that went one way, of a jump that chooses, is of what is known, the state; one that went two, of the handler
    let chooses := insn.flow == .conditionalJump || insn.flow == .indirectJump
    let decided := match nexts with
      | [step] => if chooses then step.way.pending <|> step.next else decided
      | _ => decided
    if nexts.length > 1 || nexts.any (·.next == some dispatcher) || nexts.any (·.next.isNone) then
      if let (some state, some at_) := (current, decided) then
        result.modify fun run => if run.entries.contains state then run else { run with entries := run.entries.insert state at_ }
        -- states of a few places of code are the counts of a loop, not a machine's: no more of them
        let entries := (← result.get).entries
        let places := entries.fold (init := ({} : Std.HashSet Nat)) fun set _ at_ => set.insert at_
        if entries.size ≥ 8 && 2 * places.size < entries.size then steps.set config.maxSteps
    let decided := if nexts.length > 1 then none else decided
    for step in nexts do
      match step.next with
      | none =>
        result.modify fun run => { run with arrivals := run.arrivals.push ({ state := current, last := some insn.address, nexts := none, ended := true } : Arrival) }
      | some next =>
        if next != dispatcher then go step.way next current (round + 1) (if nexts.length > 1 then none else decided)
        else
          -- a time at the dispatcher: the states the round set, and a round of each that no round has been of
          let state ← arrive step.way.state
          let values := (readState image memory state width place).bind choices
          result.modify fun run => { run with arrivals := run.arrivals.push ({ state := current, last := some insn.address, nexts := values } : Arrival) }
          -- a machine starts in a state that is a constant: of a dispatcher that is first come to otherwise, no more
          if current.isNone && !(values matches some [_]) then
            steps.set config.maxSteps
            return
          for value in values.getD [] do
            if (← expanded.get).contains value then continue
            expanded.modify (·.insert value)
            let set := setState memory state width image.endian place value
            go { step.way with state := set, visits := {} } dispatcher (some value) 0 none
  -- of PowerPC, the summary overflow that a compare puts in the condition register with what it found is clear, as it is but after
  -- an overflow that a program asked to be kept
  let initial := Partition.entryState image function.entry
  let initial := if image.arch == .powerpc then
      { initial with env := ((⟨"SO", .imm 1, 0, false⟩ : Bap.Var), Expr.const (BitVec.ofNat 1 0)) :: initial.env }
    else initial
  go { state := initial, path := [], visits := {} } function.entry none 0 none
  result.get

/-- A flattened machine of a function. -/
structure Machine where
  function : Nat
  dispatcher : Nat
  state : Cff.StateLocation
  /-- The state of the first round. -/
  initial : Option Nat
  /-- Where the handler of each state starts: the first instruction of its rounds that no other state's rounds run. -/
  handlers : List (Nat × Nat)
  cfg : Cff.Cfg
  arrivals : List Arrival
  /-- What all the rounds run, which is the dispatcher's own code. -/
  dispatch : List Nat
  deriving Repr

/-- The profile that `Cff` runs the machine with, with where each handler starts. -/
def Machine.profile (machine : Machine) : Cff.Profile :=
  { dispatcher := machine.dispatcher, state := machine.state, handlers := machine.handlers }

def Machine.handlerOf (machine : Machine) (state : Nat) : Option Nat :=
  (machine.handlers.find? (·.1 == state)).map (·.2)

/-- The graph of the states, of the rounds: a state that went to one state and didn't choose goes to it directly; one that chose,
by a branch or a choice of constants, conditionally; and one whose next state isn't known, to that too. -/
def graphOf (arrivals : List Arrival) : Cff.Cfg :=
  let sources := Partition.dedup (arrivals.filterMap (·.state))
  let edges := sources.flatMap fun source =>
    let rounds := arrivals.filter (·.state == some source) |>.filter (!·.ended)
    let unknown := rounds.any (·.nexts.isNone)
    let targets := Partition.dedup (rounds.flatMap fun arrival => arrival.nexts.getD [])
    let count (target : Nat) := (rounds.filter fun arrival => (arrival.nexts.getD []).contains target).length
    let kind : Cff.EdgeKind := if unknown then .indirect else if targets.length > 1 then .conditional else .direct
    targets.map (fun target => ({ source, target := some target, kind, count := count target } : Cff.Edge)) ++
      (if unknown then [{ source, target := none, kind, count := 0 }] else [])
  let initial := (arrivals.find? (·.state.isNone)).bind fun arrival => arrival.nexts.bind fun nexts =>
    if nexts.length == 1 then nexts.head? else none
  { entry := initial
    states := sources.mergeSort (· ≤ ·)
    edges
    exits := Partition.dedup ((arrivals.filter (·.ended)).filterMap (·.state)) }

/-- Runs of the machine, as long as each finds more that changes between rounds: what held more constants at the dispatcher than it
did of the run before, of two runs one after the other, is a counter, new to each round from then on. -/
def settle (function : Checker.Function) (memory : Option Bap.Var) (dispatcher : Nat) (place : Place)
    (config : Config := {}) (deadline : Nat := 0) : IO Run := do
  let mut run ← runMachine function memory dispatcher place {} config deadline
  -- a machine starts in a state that is a constant
  if (graphOf run.arrivals.toList).entry.isNone then return run
  let mut grewBefore : Std.HashSet String := {}
  for _ in List.range config.maxRuns do
    if deadline > 0 && (← IO.monoMsNow) > deadline then break
    let again ← runMachine function memory dispatcher place run config deadline
    -- what held more constants, of two runs one after the other: a choice holds more once what it is chosen of is new to the
    -- round, and then no more
    let grewNow := again.constants.fold (init := ({} : Std.HashSet String)) fun grew key values =>
      if (run.constants.getD key []).length < values.length then grew.insert key else grew
    let derived := grewNow.fold (init := again.derived) fun derived key =>
      if grewBefore.contains key then derived.insert key else derived
    let changed := again.varying.size > run.varying.size || derived.size > run.derived.size || !grewNow.isEmpty
    grewBefore := grewNow
    run := { again with derived }
    if !changed then break
  return run

/-- The flattened machine of a function, if it has one: a dispatcher, the state it chooses by, three states or more, and two ways
between them. -/
def machineOf (image : Image.Image) (program : Frame.Program) (function : Partition.Function) (config : Config := {}) :
    IO (Option Machine) := do
  let some checked := Checker.Function.of image program function | return none
  let memory := memoryVar (checked.instructions.toList.map (·.2))
  -- of each that may be the dispatcher, and each that may be its state, the machine of the most states that are known
  let mut best : Option (Nat × Place × Run × Cff.Cfg) := none
  let deadline := (← IO.monoMsNow) + config.maxMillis
  for dispatcher in dispatchersOf checked do
    for place in ← locate checked dispatcher do
      -- runs, as long as each finds more that changes between rounds
      let run ← settle checked memory dispatcher place config deadline
      let cfg := graphOf run.arrivals.toList
      let score (cfg : Cff.Cfg) : Int := cfg.states.length - (cfg.edges.filter (·.target.isNone)).length
      if best.all fun (_, _, _, other) => score cfg > score other then best := some (dispatcher, place, run, cfg)
  let some (dispatcher, place, run, cfg) := best | return none
  let arrivals := run.arrivals.toList
  -- a machine of a few states that go from one to another, not a loop that counts
  if cfg.states.length < 3 || (cfg.edges.filter (·.target.isSome)).length < 2 then return none
  let states := cfg.states
  let pathOf (state : Nat) : List Nat := (run.paths.getD state []).reverse
  -- the code of every round is the dispatcher's; a handler starts where its rounds first run what no other's do
  let all : List (Nat × Std.HashSet Nat) := states.map fun state =>
    (state, (pathOf state).foldl (init := {}) fun set address => set.insert address)
  let dispatch := (pathOf (states.headD 0)).filter fun address => all.all fun (_, set) => set.contains address
  -- a handler starts where the last choice of the dispatcher, which is of the state, went: of a jump straight on, where it goes,
  -- but to the dispatcher or past a delay slot that does something;
  -- else, the first instruction of its rounds that no other state's rounds run
  let straight (address : Nat) : Nat := Id.run do
    let mut at_ := address
    for _ in List.range 4 do
      match checked.instructions[at_]? with
      | some insn =>
        -- not to the dispatcher, nor past a delay slot that does something, as a handler of MIPS that only sets the state does
        let slotDoes := Frame.slotted image.arch insn &&
          (checked.instructions[insn.next]?).any fun slot => !slot.bil.isEmpty
        match insn.flow, insn.target with
        | .jump, some target => if target == dispatcher || slotDoes then break else at_ := target
        | _, _ => break
      | none => break
    return at_
  let handlers := states.filterMap fun state =>
    match run.entries[state]? with
    | some decided => some (state, straight decided)
    | none =>
      let others := all.filter (·.1 != state)
      ((pathOf state).find? fun address => !others.any fun (_, set) => set.contains address).map (state, ·)
  -- each state of a flattened machine has code of its own, where a loop that counts runs the same code of each count
  let starts := Partition.dedup (handlers.map (·.2))
  if starts.length < 3 || 2 * starts.length < states.length then return none
  return some { function := function.entry, dispatcher, state := place.location, initial := cfg.entry, handlers, cfg, arrivals
                dispatch := Partition.dedup dispatch }

/-- The flattened machines of the functions of a partition. -/
def machines (image : Image.Image) (partition : Partition) (config : Config := {}) : IO (List Machine) := do
  let program := Frame.Program.of partition
  partition.functions.filterMapM fun function =>
    if function.importName.isSome then pure none else machineOf image program function config

/-! ## The flow that a machine hides -/

/-- A partition with the flow of its machines: a round that comes back to the dispatcher goes to the handlers of the states it sets
instead, and a round whose next state isn't known still goes to the dispatcher. What is shared of the rounds of states that go to
others goes to the handlers of all of them. -/
def deflatten (partition : Partition) (machines : List Machine) : Partition :=
  let redirected : List ((Nat × Nat) × List Nat) := machines.flatMap fun machine =>
    let rounds := machine.arrivals.filter fun arrival => !arrival.ended && arrival.last.isSome
    let lasts := Partition.dedup (rounds.filterMap (·.last))
    lasts.filterMap fun last =>
      let of := rounds.filter (·.last == some last)
      if of.any (·.nexts.isNone) then none
      else
        let targets := Partition.dedup (of.flatMap fun arrival => (arrival.nexts.getD []).filterMap machine.handlerOf)
        if targets.isEmpty then none else some ((last, machine.dispatcher), targets)
  let replaced : Std.HashMap (Nat × Nat) (List Nat) := redirected.foldl (init := {}) fun table (edge, targets) =>
    table.insert edge targets
  let edges := partition.edges.flatMap fun edge =>
    match replaced[edge]? with
    | some targets => targets.map (edge.1, ·)
    | none => [edge]
  { partition with edges := Partition.dedup edges }

/-! ## What a run says -/

/-- The targets of the jumps of a partition that a run of a machine saw: of the jump of the dispatcher's code, the handlers that its
rounds went to, for a partition to have where it doesn't know them, as of a table of states that are encoded. -/
def observed (partition : Partition) (dispatcher : Cff.Dispatcher) : Nat → List Nat :=
  let jumps := dispatcher.dispatch.filter fun address =>
    partition.disasm.instructions.any fun insn => insn.address == address && insn.flow == .indirectJump
  let targets := Partition.dedup (dispatcher.handlers.flatMap (·.entries))
  fun jump => if jumps.contains jump then targets else []

/-- The partition of a project again, with the targets of its dispatchers' jumps that a run of its machine saw. -/
def repartition (project : Project.Project) (partition : Partition) (dispatcher : Cff.Dispatcher) : IO (Option Partition) :=
  Values.partition project (observed := observed partition dispatcher)

/-- Whether what a run found is of what was found without it: each way between states that the run took, and where the handler
of each state starts. -/
def agrees (machine : Machine) (dispatcher : Cff.Dispatcher) : List String := Id.run do
  let mut problems : Array String := #[]
  for (from_, to, _) in dispatcher.graph do
    if !machine.cfg.edges.any fun edge => edge.source == from_ && (edge.target == some to || edge.target.isNone) then
      problems := problems.push s!"the run went from {from_} to {to}"
  for handler in dispatcher.handlers do
    match handler.entries.head?, machine.handlerOf handler.state with
    | some ran, some found => if ran != found then problems := problems.push s!"the handler of {handler.state} started at {ran}"
    | some _, none => problems := problems.push s!"the state {handler.state} has no handler"
    | none, _ => pure ()
  return problems.toList

end Bap.Analysis.Flattening
