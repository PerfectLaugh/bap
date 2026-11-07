import Bap.Analysis.Journal
import Bap.Analysis.DynamicTaint
import Bap.Bil.Transform

/-! Flattened control flow as it ran: a dispatcher that each round of the machine goes through, with a state that says which handler
comes next. What is particular to a target, where its dispatcher is and where its state is kept, is a `Profile`, and the rest is the
same for all. A `Recorder` notes the state at each visit of the dispatcher, which is one instruction that has a hook, so that the rest
runs as it always does. With a journal of the same run, `recover` also says what each handler was: where it starts, which is where its
round first runs what no other round does, how long it ran, and what it asked of the kernel; and a tracker says what decided each
transition, and how it was decided as it ran. Registers that the profile names are noted at each visit, with each round.

`Analysis.StateMachine` and `Analysis.Deflatten` find the same from the code alone, where the states are constants that it compares. -/

namespace Bap.Analysis.Cff

open Bap.Emu (Emu ThreadId)
open Bap.Analysis.DynamicTaint

/-- Where a state is. -/
inductive StateLocation where
  | register (name : String) (width : Nat := 64)
  | memory (address size : Nat)
  /-- At an offset from what a register holds, as a state on the stack is. -/
  | relative (register : String) (offset : Int) (size : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- What is particular to a target. -/
structure Profile where
  /-- Where each round goes through. -/
  dispatcher : Nat
  state : StateLocation
  /-- What a state is from what is kept, for a target that keeps it encoded. -/
  decode : Nat → Nat := id
  /-- Where the dispatcher's code is, if that is known: a handler starts at the first instruction outside it. -/
  dispatchRange : Option (Nat × Nat) := none
  /-- What a person calls each state. -/
  names : List (Nat × String) := []
  /-- Registers, with their widths, whose values are noted at each visit, as the thread came to the dispatcher. -/
  registers : List (String × Nat) := []

/-- What a register holds now, in the thread that runs. -/
def readRegister (emu : Emu) (name : String) (width : Nat) : IO Nat := do
  match Value.asBits (← Bap.Emu.reg emu ⟨name, .imm width, 0, false⟩) with
  | .ok bits => pure bits.2.toNat
  | .error error => throw <| IO.userError s!"{name}: {error}"

/-- What a state location holds now, in the thread that runs, as it is kept. -/
def readState (emu : Emu) (location : StateLocation) : IO Nat := do
  let number (bytes : ByteArray) : Nat :=
    let ordered := if emu.config.endian == .big then bytes.toList else bytes.toList.reverse
    ordered.foldl (fun value byte => value * 256 + byte.toNat) 0
  let registerValue (name : String) (width : Nat) : IO Nat := do
    try readRegister emu name width catch error => throw <| IO.userError s!"the state in {error}"
  match location with
  | .register name width => registerValue name width
  | .memory address size => pure (number (← Bap.Emu.peek emu address size))
  | .relative name offset size =>
    let width ← Bap.Emu.wordWidth emu
    let base ← registerValue name width
    let address := ((Int.ofNat base + offset) % (2 ^ width : Int)).toNat
    pure (number (← Bap.Emu.peek emu address size))

/-- A visit of the dispatcher. -/
structure Visit where
  thread : ThreadId
  group : Nat
  state : Nat
  /-- The last instruction of the thread that wrote the state since its last visit, of a state in memory: what assigned the state that
  this visit has. -/
  writer : Option Nat := none
  /-- What the registers of the profile held, in its order. -/
  registers : List (String × Nat) := []
  deriving DecidableEq, Repr, Inhabited

structure Recorder where
  profile : Profile
  visits : IO.Ref (Array Visit)
  hook : Bap.Emu.HookId
  /-- The hook of writes to a state in memory, and where it watches. -/
  watch : IO.Ref (Option (Bap.Emu.HookId × Nat))

/-- Where a state in memory is now, in the thread that runs, and how big it is. -/
private def stateAddress (emu : Emu) : StateLocation → IO (Option (Nat × Nat))
  | .register .. => pure none
  | .memory address size => pure (some (address, size))
  | .relative name offset size => do
    let width ← Bap.Emu.wordWidth emu
    match Value.asBits (← Bap.Emu.reg emu ⟨name, .imm width, 0, false⟩) with
    | .ok bits => pure (some (((Int.ofNat bits.2.toNat + offset) % (2 ^ width : Int)).toNat, size))
    | .error _ => pure none

/-- Notes the state each time a thread comes to the dispatcher, from here on, and of a state in memory, what last wrote it before. -/
def Recorder.attach (emu : Emu) (profile : Profile) : IO Recorder := do
  -- A register that isn't one is said now, and not at the first visit, in the middle of a run.
  for (name, width) in profile.registers do
    let _ ← readRegister emu name width
  let visits ← IO.mkRef #[]
  let writers ← IO.mkRef ({} : Std.HashMap ThreadId Nat)
  let watch ← IO.mkRef (none : Option (Bap.Emu.HookId × Nat))
  let watchAt (address size : Nat) : IO Unit := do
    match ← watch.get with
    | some (_, at_) => if at_ == address then return
    | none => pure ()
    if let some (hook, _) := ← watch.get then Bap.Emu.removeHook emu hook
    let hook ← Bap.Emu.onWrite emu (address, address + size - 1) fun current _ _ _ => do
      writers.modify (·.insert (← Bap.Emu.thread current) (← current.pc.get))
    watch.set (some (hook, address))
  if let some (address, size) := ← stateAddress emu profile.state then
    if size > 0 && !(profile.state matches .relative ..) then watchAt address size
  let hook ← Bap.Emu.onCode emu (profile.dispatcher, profile.dispatcher) fun current _ => do
    let thread ← Bap.Emu.thread current
    let group := (((← current.taskTable.get).find? thread).map (·.group)).getD thread
    let writer := (← writers.get).get? thread
    writers.modify (·.erase thread)
    let registers ← profile.registers.mapM fun (name, width) => do pure (name, ← readRegister current name width)
    visits.modify (·.push { thread, group, state := profile.decode (← readState current profile.state), writer, registers })
    -- A state on the stack is watched where it is, which is where the next round writes it.
    if profile.state matches .relative .. then
      if let some (address, size) := ← stateAddress current profile.state then
        if size > 0 then watchAt address size
  pure { profile, visits, hook, watch }

/-- Stops noting. -/
def Recorder.detach (emu : Emu) (recorder : Recorder) : IO Unit := do
  Bap.Emu.removeHook emu recorder.hook
  if let some (hook, _) := ← recorder.watch.get then Bap.Emu.removeHook emu hook

/-- What assigned the next state in a round: the instruction, whether it did so on a condition, as a `csel`, a `cmov` or a store that
only happens on one, and what that condition read. -/
structure Assignment where
  pc : Nat
  conditional : Bool
  condition : List String
  deriving DecidableEq, Repr

/-- Of a program that writes a register, or of one that stores when the state is in memory, how it does: whether on a condition, and the
variables that the condition reads. None if it doesn't write it. -/
partial def assignmentIn (program : Bil.Program) (register : Option String) : Option (Bool × List String) :=
  let names (exp : Bil.Exp) : List String := ((Bil.freeVars exp).map (·.name)).eraseDups
  let rec iteCondition : Bil.Exp → Option Bil.Exp
    | .ite condition _ _ => some condition
    | .letIn _ value body => (iteCondition body).or (iteCondition value)
    | .cast _ _ value | .extract _ _ value | .un _ value => iteCondition value
    | .store _ _ value _ _ => iteCondition value
    | _ => none
  let rec stores : Bil.Exp → Bool
    | .store .. => true
    | .letIn _ value body => stores value || stores body
    | _ => false
  let rec find (statements : List Bil.Stmt) (guard : Option Bil.Exp) : Option (Bool × List String) :=
    statements.foldr (init := none) fun statement found =>
      let here : Option (Bool × List String) := match statement with
        | .move var value =>
          let writes := match register with
            | some name => var.name == name
            | none => stores value
          if !writes then none
          else match guard, iteCondition value with
            | some condition, _ => some (true, names condition)
            | none, some condition => some (true, names condition)
            | none, none => some (false, [])
        | .ifElse condition yes no => (find yes (some condition)).or (find no (some condition))
        | .while _ body => find body guard
        | _ => none
      -- The last that writes it is what the round leaves.
      found.or here
  find program none

/-- The register that a program stores, of one that stores what a register holds, as a store of a state that a `csel` chose does. -/
partial def storedRegister (program : Bil.Program) : Option String :=
  let rec ofValue : Bil.Exp → Option String
    | .var var => some var.name
    | .cast _ _ value | .extract _ _ value => ofValue value
    | _ => none
  let rec inStore : Bil.Exp → Option String
    | .store _ _ value _ _ => ofValue value
    | .letIn _ value body => (inStore body).or (inStore value)
    | _ => none
  program.findSome? fun statement => match statement with
    | .move _ value => inStore value
    | _ => none

/-- The instruction of a round that last wrote a state in a register, from the end of the round, by the code of what it ran. -/
private def lastWriter (round : Array Journal.Executed) (register : String) (programOf : Nat → Option Bil.Program) : Option Nat := Id.run do
  for entry in round.reverse do
    if let some program := programOf entry.pc then
      if (assignmentIn program (some register)).isSome then return some entry.pc
  pure none

/-- Bytes of what a decision read that were marked, as they were: of a register from the least significant, and of memory from its
address up. -/
structure Read where
  place : Place
  bytes : List (Nat × UInt8)
  deriving DecidableEq, Repr

/-- What chose where a round went: the last branch of its handler on what depends on something marked, and what that came from. -/
structure Predicate where
  pc : Nat
  sources : List (String × Option Nat)
  /-- What it was decided by as it ran: where a jump went, what a condition was, or what a conditional assignment chose. -/
  value : Option Nat := none
  /-- What it read that was marked, with what each byte was. -/
  reads : List Read := []
  deriving DecidableEq, Repr

/-- A round of the machine: the state that it was in and the one that it left, with what its handler was, when there is a journal of it. -/
structure Transition where
  thread : ThreadId
  group : Nat
  /-- Which visit of its thread this was, from 0. -/
  index : Nat
  state : Nat
  next : Option Nat
  handler : Option Nat := none
  /-- The last instruction of the round before its thread came back to the dispatcher. -/
  exit : Option Nat := none
  /-- How many instructions the round ran, and when it started and ended, in those of the journal. -/
  instructions : Option Nat := none
  span : Option (Nat × Nat) := none
  services : List String := []
  /-- What each service was asked, in order: the inputs of what the host or the kernel did for the round. -/
  serviceInputs : List (String × List Nat) := []
  calls : List Nat := []
  /-- What assigned the next state, if that is known: by a write that was seen, of a state in memory, or by the code of the round's
  instructions, of one in a register. -/
  assignment : Option Assignment := none
  /-- Whether its handler's own code, from where it started, ran a branch on a condition, outside the dispatcher's: none where that
  isn't known, without a journal of the round or the code of what it ran. -/
  branched : Option Bool := none
  predicate : Option Predicate := none
  /-- What the registers of the profile held as the round started, and as it ended, when its thread came back to the dispatcher. -/
  registers : List (String × Nat) := []
  registersAfter : Option (List (String × Nat)) := none
  deriving Repr

/-- All the rounds of one state. -/
structure Handler where
  state : Nat
  name : Option String
  /-- Where it started and where its rounds were last, each as often as it was. -/
  entries : List Nat
  exits : List Nat
  runs : Nat
  fewest : Nat
  most : Nat
  services : List String
  calls : List Nat
  /-- The states that came after it. -/
  nexts : List Nat
  deriving Repr

/-- States that came round again in the same order, in a thread. -/
structure Cycle where
  thread : ThreadId
  states : List Nat
  repeats : Nat
  /-- The visit that it starts at. -/
  first : Nat
  deriving DecidableEq, Repr

structure Dispatcher where
  entry : Nat
  state : StateLocation
  transitions : List Transition
  /-- How often each state went to each. -/
  graph : List (Nat × Nat × Nat)
  handlers : List Handler
  cycles : List Cycle
  /-- What every round runs, which is the dispatcher's own code, as far as the rounds say. -/
  dispatch : List Nat
  /-- Whether a journal of all the visits was there to say what the handlers were. -/
  complete : Bool
  deriving Repr

/-- Whether the states are what a cycle says that they are, each of its times round. -/
def Cycle.holds (states : Array Nat) (cycle : Cycle) : Bool :=
  cycle.repeats ≥ 2 && !cycle.states.isEmpty &&
    (List.range cycle.repeats).all fun round => (List.range cycle.states.length).all fun offset =>
      states[cycle.first + round * cycle.states.length + offset]? == cycle.states[offset]?

/-- What the search finds, before what it found is checked. -/
private def cyclesFound (thread : ThreadId) (states : Array Nat) (longest : Nat) : List Cycle := Id.run do
  let mut found : Array Cycle := #[]
  let mut at_ := 0
  let mut fuel := states.size + 1
  while at_ < states.size && fuel > 0 do
    fuel := fuel - 1
    let mut best : Option (Nat × Nat) := none
    for period in List.range (min longest (states.size - at_)) do
      let period := period + 1
      let mut repeats := 1
      while at_ + (repeats + 1) * period ≤ states.size &&
          (List.range period).all (fun offset => states[at_ + repeats * period + offset]! == states[at_ + offset]!) do
        repeats := repeats + 1
      if repeats ≥ 2 then
        match best with
        | some (p, r) => if repeats * period > p * r then best := some (period, repeats)
        | none => best := some (period, repeats)
    match best with
    | some (period, repeats) =>
      found := found.push { thread, states := (states.extract at_ (at_ + period)).toList, repeats, first := at_ }
      at_ := at_ + period * repeats
    | none => at_ := at_ + 1
  pure found.toList

/-- Runs of states that repeat, by the shortest period that covers the most: only what `Cycle.holds` of, which is proved. -/
def cyclesOf (thread : ThreadId) (states : Array Nat) (longest : Nat := 32) : List Cycle :=
  (cyclesFound thread states longest).filter (·.holds states)

/-- Whether an instruction compares something with this value, as a chain of compares that dispatches does for the state that it finds. -/
private partial def comparesWith (value : Nat) : Bil.Program → Bool
  | [] => false
  | stmt :: rest =>
    let rec inExp : Bil.Exp → Bool
      | .bin op left right =>
        let constant := match right with
          | .int bits => bits.toNat == value
          | _ => false
        ((op == .sub || op == .eq || op == .neq) && constant) || inExp left || inExp right
      | .un _ value | .cast _ _ value | .extract _ _ value => inExp value
      | .letIn _ value body => inExp value || inExp body
      | .ite condition yes no => inExp condition || inExp yes || inExp no
      | .concat left right => inExp left || inExp right
      | _ => false
    let here := match stmt with
      | .move _ exp => inExp exp
      | .ifElse condition yes no => inExp condition || comparesWith value yes || comparesWith value no
      | _ => false
    here || comparesWith value rest

/-- Whether an instruction may go two ways. -/
private partial def branches : Bil.Program → Bool
  | [] => false
  | .ifElse _ _ _ :: _ => true
  | .jmp (.ite ..) :: _ => true
  | _ :: rest => branches rest

/-- What has been seen, in the order that it was first: a list for that and a set for whether it has. -/
private structure Seen (α : Type) [BEq α] [Hashable α] where
  order : Array α := #[]
  known : Std.HashSet α := {}

private def Seen.add {α : Type} [BEq α] [Hashable α] (seen : Seen α) (value : α) : Seen α :=
  if seen.known.contains value then seen else { order := seen.order.push value, known := seen.known.insert value }

/-- The first of what is sorted by `key` whose key isn't below `bound`. -/
private def firstFrom {α : Type} [Inhabited α] (items : Array α) (key : α → Nat) (bound : Nat) : Nat := Id.run do
  let mut low := 0
  let mut high := items.size
  while low < high do
    let middle := (low + high) / 2
    if key items[middle]! < bound then low := middle + 1 else high := middle
  pure low

/-- What is said of all the rounds of a state, as they come. -/
private structure Gathered where
  entries : Seen Nat := {}
  exits : Seen Nat := {}
  runs : Nat := 0
  sizes : Array Nat := #[]
  services : Seen String := {}
  calls : Seen Nat := {}
  nexts : Seen Nat := {}

/-- What the visits say of the dispatcher, and with a journal of the same run, what each round was. A journal whose oldest has gone
can't say which round is which, and then only the states are there. It goes through each visit, instruction and event a few times, each
time looking it up in a table, so that it takes as long as there are of them. -/
def recover (profile : Profile) (visits : Array Visit) (record : Option Journal.Journal.Record := none)
    (programOf : Nat → Option Bil.Program := fun _ => none) : Dispatcher := Id.run do
  -- The visits of each thread, and the threads in the order that they first came.
  let mut threads : Seen ThreadId := {}
  let mut byThread : Std.HashMap ThreadId (Array Visit) := {}
  for visit in visits do
    threads := threads.add visit.thread
    -- In place: what is in a table and is taken out to be changed would otherwise be copied each time.
    byThread := byThread.alter visit.thread fun known => some ((known.getD #[]).push visit)
  let ofThread (thread : ThreadId) : Array Visit := byThread.getD thread #[]
  -- What each thread ran, and the calls and services of each, in the order that they were, which is that of when.
  let mut histories : Std.HashMap ThreadId (Array Journal.Executed) := {}
  let mut happened : Std.HashMap ThreadId (Array Journal.Event) := {}
  if let some record := record then
    for entry in record.history do
      if byThread.contains entry.thread then
        histories := histories.alter entry.thread fun known => some ((known.getD #[]).push entry)
    for event in record.events do
      match event with
      | .service .. | .call .. => happened := happened.alter event.thread fun known => some ((known.getD #[]).push event)
      | _ => pure ()
  -- Each thread's rounds, by where in its own instructions each visit is.
  let mut segments : Std.HashMap ThreadId (Array (Array Journal.Executed)) := {}
  let mut aligned := true
  if record.isSome then
    for thread in threads.order do
      let mine := histories.getD thread #[]
      let mut starts : Array Nat := #[]
      for position in List.range mine.size do
        if mine[position]!.pc == profile.dispatcher then starts := starts.push position
      if starts.size != (ofThread thread).size then aligned := false
      else
        let bounds := starts.push mine.size
        segments := segments.insert thread ((List.range starts.size).toArray.map fun k => mine.extract bounds[k]! bounds[k + 1]!)
  let complete := record.isSome && (record.map (·.droppedHistory == 0)).getD false && aligned
  -- Which states' rounds run each instruction: what only one does is its handler's, but for the last compare of a chain that finds it, which
  -- only it gets to, and the branch after that. Only rounds that another follows count, as the last may not have finished.
  let mut owners : Std.HashMap Nat (List Nat) := {}
  for thread in threads.order do
    let mine := ofThread thread
    for (round, k) in (segments.getD thread #[]).zipIdx do
      if k + 1 < mine.size then
        let state := mine[k]!.state
        for entry in round do
          let states := owners.getD entry.pc []
          unless states.contains state do owners := owners.insert entry.pc (state :: states)
  let mut dispatch : Seen Nat := {}
  for thread in threads.order do
    let mine := ofThread thread
    for (round, k) in (segments.getD thread #[]).zipIdx do
      if k + 1 < mine.size then
        for entry in round do
          if (owners.getD entry.pc []).length ≥ 2 then dispatch := dispatch.add entry.pc
  let entryOf (state : Nat) (round : Array Journal.Executed) : Option Nat := Id.run do
    let mut previousCompared := false
    for entry in round.toList.drop 1 do
      let pc := entry.pc
      let inside := match profile.dispatchRange with
        | some (low, high) => low ≤ pc && pc < high
        | none => (owners.getD pc []) != [state]
      if inside then
        previousCompared := false
      else if profile.dispatchRange.isNone && ((programOf pc).any (comparesWith state) || (previousCompared && (programOf pc).any branches)) then
        previousCompared := true
      else
        return some pc
    pure none
  -- The rounds, with what happened in each: what a thread's events are in order of when, which a round is a stretch of.
  let mut transitions : Array Transition := #[]
  let mut graph : Seen (Nat × Nat) := {}
  let mut edges : Std.HashMap (Nat × Nat) Nat := {}
  let mut states : Seen Nat := {}
  let mut gathered : Std.HashMap Nat Gathered := {}
  for thread in threads.order do
    let mine := ofThread thread
    let rounds := segments.get? thread
    let events := happened.getD thread #[]
    for k in List.range mine.size do
      let visit := mine[k]!
      let next := (mine[k + 1]?).map (·.state)
      let round := rounds.bind (·[k]?)
      let span := round.bind fun round => match round[0]?, round.back? with
        | some first, some last => some (first.seq, last.seq + 1)
        | _, _ => none
      let (services, serviceInputs, calls) := match span with
        | some (first, stop) => Id.run do
          let mut services : Array String := #[]
          let mut inputs : Array (String × List Nat) := #[]
          let mut calls : Array Nat := #[]
          let mut at_ := firstFrom events Journal.Event.seq first
          while at_ < events.size && events[at_]!.seq < stop do
            match events[at_]! with
            | .service _ _ _ _ label args _ _ =>
              services := services.push label
              inputs := inputs.push (label, args)
            | .call _ _ frame => calls := calls.push frame.callee
            | _ => pure ()
            at_ := at_ + 1
          pure (services.toList, inputs.toList, calls.toList)
        | none => ([], [], [])
      -- What assigned the state that the next visit has.
      let register := match profile.state with
        | .register name _ => some name
        | _ => none
      let writer := match register with
        | some name => if next.isSome then round.bind (lastWriter · name programOf) else none
        | none => (mine[k + 1]?).bind (·.writer)
      let assignment := writer.map fun pc =>
        match (programOf pc).bind (assignmentIn · register) with
        | some (true, condition) => { pc, conditional := true, condition : Assignment }
        | _ =>
          -- A store of what a register holds: what chose that, earlier in the round, as a `csel` before a `str` does.
          let chosen : Option (List String) := match register, (programOf pc).bind storedRegister, round with
            | none, some source, some round => Id.run do
              let entries := round.toList
              let before := (entries.reverse.dropWhile (·.pc != pc)).drop 1
              for entry in before do
                if let some program := programOf entry.pc then
                  if let some (conditional, condition) := assignmentIn program (some source) then
                    return if conditional then some condition else none
              pure none
            | _, _, _ => none
          match chosen with
          | some condition => { pc, conditional := true, condition }
          | none => { pc, conditional := false, condition := [] }
      let handler := round.bind (entryOf visit.state)
      let inDispatch (pc : Nat) : Bool := match profile.dispatchRange with
        | some (low, high) => low ≤ pc && pc < high
        | none => dispatch.known.contains pc
      let branched := match round, handler with
        | some round, some entry =>
          let own := ((round.toList.drop 1).dropWhile (·.pc != entry)).filter (!inDispatch ·.pc)
          if own.all fun executed => (programOf executed.pc).isSome then
            some (own.any fun executed => (programOf executed.pc).any branches)
          else none
        | _, _ => none
      let transition : Transition := {
        thread, group := visit.group, index := k, state := visit.state, next, handler, branched
        exit := if next.isSome then round.bind (·.back?.map (·.pc)) else none
        instructions := if next.isSome then round.map (·.size) else none
        span, services, serviceInputs, calls, assignment
        registers := visit.registers, registersAfter := (mine[k + 1]?).map (·.registers) }
      transitions := transitions.push transition
      states := states.add visit.state
      if let some to := next then
        graph := graph.add (visit.state, to)
        edges := edges.insert (visit.state, to) (edges.getD (visit.state, to) 0 + 1)
      gathered := gathered.alter visit.state fun known => some (
        let known := known.getD {}
        { entries := (transition.handler.map known.entries.add).getD known.entries
          exits := (transition.exit.map known.exits.add).getD known.exits
          runs := known.runs + 1
          sizes := (transition.instructions.map known.sizes.push).getD known.sizes
          services := services.foldl Seen.add known.services
          calls := calls.foldl Seen.add known.calls
          nexts := (next.map known.nexts.add).getD known.nexts })
  let handlers := states.order.toList.map fun state =>
    let known := gathered.getD state {}
    { state, name := profile.names.lookup state
      entries := known.entries.order.toList, exits := known.exits.order.toList, runs := known.runs
      fewest := known.sizes.foldl min (known.sizes[0]?.getD 0), most := known.sizes.foldl max 0
      services := known.services.order.toList, calls := known.calls.order.toList, nexts := known.nexts.order.toList : Handler }
  let cycles := threads.order.toList.flatMap fun thread => cyclesOf thread ((ofThread thread).map (·.state))
  pure { entry := profile.dispatcher, state := profile.state, transitions := transitions.toList
         graph := graph.order.toList.map fun (from_, to) => (from_, to, edges.getD (from_, to) 0)
         handlers, cycles, dispatch := dispatch.order.toList, complete }

/-- `recover`, with the code of the instructions from the emulator as it is now, to tell the compares of the dispatcher from a handler. -/
def recoverIn (emu : Emu) (profile : Profile) (visits : Array Visit) (record : Option Journal.Journal.Record := none) : IO Dispatcher := do
  let mut programs : Std.HashMap Nat Bil.Program := {}
  let mut looked : Std.HashSet Nat := {}
  if let some record := record then
    for entry in record.history do
      unless looked.contains entry.pc do
        looked := looked.insert entry.pc
        if let some program := ← Bap.Emu.programAt emu entry.pc then
          programs := programs.insert entry.pc program
  -- And what wrote a state in memory, which a journal needn't have been there for.
  for visit in visits do
    if let some pc := visit.writer then
      unless looked.contains pc do
        looked := looked.insert pc
        if let some program := ← Bap.Emu.programAt emu pc then
          programs := programs.insert pc program
  pure (recover profile visits record (programs.get? ·))

/-- The binary search of what is sorted by its key, for the last that is below a bound. -/
private def lastBelow (items : Array (Nat × Node)) (bound : Nat) : Option Nat := Id.run do
  let mut low := 0
  let mut high := items.size
  while low < high do
    let middle := (low + high) / 2
    if items[middle]!.1 < bound then low := middle + 1 else high := middle
  pure (if low == 0 then none else some (low - 1))

/-- What a node of a decision says of it: where it is, what it comes from, what it was, and what it read that was marked, as that was. -/
private def predicateOf (tracker : Tracker) (node : Node) : IO Predicate := do
  let sources ← tracker.sourcesOf (nodeTag node.id 0)
  let value := if node.values.isEmpty then none else some (node.values.toList.foldr (fun byte value => value * 256 + byte.toNat) 0)
  -- What it read, by the node that each byte was of, in the order that they come.
  let mut order : Array Nat := #[]
  let mut bytes : Std.HashMap Nat (Std.HashMap Nat UInt8) := {}
  let mut places : Std.HashMap Nat Place := {}
  for inputs in node.inputs do
    for input in inputs do
      if !input.tag.isNode then continue
      let id := input.tag.node
      let some read ← tracker.node? id | continue
      let some byte := read.valueAt input.tag.byte | continue
      unless places.contains id do
        order := order.push id
        places := places.insert id read.place
      bytes := bytes.alter id fun known => some ((known.getD {}).insert input.tag.byte byte)
  let reads := order.toList.map fun id =>
    let known := (bytes.getD id {}).toArray.qsort (·.1 < ·.1)
    { place := places.getD id .control, bytes := known.toList : Read }
  pure { pc := node.pc, value, reads
         sources := sources.filterMap fun (source, byte, _) => match source.kind with
           | .source label offset => some (label, offset.map (· + byte))
           | _ => none }

/-- Each round with what decided it, by a tracker that started with the journal: the last branch of its handler, outside the dispatcher's
code, on what depends on something marked, and the sources of that, or else, of a round that chose its next state without a branch, as a
`csel` does, what that chose by; each with what it was decided by and what it read, as that was. A round whose handler decided on nothing
marked has none. -/
def withPredicates (dispatcher : Dispatcher) (tracker : Tracker) (journal : Journal.Journal) : IO Dispatcher := do
  let ahead := (← tracker.insn.get) - (← journal.seq.get)
  let dispatch : Std.HashSet Nat := dispatcher.dispatch.foldl (·.insert ·) {}
  -- The branches of each thread outside the dispatcher, in the order that they were, gathered once.
  let mut byThread : Std.HashMap ThreadId (Array (Nat × Node)) := {}
  -- And the nodes of what assigned a state on a condition, by thread and where.
  let conditional : Std.HashSet Nat := dispatcher.transitions.foldl (init := {}) fun set transition =>
    match transition.assignment with
    | some assignment => if assignment.conditional then set.insert assignment.pc else set
    | none => set
  let mut assigning : Std.HashMap (ThreadId × Nat) (Array (Nat × Node)) := {}
  for node in ← tracker.nodes.get do
    if node.kind matches .branch _ && !dispatch.contains node.pc then
      byThread := byThread.alter node.thread fun known => some ((known.getD #[]).push (node.insn, node))
    if conditional.contains node.pc then
      assigning := assigning.alter (node.thread, node.pc) fun known => some ((known.getD #[]).push (node.insn, node))
  let mut transitions : Array Transition := #[]
  for transition in dispatcher.transitions do
    let predicate ← match transition.span with
      | some (first, last) =>
        let mine := byThread.getD transition.thread #[]
        match lastBelow mine (last + ahead) with
        | some position =>
          let (insn, node) := mine[position]!
          if insn < first + ahead then pure none else pure (some (← predicateOf tracker node))
        | none => pure none
      | none => pure none
    -- What chose the next state without a branch, in the same round.
    let predicate ← match predicate, transition.assignment, transition.span with
      | none, some assignment, some (first, last) =>
        if !assignment.conditional then pure none else
        match lastBelow (assigning.getD (transition.thread, assignment.pc) #[]) (last + ahead) with
        | some position =>
          let (insn, node) := (assigning.getD (transition.thread, assignment.pc) #[])[position]!
          if insn < first + ahead then pure none else pure (some (← predicateOf tracker node))
        | none => pure none
      | found, _, _ => pure found
    transitions := transitions.push { transition with predicate }
  pure { dispatcher with transitions := transitions.toList }

/-- What one state of a flattened machine does, over all its rounds: the services it asks of the kernel or host, and the targets it
calls, each once, in the order they were first asked or called. -/
structure StateEffects where
  state : Nat
  name : Option String
  services : List String
  calls : List Nat
  deriving DecidableEq, Repr

/-- An inventory of what a flattened machine does, from its rounds, without running it again: every service it asks of the kernel or
host and every target it calls, each once, in first-seen order, and the same for each state on its own — the effects a dispatcher hides
behind its rounds. The memory it writes beyond the state itself is the Contract's to say, by running a round against a replacement. -/
structure Effects where
  services : List String
  calls : List Nat
  byState : List StateEffects
  deriving DecidableEq, Repr

/-- The effects of a dispatcher: what each state asks and calls, and all of it together. -/
def Dispatcher.effects (dispatcher : Dispatcher) : Effects := Id.run do
  let names : Std.HashMap Nat (Option String) :=
    dispatcher.handlers.foldl (fun names handler => names.insert handler.state handler.name) {}
  -- The states in the order their rounds first came, so the inventory reads as the machine ran.
  let mut order : List Nat := []
  let mut perState : Std.HashMap Nat StateEffects := {}
  for transition in dispatcher.transitions do
    let state := transition.state
    if !perState.contains state then order := state :: order
    let current := perState.getD state { state, name := names.getD state none, services := [], calls := [] }
    perState := perState.insert state
      { current with
        services := (current.services ++ transition.services).eraseDups
        calls := (current.calls ++ transition.calls).eraseDups }
  let byState := order.reverse.filterMap (perState[·]?)
  pure {
    services := (byState.flatMap (·.services)).eraseDups
    calls := (byState.flatMap (·.calls)).eraseDups
    byState
  }

/-- How the rounds of a state chose the state after them, as far as they say. -/
inductive EdgeKind where
  /-- Without a branch of its handler or a condition, to the one state that every round of it went to. -/
  | direct
  /-- On a condition: a branch of its handler, a conditional assignment, or something marked that decided it. -/
  | conditional
  /-- Without a branch or a condition, to more than one state, as by a table: computed. -/
  | indirect
  /-- How isn't known, as the rounds have no journal or the code of what they ran isn't there: a round went there, but that it is the
  only way that it goes isn't said. -/
  | unresolved
  deriving DecidableEq, Repr

/-- A way from a state to the next: where to, or nowhere known, for an alternative that no round took, and how many rounds took it. -/
structure Edge where
  source : Nat
  target : Option Nat
  kind : EdgeKind
  count : Nat
  deriving DecidableEq, Repr

/-- The control flow that a flattened machine hides behind its dispatcher, of states rather than blocks: the state of its first round, the
states, the ways from each to the next, and where the rounds ended. -/
structure Cfg where
  entry : Option Nat
  states : List Nat
  edges : List Edge
  exits : List Nat
  deriving DecidableEq, Repr

/-- The graph of the states, from the rounds: an edge is direct only where every round of its state is known to have chosen the next one
without a branch or a condition and all chose the same. A state that chose on a condition and went one way keeps the alternative that no
round took, and one that computed where to go keeps that it may go elsewhere, as an edge to nowhere known; an edge whose rounds don't say
how they chose is unresolved, never direct. -/
def Dispatcher.cfg (dispatcher : Dispatcher) : Cfg :=
  let edges := dispatcher.handlers.flatMap fun handler =>
    let source := handler.state
    let rounds := dispatcher.transitions.filter fun transition => transition.state == source && transition.next.isSome
    let targets := dispatcher.graph.filter (·.1 == source)
    let conditional := rounds.any fun transition =>
      transition.branched == some true || transition.assignment.any (·.conditional) || transition.predicate.isSome
    let known := rounds.all fun transition => transition.branched.isSome && transition.assignment.isSome
    let kind : EdgeKind :=
      if conditional then .conditional else if !known then .unresolved else if targets.length > 1 then .indirect else .direct
    let seen := targets.map fun (_, to, count) => { source, target := some to, kind, count : Edge }
    let open_ := { source, target := none, kind, count := 0 : Edge }
    if targets.isEmpty then []
    else match kind with
      | .conditional => if targets.length == 1 then seen ++ [open_] else seen
      | .indirect => seen ++ [open_]
      | _ => seen
  { entry := dispatcher.transitions.head?.map (·.state)
    states := dispatcher.handlers.map (·.state)
    edges
    exits := (dispatcher.transitions.filter (·.next.isNone)).map (·.state) |>.eraseDups }

private def hex (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

def Dispatcher.text (dispatcher : Dispatcher) : String :=
  let edges := dispatcher.graph.map fun (from_, to, count) => s!"  {from_} -> {to} ({count})"
  let handlers := dispatcher.handlers.map fun handler =>
    let name := handler.name.map (s!" {·}") |>.getD ""
    s!"  {handler.state}{name}: at {handler.entries.map hex}, {handler.runs} runs of {handler.fewest} to {handler.most} instructions, services {handler.services}, next {handler.nexts}"
  let cycles := dispatcher.cycles.map fun cycle => s!"  thread {cycle.thread}: {cycle.states} {cycle.repeats} times from visit {cycle.first}"
  s!"dispatcher {hex dispatcher.entry}\ntransitions\n{"\n".intercalate edges}\nhandlers\n{"\n".intercalate handlers}\ncycles\n{"\n".intercalate cycles}"

end Bap.Analysis.Cff
