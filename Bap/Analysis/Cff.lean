import Bap.Analysis.Journal
import Bap.Analysis.DynamicTaint

/-! Flattened control flow as it ran: a dispatcher that each round of the machine goes through, with a state that says which handler
comes next. What is particular to a target, where its dispatcher is and where its state is kept, is a `Profile`, and the rest is the
same for all. A `Recorder` notes the state at each visit of the dispatcher, which is one instruction that has a hook, so that the rest
runs as it always does. With a journal of the same run, `recover` also says what each handler was: where it starts, which is where its
round first runs what no other round does, how long it ran, and what it asked of the kernel; and a tracker says what decided each
transition.

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

/-- What a state location holds now, in the thread that runs, as it is kept. -/
def readState (emu : Emu) (location : StateLocation) : IO Nat := do
  let number (bytes : ByteArray) : Nat :=
    let ordered := if emu.config.endian == .big then bytes.toList else bytes.toList.reverse
    ordered.foldl (fun value byte => value * 256 + byte.toNat) 0
  let registerValue (name : String) (width : Nat) : IO Nat := do
    match Value.asBits (← Bap.Emu.reg emu ⟨name, .imm width, 0, false⟩) with
    | .ok bits => pure bits.2.toNat
    | .error error => throw <| IO.userError s!"the state in {name}: {error}"
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
  deriving DecidableEq, Repr, Inhabited

structure Recorder where
  profile : Profile
  visits : IO.Ref (Array Visit)
  hook : Bap.Emu.HookId

/-- Notes the state each time a thread comes to the dispatcher, from here on. -/
def Recorder.attach (emu : Emu) (profile : Profile) : IO Recorder := do
  let visits ← IO.mkRef #[]
  let hook ← Bap.Emu.onCode emu (profile.dispatcher, profile.dispatcher) fun current _ => do
    let thread ← Bap.Emu.thread current
    let group := (((← current.taskTable.get).find? thread).map (·.group)).getD thread
    visits.modify (·.push { thread, group, state := profile.decode (← readState current profile.state) })
  pure { profile, visits, hook }

/-- Stops noting. -/
def Recorder.detach (emu : Emu) (recorder : Recorder) : IO Unit := Bap.Emu.removeHook emu recorder.hook

/-- What chose where a round went: the last branch of its handler on what depends on something marked, and what that came from. -/
structure Predicate where
  pc : Nat
  sources : List (String × Option Nat)
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
  calls : List Nat := []
  predicate : Option Predicate := none
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
  let mut found : List Cycle := []
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
      found := found ++ [{ thread, states := (states.extract at_ (at_ + period)).toList, repeats, first := at_ }]
      at_ := at_ + period * repeats
    | none => at_ := at_ + 1
  pure found

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

private def counted (values : List Nat) : List Nat :=
  values.foldl (fun out value => if out.contains value then out else out ++ [value]) []

/-- What the visits say of the dispatcher, and with a journal of the same run, what each round was. A journal whose oldest has gone
can't say which round is which, and then only the states are there. -/
def recover (profile : Profile) (visits : Array Visit) (record : Option Journal.Journal.Record := none)
    (programOf : Nat → Option Bil.Program := fun _ => none) : Dispatcher := Id.run do
  let threads := visits.foldl (fun order visit => if order.contains visit.thread then order else order.push visit.thread) #[]
  -- Each thread's rounds, by where in its own instructions each visit is.
  let ofThread (thread : ThreadId) : Array Visit := visits.filter (·.thread == thread)
  let segmentsOf (thread : ThreadId) : Option (Array (Array Journal.Executed)) := do
    let record ← record
    let mine := record.history.filter (·.thread == thread)
    let starts := (List.range mine.size).filter fun position => mine[position]!.pc == profile.dispatcher
    if starts.length != (ofThread thread).size then none
    else
      let bounds := starts.toArray.push mine.size
      some ((List.range starts.length).toArray.map fun k => mine.extract bounds[k]! bounds[k + 1]!)
  let segments := threads.map fun thread => (thread, segmentsOf thread)
  let complete := record.isSome && (record.map (·.droppedHistory == 0)).getD false && segments.all (·.2.isSome)
  -- What every round that was followed by another runs.
  let rounds := segments.toList.flatMap fun (thread, found) =>
    match found with
    | some found => (List.range found.size).filterMap fun k => if k + 1 < (ofThread thread).size then found[k]? else none
    | none => []
  -- Which states' rounds run each instruction: what only one does is its handler's, but for the last compare of a chain that finds it, which
  -- only it gets to, and the branch after that.
  let stateOfRound (thread : ThreadId) (k : Nat) : Nat := ((ofThread thread)[k]?.map (·.state)).getD 0
  let owners : Std.HashMap Nat (List Nat) := segments.foldl (init := {}) fun table (thread, found) =>
    match found with
    | some found => (List.range found.size).foldl (init := table) fun table k =>
        if k + 1 < (ofThread thread).size then
          found[k]!.foldl (init := table) fun table entry =>
            let states := table.getD entry.pc []
            let state := stateOfRound thread k
            table.insert entry.pc (if states.contains state then states else state :: states)
        else table
    | none => table
  let common : List Nat := counted (rounds.flatMap fun round => round.toList.map (·.pc) |>.filter fun pc => (owners.getD pc []).length ≥ 2)
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
  let mut transitions : List Transition := []
  for thread in threads do
    let mine := ofThread thread
    let found := (segments.find? (·.1 == thread)).bind (·.2)
    for k in List.range mine.size do
      let visit := mine[k]!
      let next := (mine[k + 1]?).map (·.state)
      let round := found.bind (·[k]?)
      let services := match record, round with
        | some record, some round =>
          match round[0]?, round.back? with
          | some first, some last => record.events.toList.filterMap fun event => match event with
              | .service seq t _ _ label _ _ _ => if t == thread && first.seq ≤ seq && seq ≤ last.seq then some label else none
              | _ => none
          | _, _ => []
        | _, _ => []
      let calls := match record, round with
        | some record, some round =>
          match round[0]?, round.back? with
          | some first, some last => record.events.toList.filterMap fun event => match event with
              | .call seq t frame => if t == thread && first.seq ≤ seq && seq ≤ last.seq then some frame.callee else none
              | _ => none
          | _, _ => []
        | _, _ => []
      transitions := transitions ++ [{
        thread, group := visit.group, index := k, state := visit.state, next
        handler := round.bind (entryOf visit.state)
        exit := if next.isSome then round.bind (·.back?.map (·.pc)) else none
        instructions := (if next.isSome then round.map (·.size) else none)
        span := round.bind fun round => match round[0]?, round.back? with
          | some first, some last => some (first.seq, last.seq + 1)
          | _, _ => none
        services, calls }]
  let pairs := transitions.filterMap fun transition => transition.next.map (transition.state, ·)
  let graph := (counted (pairs.map fun (from_, to) => from_ * 2 ^ 64 + to)).map fun key =>
    (key / 2 ^ 64, key % 2 ^ 64, pairs.countP (· == (key / 2 ^ 64, key % 2 ^ 64)))
  let states := counted (transitions.map (·.state))
  let handlers := states.map fun state =>
    let mine := transitions.filter (·.state == state)
    let sizes := mine.filterMap (·.instructions)
    { state, name := profile.names.lookup state
      entries := counted (mine.filterMap (·.handler))
      exits := counted (mine.filterMap (·.exit))
      runs := mine.length
      fewest := sizes.foldl min (sizes.headD 0), most := sizes.foldl max 0
      services := counted' (mine.flatMap (·.services))
      calls := counted (mine.flatMap (·.calls))
      nexts := counted (mine.filterMap (·.next)) : Handler }
  let cycles := threads.toList.flatMap fun thread => cyclesOf thread ((ofThread thread).map (·.state))
  pure { entry := profile.dispatcher, state := profile.state, transitions, graph, handlers, cycles, dispatch := common, complete }
where
  counted' (labels : List String) : List String :=
    labels.foldl (fun out label => if out.contains label then out else out ++ [label]) []

/-- `recover`, with the code of the instructions from the emulator as it is now, to tell the compares of the dispatcher from a handler. -/
def recoverIn (emu : Emu) (profile : Profile) (visits : Array Visit) (record : Option Journal.Journal.Record := none) : IO Dispatcher := do
  let pcs : List Nat := match record with
    | some record => (record.history.toList.map Journal.Executed.pc).eraseDups
    | none => []
  let mut programs : Std.HashMap Nat Bil.Program := {}
  for pc in pcs do
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

/-- Each round with what decided it, by a tracker that started with the journal: the last branch of its handler, outside the dispatcher's
code, on what depends on something marked, and the sources of that. A round whose handler decided on nothing marked has none. -/
def withPredicates (dispatcher : Dispatcher) (tracker : Tracker) (journal : Journal.Journal) : IO Dispatcher := do
  let ahead := (← tracker.insn.get) - (← journal.seq.get)
  let nodes ← tracker.nodes.get
  -- The branches of each thread, in the order that they were.
  let branches := nodes.filter fun node => node.kind matches .branch _ && !dispatcher.dispatch.contains node.pc
  let mut transitions : List Transition := []
  for transition in dispatcher.transitions do
    let predicate ← match transition.span with
      | some (first, last) =>
        let mine := (branches.filter (·.thread == transition.thread)).map fun node => (node.insn, node)
        match lastBelow mine (last + ahead) with
        | some position =>
          let (insn, node) := mine[position]!
          if insn < first + ahead then pure none
          else
            let explanation ← tracker.explainTag (nodeTag node.id 0)
            pure (some { pc := node.pc, sources := explanation.sources.filterMap fun (source, byte, _) => match source.kind with
              | .source label offset => some (label, offset.map (· + byte))
              | _ => none : Predicate })
        | none => pure none
      | none => pure none
    transitions := transitions ++ [{ transition with predicate }]
  pure { dispatcher with transitions }

private def hex (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

def Dispatcher.text (dispatcher : Dispatcher) : String :=
  let edges := dispatcher.graph.map fun (from_, to, count) => s!"  {from_} -> {to} ({count})"
  let handlers := dispatcher.handlers.map fun handler =>
    let name := handler.name.map (s!" {·}") |>.getD ""
    s!"  {handler.state}{name}: at {handler.entries.map hex}, {handler.runs} runs of {handler.fewest} to {handler.most} instructions, services {handler.services}, next {handler.nexts}"
  let cycles := dispatcher.cycles.map fun cycle => s!"  thread {cycle.thread}: {cycle.states} {cycle.repeats} times from visit {cycle.first}"
  s!"dispatcher {hex dispatcher.entry}\ntransitions\n{"\n".intercalate edges}\nhandlers\n{"\n".intercalate handlers}\ncycles\n{"\n".intercalate cycles}"

end Bap.Analysis.Cff
