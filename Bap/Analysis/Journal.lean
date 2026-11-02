import Bap.Analysis.CallSites
import Bap.Emu.Tasks
import Bap.Linux.Wire

/-! What a run did, kept: each instruction of each thread, each call and return, and each call of a service. A frame pointer says
where a function was called from only if the function keeps one, and a stack of generated code keeps nothing of the sort, so
that a call stack here is what was seen to happen. An instruction is a call if it leaves where to come back to just after itself and jumps, whichever
way a target does that, and a call site in the middle of a block is one like any other, as this goes by the instruction. Coming back to a site ends that
call and those within it, which is how a `longjmp` goes. A jump into a function isn't a call: a tail call has no frame here, as it has none on a machine.

It runs one instruction at a time, without the JIT, as a `Tracker` does. The guest does the same as it would have.

`compare` says where two runs part, by thread and instruction, and what the first thing was that they were given differently. -/

namespace Bap.Analysis.Journal

open Bap.Emu (Emu ThreadId)

/-- A call that hasn't come back. -/
structure Frame where
  /-- The instruction that called. -/
  site : Nat
  callee : Nat
  /-- Where it comes back to. -/
  returnsTo : Nat
  /-- When it was called, in instructions of all threads. -/
  seq : Nat
  deriving DecidableEq, Repr, Inhabited

/-- An instruction as it ran: which of its thread's it was, and where. -/
structure Executed where
  seq : Nat
  thread : ThreadId
  /-- The process that it was of. -/
  group : Nat
  index : Nat
  pc : Nat
  deriving DecidableEq, Repr, Inhabited

inductive Event where
  | call (seq : Nat) (thread : ThreadId) (frame : Frame)
  /-- How far it went back: more than one if calls within it never came back. -/
  | ret (seq : Nat) (thread : ThreadId) (from_ to frames : Nat)
  /-- Something outside the guest served it: what that was, what it was asked, what it answered and the digest of what it left in memory, and its index among the thread's services. -/
  | service (seq : Nat) (thread : ThreadId) (index : Nat) (pc : Nat) (label : String) (args : List Nat) (result : Option Nat) (written : Nat)
  /-- The machine was put back to what it was before, by what this says, so that what it holds now has no writer in what was run since. -/
  | restored (seq : Nat) (thread : ThreadId) (label : String)
  deriving DecidableEq, Repr, Inhabited

def Event.seq : Event → Nat
  | .call seq .. | .ret seq .. | .service seq .. | .restored seq .. => seq

def Event.thread : Event → ThreadId
  | .call _ thread _ | .ret _ thread .. | .service _ thread .. | .restored _ thread _ => thread

structure Config where
  /-- How many instructions are kept, and how many events, of which the oldest half goes when they run out. -/
  instructions : Nat := 4000000
  events : Nat := 1000000
  /-- What a system call is called. -/
  describe : Nat → List Nat → IO String := fun number _ => pure s!"syscall {number}"

/-- A call that an instruction has just made, whose target isn't known until the thread gets there. -/
private structure Pending where
  site : Nat
  returnsTo : Nat
  seq : Nat
  deriving Inhabited

/-- What is known of a thread. -/
private structure ThreadState where
  /-- How many instructions and services have been seen. -/
  count : Nat := 0
  services : Nat := 0
  stack : List Frame := []
  sites : CallSites := {}
  pending : Option Pending := none
  last : Nat := 0
  group : Option Nat := none
  deriving Inhabited

structure Journal where
  emu : Emu
  config : Config
  history : IO.Ref (Array Executed)
  droppedHistory : IO.Ref Nat
  events : IO.Ref (Array Event)
  droppedEvents : IO.Ref Nat
  seq : IO.Ref Nat
  threads : IO.Ref (Std.HashMap ThreadId ThreadState)
  /-- The program of an instruction if it can call at all, by what it was made of: most can't, and then this is all it costs. -/
  jumping : IO.Ref (Std.HashMap Nat (ByteArray × Option Bil.Program))
  /-- A service in progress: what it was called, what it was asked, what it has left in memory so far and those that it interrupted. -/
  serving : IO.Ref (List (String × List Nat × Nat))
  /-- The checkpoint that this machine went on from, if it did, which isn't saved, as going on from one changes nothing of what it was. -/
  loadedFrom : IO.Ref (Option String)

namespace Journal

private def record (journal : Journal) (event : Event) : IO Unit := do
  journal.events.modify (·.push event)
  if (← journal.events.get).size > journal.config.events then
    let half := journal.config.events / 2
    journal.events.modify fun events => events.extract half events.size
    journal.droppedEvents.modify (· + half)

private partial def jumps : Bil.Program → Bool
  | [] => false
  | .jmp _ :: _ => true
  | .ifElse _ yes no :: rest => jumps yes || jumps no || jumps rest
  | .while _ body :: rest => jumps body || jumps rest
  | _ :: rest => jumps rest

private def programOf (journal : Journal) (pc : Nat) : IO (Option Bil.Program) := do
  let code ← Emu.codeAt journal.emu pc
  match (← journal.jumping.get)[pc]? with
  | some (bytes, program) => if bytes == code then return program
  | none => pure ()
  match ← Emu.programAt journal.emu pc with
  | some program =>
    let kept := if jumps program then some program else none
    journal.jumping.modify (·.insert pc (code, kept))
    pure kept
  | none => pure none

/-- What an instruction leaves that may be where it comes back to, on the way it goes in this state. -/
private partial def linkOf (pc : Nat) (env : Bil.Env) : Bil.Program → Option Nat × Bil.Env × Bool
  | [] => (none, env, false)
  | stmt :: rest =>
    let close (value : Bil.Exp) : Option Nat :=
      match Bil.evalExp env value with
      | .ok value =>
        match Value.asBits value with
        | .ok bits => if pc < bits.2.toNat && bits.2.toNat ≤ pc + 32 then some bits.2.toNat else none
        | .error _ => none
      | .error _ => none
    let keep (found : Option Nat) (next : Bil.Env) : Option Nat × Bil.Env × Bool :=
      let (later, env, jumped) := linkOf pc next rest
      (later.orElse fun _ => found, env, jumped)
    match stmt with
    | .jmp _ => (none, env, true)
    | .move var value =>
      let stored : Bil.Exp := match value with
        | .store _ _ stored _ _ => stored
        | other => other
      let next := match Bil.evalExp env value with
        | .ok result => Bil.bind env var result
        | .error _ => env
      keep (close stored) next
    | .ifElse condition yes no =>
      match Bil.evalExp env condition with
      | .ok value =>
        match Value.asBits value with
        | .ok bits =>
          let (found, next, jumped) := linkOf pc env (if bits.2.toNat != 0 then yes else no)
          if jumped then (found, next, true) else keep found next
        | .error _ => keep none env
      | .error _ => keep none env
    | _ => keep none env

private def step (journal : Journal) (pc : Nat) : IO Unit := do
  let emu := journal.emu
  let thread ← Emu.thread emu
  let seq ← journal.seq.get
  journal.seq.set (seq + 1)
  let state := (← journal.threads.get).getD thread {}
  let index := state.count
  -- The process of a thread is the one that it started in, as `execve` keeps it.
  let group ← match state.group with
    | some group => pure group
    | none => pure (((← emu.taskTable.get).find? thread).map (·.group) |>.getD thread)
  journal.history.modify (·.push { seq, thread, group, index, pc })
  if (← journal.history.get).size > journal.config.instructions then
    let half := journal.config.instructions / 2
    journal.history.modify fun history => history.extract half history.size
    journal.droppedHistory.modify (· + half)
  let previous := state.last
  let isSite (site : Nat) : Bool := site == pc || site == pc + 1
  let mut stack := state.stack
  let mut sites := state.sites
  let mut pending := state.pending
  match pending with
  | some call =>
    -- What is in the slot of a delayed branch isn't where it went yet.
    if (← emu.pendingRef.get).isNone then
      pending := none
      if !isSite call.returnsTo then
        let frame : Frame := { site := call.site, callee := pc, returnsTo := call.returnsTo, seq := call.seq }
        stack := frame :: stack
        sites := sites.push call.returnsTo
        record journal (.call seq thread frame)
  | none =>
    if let some (rest, gone) := sites.pop pc then
      sites := rest
      stack := stack.drop gone
      record journal (.ret seq thread previous pc gone)
  -- A call that it makes now.
  if let some program := ← programOf journal pc then
    let (link, _, jumped) := linkOf pc (← emu.state.get).env program
    if jumped then
      if let some returnsTo := link then
        pending := some { site := pc, returnsTo, seq }
  journal.threads.modify (·.insert thread { state with count := index + 1, stack, sites, pending, last := pc, group := some group })

private def serviceStarts (journal : Journal) (label : String) (args : List Nat) : IO Unit :=
  journal.serving.modify ((label, args, 0xcbf29ce484222325) :: ·)

private def serviceEnds (journal : Journal) (result : Option Nat) : IO Unit := do
  match ← journal.serving.get with
  | [] => pure ()
  | (label, args, written) :: rest =>
    journal.serving.set rest
    let thread ← Emu.thread journal.emu
    let state := (← journal.threads.get).getD thread {}
    let index := state.services
    journal.threads.modify (·.insert thread { state with services := index + 1 })
    record journal (.service (← journal.seq.get) thread index (← journal.emu.pc.get) label args result written)

/-- What a service leaves in memory goes into what it is known by, as it may say the same and leave something else. -/
private def noteWritten (journal : Journal) (address size : Nat) (cleared : Bool) : IO Unit := do
  match ← journal.serving.get with
  | [] => pure ()
  | (label, args, written) :: rest =>
    if cleared then return
    match ← (Emu.peek journal.emu address size).toBaseIO with
    | .ok bytes =>
      let digest := bytes.foldl (fun digest byte => ((digest ^^^ byte.toNat) * 0x100000001b3) % 2 ^ 64) written
      journal.serving.set ((label, args, digest) :: rest)
    | .error _ => pure ()

/-- Starts keeping what a run does, from here on. -/
def start (emu : Emu) (config : Config := {}) : IO Journal := do
  let journal : Journal := {
    emu, config
    history := ← IO.mkRef #[]
    droppedHistory := ← IO.mkRef 0
    events := ← IO.mkRef #[]
    droppedEvents := ← IO.mkRef 0
    seq := ← IO.mkRef 0
    threads := ← IO.mkRef {}
    jumping := ← IO.mkRef {}
    serving := ← IO.mkRef []
    loadedFrom := ← IO.mkRef none }
  let width ← Emu.wordWidth emu
  let _ ← Emu.onCode emu (0, 2 ^ width - 1) fun _ pc => step journal pc
  emu.syscallStarts.modify ((fun number args => do serviceStarts journal (← config.describe number args) args) :: ·)
  emu.syscallEnds.modify (serviceEnds journal :: ·)
  emu.memoryChanged.modify (noteWritten journal :: ·)
  emu.hostStarts.modify ((fun label => serviceStarts journal label []) :: ·)
  emu.hostEnds.modify ((fun register => do
    let result ← match register with
      | some name =>
        match Value.asBits (← Emu.reg emu ⟨name, .imm (← Emu.wordWidth emu), 0, false⟩) with
        | .ok bits => pure (some bits.2.toNat)
        | .error _ => pure none
      | none => pure none
    serviceEnds journal result) :: ·)
  -- A child goes on from where its parent was, in a thread of its own.
  emu.processHooks.modify ((fun parent child => do
    let from_ ← Emu.thread emu
    let table ← emu.taskTable.get
    let source := if (table.find? from_).map (·.group) == some parent then from_ else parent
    journal.threads.modify fun threads => match threads[source]? with
      | some state => threads.alter child fun known => some { known.getD {} with stack := state.stack, sites := state.sites }
      | none => threads) :: ·)
  pure journal

/-- That the machine was put back, as this says. Going on from a checkpoint is noted apart, as what is saved again has to be what was. -/
def noteRestored (journal : Journal) (label : String) : IO Unit := do
  if label.startsWith "checkpoint" then journal.loadedFrom.set (some label)
  else record journal (.restored (← journal.seq.get) (← Emu.thread journal.emu) label)

/-! ### What it can say -/

/-- The calls of a thread that haven't come back, the innermost first. -/
def callStack (journal : Journal) (thread : Option ThreadId := none) : IO (List Frame) := do
  let thread ← match thread with
    | some thread => pure thread
    | none => Emu.thread journal.emu
  pure ((← journal.threads.get).getD thread {}).stack

/-- The calls that were made to an address. -/
def callsOf (journal : Journal) (callee : Nat) : IO (List (ThreadId × Frame)) := do
  pure ((← journal.events.get).toList.filterMap fun event => match event with
    | .call _ thread frame => if frame.callee == callee then some (thread, frame) else none
    | _ => none)

/-- How a run first came to an instruction. -/
structure Entry where
  instruction : Executed
  /-- What its thread ran before it, the latest last. -/
  before : List Nat
  /-- The call that came here, if one did. -/
  call : Option Frame
  /-- The calls of the thread that hadn't come back, the innermost first. -/
  stack : List Frame
  /-- Whether what led to it has gone, for which there wasn't room. -/
  partial_ : Bool
  deriving Repr

/-- How a run first came to an address, with what its thread had run and what had called what. -/
def firstEntry (journal : Journal) (address : Nat) (before : Nat := 16) : IO (Option Entry) := do
  let history ← journal.history.get
  let some position := history.findIdx? (·.pc == address) | return none
  let instruction := history[position]!
  let earlier := (history.extract 0 position).toList.filter (·.thread == instruction.thread)
  let kept := earlier.drop (earlier.length - before)
  let events := (← journal.events.get).toList.filter fun event => event.thread == instruction.thread
  let stack := events.foldl (init := ([] : List Frame)) fun stack event =>
    if event.seq > instruction.seq then stack
    else match event with
      | .call _ _ frame => frame :: stack
      | .ret _ _ _ _ frames => stack.drop frames
      | .service .. | .restored .. => stack
  let call := stack.head?.bind fun frame => if frame.callee == address && frame.seq + 2 ≥ instruction.seq then some frame else none
  pure (some {
    instruction, before := kept.map (·.pc), call, stack
    partial_ := (← journal.droppedHistory.get) > 0 || (← journal.droppedEvents.get) > 0 })

private def hex (value : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 value)

def Frame.text (frame : Frame) : String :=
  s!"{hex frame.callee} called at {hex frame.site}, back to {hex frame.returnsTo}"

def Entry.text (entry : Entry) : String :=
  let how := match entry.call with
    | some frame => s!"called at {hex frame.site}"
    | none =>
      match entry.before.getLast? with
      | some pc => s!"from {hex pc}"
      | none => "as the first thing it ran"
  let stack := String.intercalate "\n    " (entry.stack.map Frame.text)
  s!"{hex entry.instruction.pc} first ran in thread {entry.instruction.thread}, {how}\n  with\n    {stack}"

/-! ### Comparing runs -/

/-- What of a run can be compared, on its own, from a file or from another machine. -/
structure Record where
  history : Array Executed
  droppedHistory : Nat
  events : Array Event
  droppedEvents : Nat
  deriving Repr, Inhabited

def toRecord (journal : Journal) : IO Record := do
  pure { history := ← journal.history.get, droppedHistory := ← journal.droppedHistory.get
         events := ← journal.events.get, droppedEvents := ← journal.droppedEvents.get }

/-- Where the threads of two runs first went different ways: the instruction that they ran last in common, which is the branch, and where each went. -/
structure BranchDifference where
  /-- Threads go by the order in which they first ran, as their numbers needn't be the same. -/
  ordinal : Nat
  leftThread : ThreadId
  rightThread : ThreadId
  index : Nat
  /-- When it was, in the instructions of the left run. -/
  seq : Nat
  branch : Option Nat
  left : Option Nat
  right : Option Nat
  deriving DecidableEq, Repr

/-- The first thing that the two runs were given differently, which is where a reason for that is to be found. -/
structure ServiceDifference where
  ordinal : Nat
  index : Nat
  seq : Nat
  left : Option Event
  right : Option Event
  deriving DecidableEq, Repr

structure Difference where
  branch : Option BranchDifference
  service : Option ServiceDifference
  /-- Whether all of what was compared was there: runs of which the oldest has gone can only be compared from where both have it. -/
  complete : Bool
  deriving DecidableEq, Repr

private def threadOrder (record : Record) : Array ThreadId :=
  (record.history.foldl (fun (order, seen) entry =>
    if seen.contains entry.thread then (order, seen) else (order.push entry.thread, seen.insert entry.thread))
    ((#[] : Array ThreadId), ({} : Std.HashSet ThreadId))).1

/-- What a service is to a comparison: what it is and what came of it. Its arguments may only be addresses. -/
def Event.serviceKey : Event → Option (String × Option Nat × Nat)
  | .service _ _ _ _ label _ result written => some (label, result, written)
  | _ => none

/-- The first thing that differs, by when it was on the left. -/
def earliest {α : Type} (seqOf : α → Nat) (found : List α) : Option α :=
  found.foldl (fun best item => match best with
    | some current => if seqOf item < seqOf current then some item else best
    | none => some item) none

/-- The threads of two runs, paired by the order in which they first ran. -/
def threadPairs (left right : Record) : List (Nat × Option ThreadId × Option ThreadId) :=
  let leftThreads := threadOrder left
  let rightThreads := threadOrder right
  (List.range (max leftThreads.size rightThreads.size)).map fun ordinal => (ordinal, leftThreads[ordinal]?, rightThreads[ordinal]?)

/-- What a thread ran, or nothing for one that isn't there. -/
def ofThread (record : Record) (thread : Option ThreadId) : Array Executed :=
  match thread with
  | some thread => record.history.filter (·.thread == thread)
  | none => #[]

/-- Where a pair of threads first went different ways, from where both still have what they ran, which is the same index of each. -/
def branchAt (left right : Record) (pair : Nat × Option ThreadId × Option ThreadId) : Option BranchDifference :=
  let (ordinal, leftThread, rightThread) := pair
  let ls := ofThread left leftThread
  let rs := ofThread right rightThread
  let first := max (ls[0]?.map (·.index) |>.getD 0) (rs[0]?.map (·.index) |>.getD 0)
  let ls := ls.filter (·.index ≥ first)
  let rs := rs.filter (·.index ≥ first)
  let parted := (List.range (max ls.size rs.size)).find? fun position =>
    (ls[position]?.map (·.pc)) != (rs[position]?.map (·.pc))
  parted.map fun position =>
    { ordinal, leftThread := leftThread.getD 0, rightThread := rightThread.getD 0
      index := first + position
      seq := (ls[position]?.map (·.seq)).getD ((ls.back?.map (·.seq)).getD 0)
      branch := if position > 0 then ls[position - 1]?.map (·.pc) else none
      left := ls[position]?.map (·.pc), right := rs[position]?.map (·.pc) : BranchDifference }

/-- What services a thread had, or none for one that isn't there. -/
def servicesOf (record : Record) (thread : Option ThreadId) : Array Event :=
  match thread with
  | some thread => record.events.filter fun event => event.thread == thread && (event matches .service ..)
  | none => #[]

/-- Whether two services are the same, by what they were and what came of them, as their arguments may only be addresses. -/
def sameService (left right : Option Event) : Bool := left.bind Event.serviceKey == right.bind Event.serviceKey

/-- What a pair of threads were first given differently. -/
def serviceAt (left right : Record) (pair : Nat × Option ThreadId × Option ThreadId) : Option ServiceDifference :=
  let (ordinal, leftThread, rightThread) := pair
  let ls := servicesOf left leftThread
  let rs := servicesOf right rightThread
  let parted := (List.range (max ls.size rs.size)).find? fun position => !sameService ls[position]? rs[position]?
  parted.map fun position =>
    { ordinal, index := position
      seq := (ls[position]?.map Event.seq).getD ((ls.back?.map Event.seq).getD 0)
      left := ls[position]?, right := rs[position]? : ServiceDifference }

/-- Where two runs part, and what they were given differently first. Threads are paired by the order in which they first ran, and each is compared on its own, so
that it doesn't matter how the threads were scheduled. -/
def compare (left right : Record) : Difference :=
  let pairs := threadPairs left right
  { branch := earliest (·.seq) (pairs.filterMap (branchAt left right))
    service := earliest (·.seq) (pairs.filterMap (serviceAt left right))
    complete := left.droppedHistory == 0 && right.droppedHistory == 0 && left.droppedEvents == 0 && right.droppedEvents == 0 }

def Difference.text (difference : Difference) : String :=
  let branch := match difference.branch with
    | some part =>
      let side (value : Option Nat) := (value.map hex).getD "nothing, as it ended"
      let at_ := (part.branch.map hex).getD "its first instruction"
      s!"thread {part.ordinal} parts after {at_}, instruction {part.index}: to {side part.left} and to {side part.right}"
    | none => "they run the same instructions"
  let service := match difference.service with
    | some part =>
      let side : Option Event → String
        | some (.service _ _ _ pc label _ result _) => s!"{label} at {hex pc} = {(result.map hex).getD "nothing"}"
        | _ => "nothing"
      s!"\nthread {part.ordinal} is first given something else by its service {part.index}: {side part.left} and {side part.right}"
    | none => "\nthey are given the same"
  branch ++ service ++ (if difference.complete then "" else "\n(the oldest of it has gone)")

/-! ### For a checkpoint -/

open Bap.Linux.Wire

private def putExecuted (out : ByteArray) (entry : Executed) : ByteArray :=
  putNat (putNat (putNat (putNat (putNat out entry.seq) entry.thread) entry.group) entry.index) entry.pc

private def getExecuted : Decoder Executed := fun data at_ => do
  let (seq, at_) ← getNat data at_
  let (thread, at_) ← getNat data at_
  let (group, at_) ← getNat data at_
  let (index, at_) ← getNat data at_
  let (pc, at_) ← getNat data at_
  .ok ({ seq, thread, group, index, pc }, at_)

private def putFrame (out : ByteArray) (frame : Frame) : ByteArray :=
  putNat (putNat (putNat (putNat out frame.site) frame.callee) frame.returnsTo) frame.seq

private def getFrame : Decoder Frame := fun data at_ => do
  let (site, at_) ← getNat data at_
  let (callee, at_) ← getNat data at_
  let (returnsTo, at_) ← getNat data at_
  let (seq, at_) ← getNat data at_
  .ok ({ site, callee, returnsTo, seq }, at_)

private def putEvent (out : ByteArray) : Event → ByteArray
  | .call seq thread frame => putFrame (putNat (putNat (putNat out 0) seq) thread) frame
  | .ret seq thread from_ to frames => putNat (putNat (putNat (putNat (putNat (putNat out 1) seq) thread) from_) to) frames
  | .service seq thread index pc label args result written =>
    let out := putNat (putNat (putNat (putNat (putNat out 2) seq) thread) index) pc
    let out := putList putNat (putText out label) args
    let out := match result with
      | some value => putNat out (value + 1)
      | none => putNat out 0
    putNat out written
  | .restored seq thread label => putText (putNat (putNat (putNat out 3) seq) thread) label

private def getEvent : Decoder Event := fun data at_ => do
  let (which, at_) ← getNat data at_
  let (seq, at_) ← getNat data at_
  let (thread, at_) ← getNat data at_
  match which with
  | 0 =>
    let (frame, at_) ← getFrame data at_
    .ok (.call seq thread frame, at_)
  | 1 =>
    let (from_, at_) ← getNat data at_
    let (to, at_) ← getNat data at_
    let (frames, at_) ← getNat data at_
    .ok (.ret seq thread from_ to frames, at_)
  | 2 =>
    let (index, at_) ← getNat data at_
    let (pc, at_) ← getNat data at_
    let (label, at_) ← getText data at_
    let (args, at_) ← getList getNat data at_
    let (result, at_) ← getNat data at_
    let (written, at_) ← getNat data at_
    .ok (.service seq thread index pc label args (if result == 0 then none else some (result - 1)) written, at_)
  | 3 =>
    let (label, at_) ← getText data at_
    .ok (.restored seq thread label, at_)
  | _ => .error "a journal with an event that isn't one"

private def byKey {α : Type} (entries : List (Nat × α)) : List (Nat × α) :=
  (entries.toArray.qsort fun left right => left.1 < right.1).toList

private def putThread (out : ByteArray) (entry : ThreadId × ThreadState) : ByteArray :=
  let state := entry.2
  let out := putNat (putNat (putNat out entry.1) state.count) state.services
  let out := putList putFrame out state.stack
  let out := match state.pending with
    | some call => putNat (putNat (putNat (putNat out 1) call.site) call.returnsTo) call.seq
    | none => putNat out 0
  let out := putNat out state.last
  match state.group with
  | some group => putNat out (group + 1)
  | none => putNat out 0

private def getThread : Decoder (ThreadId × ThreadState) := fun data at_ => do
  let (thread, at_) ← getNat data at_
  let (count, at_) ← getNat data at_
  let (services, at_) ← getNat data at_
  let (stack, at_) ← getList getFrame data at_
  let (known, at_) ← getNat data at_
  let (pending, at_) ← if known == 0 then Except.ok (none, at_) else do
    let (site, at_) ← getNat data at_
    let (returnsTo, at_) ← getNat data at_
    let (seq, at_) ← getNat data at_
    Except.ok (some ({ site, returnsTo, seq } : Pending), at_)
  let (last, at_) ← getNat data at_
  let (group, at_) ← getNat data at_
  let group := if group == 0 then none else some (group - 1)
  .ok ((thread, { count, services, stack, sites := CallSites.ofSites (stack.map (·.returnsTo)), pending, last, group }), at_)

/-- All that it has, in an order that the same run always has. It is only saved between instructions, when no service is in progress. -/
def save (journal : Journal) : IO ByteArray := do
  let out := putList putExecuted ByteArray.empty (← journal.history.get).toList
  let out := putNat out (← journal.droppedHistory.get)
  let out := putList putEvent out (← journal.events.get).toList
  let out := putNat (putNat out (← journal.droppedEvents.get)) (← journal.seq.get)
  pure (putList putThread out (byKey (← journal.threads.get).toList))

/-- What `save` gave, and where it ends. -/
def load (journal : Journal) (data : ByteArray) (at_ : Nat := 0) : IO Nat := do
  let decoded : Except String _ := do
    let (history, at_) ← getList getExecuted data at_
    let (droppedHistory, at_) ← getNat data at_
    let (events, at_) ← getList getEvent data at_
    let (droppedEvents, at_) ← getNat data at_
    let (seq, at_) ← getNat data at_
    let (threads, at_) ← getList getThread data at_
    .ok (history, droppedHistory, events, droppedEvents, seq, threads, at_)
  let (history, droppedHistory, events, droppedEvents, seq, threads, at_) ← IO.ofExcept decoded
  journal.history.set history.toArray
  journal.droppedHistory.set droppedHistory
  journal.events.set events.toArray
  journal.droppedEvents.set droppedEvents
  journal.seq.set seq
  journal.threads.set (threads.foldl (fun map pair => map.insert pair.1 pair.2) {})
  pure at_

end Journal

end Bap.Analysis.Journal
