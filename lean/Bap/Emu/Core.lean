import Bap.Bil.Eval
import Bap.Primus.Memory
import Bap.Emu.Semantics

/-! The pure core of emulator execution.

Everything here is free of `IO.Ref`s: pure transitions (`advance`, `commit`, `failControl`, `afterHook`,
`pickNext`, `mergeRound`, `accessFault`, ...) and control flows that are generic in the monad (`stepM`,
`runM`, `runChainedM`, `preemptiveM`, `roundM`, `readThroughM`). `Bap.Emu` instantiates the generic flows with its
references, so that the code that runs is the code that `Bap.Emu.CoreProofs` proves things about, through a
state-monad model.

## What stays trusted

Everything that the theorems about the emulator and native code rest on and that Lean cannot prove is in this list, and nothing else. All of the proofs
are about the flows on the model, and Lean sees no more of `IO`, `Task` and `@[extern]` than an `opaque` that it cannot unfold:

1. **The cells.** `controlCells` is `ControlCells` on five `IO.Ref`s, and a ref returns what was last set in it, with
   no thread writing to it meanwhile. Each worker of a parallel round has refs of its own. `stepOpsOf` is what both
   the emulator and the model make their operations with, so that which reference is which is not a matter of
   reading: the model's operations are `stepOpsOf` of its cells (`Model.ops_is_stepOpsOf`). The same goes for the refs of
   `Bap.Primus.Lifted`, whose code around native runs is plumbing of the proved `encodeState`, `withControl`, `chainedCount`, `syncState` and `nativeOutcome`.
2. **The arguments of `stepOpsOf`.** `save`, `restore`, `execute`, `notifyCode`, `dispatch` in `stepOps` have the
   effects that `Model.World` gives them: `restore` undoes all that happened since `save`, except for what the log of
   the model keeps, what hooks did to the outside. That `save` takes all that `Snapshot` has is by reading `snapshotBlock`.
3. **What a step of a range is on these references.** `lowerGraph_correct` is about the program and the slots that go in and come out. That
   `executeBlock` passes them along, on the cells, and so that a range meets `RangeLaws`, is by reading it; its decisions are the proved
   `rangeSiteStops` and `rangeBudgetOf`.
4. **The parallel round.** `roundM` is proved on the model. `IO.asTask` runs the workers, `IO.wait` waits for them all,
   and the mutex of `serialize` gives hooks one at a time. Between the workers only the native memory is shared, by
   obligation 10 of `Bap.Jit`.
5. **Native code**, on the terms of `Bap.Jit`: the C++ and LLVM are not verified.
6. **Lifting.** The blocks a range is made of are what the lifter makes of the bytes, and it makes the same of the same bytes.
   `sameBytes_eq` and the versions of ranges go by that. -/

namespace Bap.Emu

structure Region where
  address : Nat
  data : ByteArray
  protection : Primus.Protection
  deriving DecidableEq

namespace Region

def contains (region : Region) (address : Nat) : Bool :=
  region.address ≤ address && address < region.address + region.data.size

end Region

def lookupRegion (regions : List Region) (address : Nat) : Option Region :=
  regions.find? fun region => region.contains address

inductive MemoryOperation where
  | read | write | fetch
  deriving DecidableEq, Repr

abbrev ThreadId := Nat

structure MemoryFault where
  pc : Nat
  address : Nat
  operation : MemoryOperation
  thread : ThreadId := 1
  deriving DecidableEq, Repr

inductive DelayKind where
  | none | delayed | likely | forbidden
  deriving DecidableEq, Repr

structure PendingBranch where
  branch : Nat
  target : Nat
  deriving DecidableEq, Repr

structure ThreadContext where
  id : Nat
  state : Bil.State
  pc : Nat
  stopped : Bool
  pending : Option PendingBranch := none
  /-- The address whose code hooks fired already for the instruction this thread is about to run. -/
  skip : Option Nat := none
  deriving Repr

structure ThreadInfo where
  id : Nat
  pc : Nat
  stopped : Bool
  deriving DecidableEq, Repr

/-- What `save` and `restore` keep of an emulator. Hooks are closures, and stay out of it. -/
structure Snapshot where
  state : Bil.State
  pc : Nat
  regions : List Region
  stopped : Bool
  threads : List ThreadContext
  currentThread : ThreadId
  nextThread : ThreadId
  pending : Option PendingBranch
  processMemory : List (ThreadId × List Region) := []
  skip : Option Nat := none

/-! ### One instruction -/

/-- Where control goes after an instruction. -/
structure Advance where
  pc : Nat
  pending : Option PendingBranch := none
  stop : Bool := false
  deriving DecidableEq, Repr

/-- The size of the only instructions with delay slots, those of MIPS. -/
def delaySlotSize : Nat := 4

/-- The control flow of an instruction at `address` with fall-through `next`.
A delayed branch enters the slot, which lies right after the branch. An untaken likely branch annuls the slot. A pending branch
is taken once the slot completes. An instruction that could not complete, an unhandled special or a CPU
exception, keeps the pc and the pending branch, like a precise exception, and stops the thread. -/
def advance (address next : Nat) (effect : Bil.Effect) (handled : Bool) (delay : DelayKind)
    (pending : Option PendingBranch) : Advance :=
  match effect with
  | .normal =>
    match pending with
    | some branch => { pc := branch.target }
    | none => { pc := if delay == .likely then next + delaySlotSize else next }
  | .jump target =>
    match pending with
    | some _ => { pc := target.toNat }
    | none =>
      match delay with
      | .delayed | .likely => { pc := address + delaySlotSize, pending := some ⟨address, target.toNat⟩ }
      | .none | .forbidden => { pc := target.toNat }
  | .special _ =>
    if handled then
      match pending with
      | some branch => { pc := branch.target }
      | none => { pc := next }
    else { pc := address, pending, stop := true }
  | .cpuExn _ => { pc := address, pending, stop := true }

/-- `advance`, except that a handler that served a special and moved the pc decides where to go on. -/
def commit (address next : Nat) (effect : Bil.Effect) (handled : Bool) (current : Nat) (delay : DelayKind)
    (pending : Option PendingBranch) : Advance :=
  if handled && current != address then { pc := current }
  else advance address next effect handled delay pending

/-- What a step does once the code hooks of `address` ran. -/
inductive AfterHook where
  /-- A hook stopped the thread: nothing executes. Resuming must not run the hooks again. -/
  | halt (skip : Option Nat)
  /-- A hook moved the pc: the instruction does not execute, and the next step starts at the new pc. -/
  | redirect
  | proceed
  deriving DecidableEq, Repr

def afterHook (address current : Nat) (stopped : Bool) : AfterHook :=
  if stopped then .halt (if current == address then some address else none)
  else if current == address then .proceed
  else .redirect

/-- The pc and skip marker after a failed step. A fault in a delay slot rewinds to the branch, whose
hooks fire again as it runs again. Any other fault retries the same instruction, whose hooks fired. -/
def failControl (address : Nat) (pending : Option PendingBranch) : Nat × Option Nat :=
  match pending with
  | some branch => (branch.branch, none)
  | none => (address, some address)

/-- The environment of a step: references in `IO`, a state in the model of `Bap.Emu.CoreProofs`. -/
structure StepOps (m : Type → Type) (σ : Type) where
  stopped : m Bool
  pc : m Nat
  skip : m (Option Nat)
  setSkip : Option Nat → m Unit
  notifyCode : Nat → m Unit
  save : m σ
  pending : m (Option PendingBranch)
  delayFor : Nat → m DelayKind
  /-- Records the instruction in the trace. -/
  mark : Nat → m Unit
  /-- Runs the instruction, commits its state, and returns its fall-through and effect. -/
  execute : Nat → m (Nat × Bil.Effect)
  /-- Whether a hook served the special. -/
  dispatch : String → m Bool
  setControl : Nat → Option PendingBranch → m Unit
  halt : m Unit
  /-- Undoes everything since `save`. -/
  restore : σ → m Unit
  /-- Attributes a recorded fault to the branch at the given address. -/
  faultAt : Nat → m Unit

/-- The references that say where a thread is. -/
structure ControlCells (m : Type → Type) where
  stopped : m Bool
  setStopped : Bool → m Unit
  pc : m Nat
  skip : m (Option Nat)
  setSkip : Option Nat → m Unit
  pending : m (Option PendingBranch)
  /-- The pc and the pending branch, which change together. -/
  setControl : Nat → Option PendingBranch → m Unit

/-- The environment of a step, from the cells and what is particular to who runs it. -/
@[inline] def stepOpsOf {m : Type → Type} {σ : Type} (cells : ControlCells m) (notifyCode : Nat → m Unit) (save : m σ)
    (delayFor : Nat → m DelayKind) (mark : Nat → m Unit) (execute : Nat → m (Nat × Bil.Effect))
    (dispatch : String → m Bool) (restore : σ → m Unit) (faultAt : Nat → m Unit) : StepOps m σ where
  stopped := cells.stopped
  pc := cells.pc
  skip := cells.skip
  setSkip := cells.setSkip
  notifyCode := notifyCode
  save := save
  pending := cells.pending
  delayFor := delayFor
  mark := mark
  execute := execute
  dispatch := dispatch
  setControl := cells.setControl
  halt := cells.setStopped true
  restore := restore
  faultAt := faultAt

/-- Runs the instruction at `address`, whose hooks ran. Atomic: a failure restores what `save` saved. -/
@[specialize] def stepExecute {m : Type → Type} {σ ε : Type} [Monad m] [MonadExcept ε m]
    (ops : StepOps m σ) (address : Nat) : m Bool := do
  let before ← ops.save
  let pending ← ops.pending
  tryCatch
    (do
      let delay ← match pending with
        | some _ => pure DelayKind.none
        | none => ops.delayFor address
      ops.mark address
      let (next, effect) ← ops.execute address
      let handled ← match effect with
        | .special name => ops.dispatch name
        | _ => pure false
      let current ← ops.pc
      let out := commit address next effect handled current delay pending
      ops.setControl out.pc out.pending
      if out.stop then
        ops.halt
        ops.setSkip (some address)
      pure !out.stop)
    (fun error => do
      ops.restore before
      let (pc, skip) := failControl address pending
      ops.setControl pc none
      ops.setSkip skip
      if pending.isSome then ops.faultAt pc
      throw error)

/-- One step: hooks of the pc, unless they fired for this very instruction, then the instruction. -/
@[specialize] def stepM {m : Type → Type} {σ ε : Type} [Monad m] [MonadExcept ε m]
    (ops : StepOps m σ) : m Bool := do
  if ← ops.stopped then
    pure false
  else
    let address ← ops.pc
    let skipped ← ops.skip
    ops.setSkip none
    if skipped != some address then ops.notifyCode address
    let current ← ops.pc
    let stopped ← ops.stopped
    match afterHook address current stopped with
    | .halt skip =>
      ops.setSkip skip
      pure false
    | .redirect => pure true
    | .proceed => stepExecute (ε := ε) ops address

/-- Up to `fuel` steps, until one reports that the thread cannot go on. -/
@[specialize] def runM {m : Type → Type} [Monad m] (step : m Bool) : Nat → Nat → m Nat
  | 0, total => pure total
  | fuel + 1, total => do
    if ← step then runM step fuel (total + 1) else pure total

/-- `runM` for a step that may run a range of instructions. `allow` tells it how many it may run after its first,
and `chained` how many it did, so that the instructions, and not the steps, are what the fuel counts. -/
@[specialize] def runChainedM {m : Type → Type} [Monad m] (step : m Bool) (allow : Nat → m Unit) (chained : m Nat) :
    Nat → Nat → Nat → m Nat
  | 0, _, total => pure total
  | rounds + 1, remaining, total => do
    if remaining = 0 then
      pure total
    else
      allow (remaining - 1)
      if ← step then
        let extra := min (← chained) (remaining - 1)
        runChainedM step allow chained rounds (remaining - 1 - extra) (total + 1 + extra)
      else pure total

/-- `run` with precise faults: when a step that may have chained fails, it has rolled back to where it started, which is
not where the fault was. Then `again`, if it says that it did chain, and single steps from there on, the first to fail being the fault itself,
which leaves everything as single steps do. This costs nothing on the way to a fault. Nothing that a range ran is
observed, which `rangeSiteStops` and `rangeBudgetOf` see to, so that running it again is not seen either. -/
@[specialize] def runPreciseM {m : Type → Type} {ε : Type} [Monad m] [MonadExcept ε m] (chained : m Nat) (single again : m Bool) (bound : Nat) :
    m Nat :=
  tryCatch chained fun error => do
    if ← again then
      let _ ← runM single bound 0
    throw error

/-- Whether a code site inside a range ends the run before its block: code that was written, a hook that arrived while nothing
observed the sites, or a hook of the block. Hooks read the state, which only the step that starts at the block has up to date. -/
def rangeSiteStops (dirty late hooked : Bool) : Bool := dirty || late || hooked

/-- How many blocks a step may chain. A hook of an access runs in the middle of a block and reads the state, which is
that of a step's start, so that with one a step is one instruction. -/
def rangeBudgetOf (budget : Nat) (accessesWatched : Bool) : Nat := if accessesWatched then 0 else budget

/-! ### Memory accesses -/

/-- Whether an access of `size` bytes at `address` touches the inclusive range `first`..`last`. -/
def accessTouches (first last address size : Nat) : Bool :=
  address ≤ last && first < address + max size 1

/-- Whether `region` holds every byte of the access and allows it. -/
def accessAllowed (region : Region) (write : Bool) (address size : Nat) : Bool :=
  region.contains address && address + size ≤ region.address + region.data.size &&
    (if write then region.protection.writable else region.protection.readable)

/-- The first offset of an access that the protection forbids, searched byte by byte. -/
def accessFaultSlow (regions : List Region) (write : Bool) (address size : Nat) : Option Nat :=
  (List.range size).find? fun offset =>
    match lookupRegion regions (address + offset) with
    | none => true
    | some region => if write then !region.protection.writable else !region.protection.readable

/-- The first offset of an access that the protection forbids. Almost all accesses lie in the region of
their first byte, which settles them without a search. -/
@[inline] def accessFault (regions : List Region) (write : Bool) (address size : Nat) : Option Nat :=
  match lookupRegion regions address with
  | some region =>
    if accessAllowed region write address size then none
    else accessFaultSlow regions write address size
  | none => accessFaultSlow regions write address size

/-- Whether a write of `size` bytes at `address` touches executable memory. -/
def writesCode (regions : List Region) (address size : Nat) : Bool :=
  regions.any fun region =>
    region.protection.executable && region.address < address + size &&
      address < region.address + region.data.size

/-- An access as the emulator handles it: permissions first, and a forbidden access does nothing else. -/
@[specialize] def notifyAccess {m : Type → Type} [Monad m] (regions : List Region) (write : Bool) (address size : Nat)
    (fault : Nat → m Unit) (dirty : m Unit) (record : m Unit) (hooks : m Unit) : m Unit :=
  match accessFault regions write address size with
  | some offset => fault offset
  | none => do
    if write && size > 0 && writesCode regions address size then dirty
    record
    hooks

/-- The hooks that an access fires, in registration order. -/
@[inline] def hooksForAccess {β : Type} (first last : β → Nat) (hooks : List β) (address size : Nat) : List β :=
  hooks.filter fun hook => accessTouches (first hook) (last hook) address size

/-- The hooks that an instruction at `address` fires, in registration order. -/
@[inline] def hooksForCode {β : Type} (first last : β → Nat) (hooks : List β) (address : Nat) : List β :=
  hooks.filter fun hook => first hook ≤ address && address ≤ last hook

/-! ### Threads -/

/-- The table with `context` replacing the previous context of its thread. -/
def saveContext (threads : List ThreadContext) (context : ThreadContext) : List ThreadContext :=
  context :: threads.filter fun thread => thread.id != context.id

def setThreadStopped (threads : List ThreadContext) (id : Nat) (stopped : Bool) : List ThreadContext :=
  threads.map fun context => if context.id == id then { context with stopped } else context

/-- The context of a thread that `spawnThread` starts. -/
def spawnContext (id : Nat) (state : Bil.State) (argument : Bap.Var) (value : Value) (start : Nat) :
    ThreadContext :=
  ⟨id, { env := Bil.bind state.env argument value }, start, false, none, none⟩

/-- The context of a process that `forkThread` creates: the parent's registers but the result register,
stopped until its parent lets it go. -/
def forkContext (id : Nat) (state : Bil.State) (result : Bap.Var) (value : Value) (childPc : Nat) :
    ThreadContext :=
  ⟨id, { env := Bil.bind state.env result value }, childPc, true, none, none⟩

def lowerId (best : Option Nat) (id : Nat) : Option Nat :=
  match best with
  | some other => if other ≤ id then some other else some id
  | none => some id

/-- The smallest id satisfying `p`, among the threads that can run. -/
def minRunnable (threads : List ThreadContext) (p : Nat → Bool) : Option Nat :=
  threads.foldl (init := none) fun best context =>
    if !context.stopped && p context.id then lowerId best context.id else best

/-- Round robin: the runnable thread after `current` in id order, wrapping around. -/
def pickNext (threads : List ThreadContext) (current : Nat) : Option Nat :=
  match minRunnable threads (fun id => current < id) with
  | some id => some id
  | none => minRunnable threads (fun id => id != current)

/-- All-stop preemption: threads take turns of `quantum` steps until the fuel runs out, or the thread
that runs stops. A stop returns to the caller at once with that thread current, so that a breakpoint can
be inspected in the thread that hit it, and the threads behind it stay where they are. `runQuantum` and
`resumeNext` move on past a stopped thread. -/
@[specialize] def preemptiveM {m : Type → Type} [Monad m] (run : Nat → m Nat) (stopped : m Bool)
    (switchNext : m Bool) (quantum fuel : Nat) : Nat → Nat → Nat → m Nat
  | 0, _, total => pure total
  | rounds + 1, remaining, total => do
    if remaining = 0 then
      pure total
    else
      let steps ← run (min quantum remaining)
      let total := total + steps
      if total = fuel then
        pure total
      else if ← stopped then
        pure total
      else if ← switchNext then
        preemptiveM run stopped switchNext quantum fuel rounds (remaining - steps) total
      else
        pure total

/-- The table on the way out of the shared address space: what all its threads hold is what the thread
that leaves holds, since threads there do not keep their contexts up to date for each other. -/
def parkShared {β : Type} (threads : List ThreadContext) (processes : Std.HashMap Nat β) (memoryVar : Bap.Var)
    (memory : Value) : List ThreadContext :=
  threads.map fun context =>
    if processes.contains context.id then context
    else { context with state := { env := Bil.bind context.state.env memoryVar memory } }

/-- Total steps of a parallel round, or the first worker's error in thread order. -/
def joinWorkers {ε : Type} : List (Except ε Nat) → Except ε Nat
  | [] => .ok 0
  | .error error :: _ => .error error
  | .ok steps :: rest =>
    match joinWorkers rest with
    | .ok total => .ok (steps + total)
    | .error error => .error error

/-- A parallel round. All workers finish before it is judged, a failure of any undoes the round, whatever else it did,
and only a round without one commits. -/
@[specialize] def roundM {m : Type → Type} {σ ε ω : Type} [Monad m] [MonadExcept ε m] (save : m σ) (restore : σ → m Unit)
    (setUp : m ω) (runAll : ω → m (List (Except ε Nat))) (reportFault : ω → m Unit) (commit : ω → m Unit) : m Nat := do
  let before ← save
  tryCatch
    (do
      let workers ← setUp
      let results ← runAll workers
      match joinWorkers results with
      | .ok steps =>
        commit workers
        pure steps
      | .error error =>
        reportFault workers
        throw error)
    (fun error => do
      restore before
      throw error)

/-- What a worker of a parallel round leaves behind. -/
structure WorkerResult where
  id : Nat
  state : Bil.State
  pc : Nat
  stopped : Bool
  pending : Option PendingBranch
  skip : Option Nat

/-- The threads that take part in a parallel round. -/
def activeThreads (threads : List ThreadContext) : List ThreadContext :=
  threads.filter fun context => !context.stopped

/-- The thread table after a parallel round. Workers report their contexts, the others keep theirs, a
`stopThread` or `resumeThread` of the round wins over the flag, and threads that hooks created during the
round, which are in `live` but not in `contexts`, stay. -/
def mergeRound (contexts live : List ThreadContext) (results : List WorkerResult)
    (control : Std.HashMap Nat Bool) : List ThreadContext :=
  let merged := contexts.map fun context =>
    match results.find? fun result => result.id == context.id with
    | none => { context with stopped := controlledStopped control context.id context.stopped }
    | some result =>
      { context with
        state := result.state
        pc := result.pc
        stopped := controlledStopped control context.id result.stopped
        pending := result.pending
        skip := result.skip }
  merged ++ (live.filter fun thread => !contexts.any fun context => context.id == thread.id).map fun thread =>
    { thread with stopped := controlledStopped control thread.id thread.stopped }

/-! ### Address spaces -/

/-- The native memory of a thread: its private one, or the one that the threads without one share. -/
def nativeFor {β : Type} (processes : Std.HashMap Nat β) (shared : Option β) (id : Nat) : Option β :=
  match processes.get? id with
  | some memory => some memory
  | none => shared

/-- `Memory.readByte` at an address known to be in the address space, which saves working out `2 ^ width`. -/
def peekByte {width : Nat} (memory : Bap.Memory width) (address : Nat) : UInt8 :=
  match memory.pages.get? (address / Bap.Memory.pageSize) with
  | some page => page[address % Bap.Memory.pageSize]!
  | none => 0

/-- `size` bytes from an address, where all of them are in the address space. -/
def peekBytes {width : Nat} (memory : Bap.Memory width) (address size : Nat) : ByteArray :=
  (List.range size).foldl (init := ByteArray.emptyWithCapacity size) fun bytes offset =>
    bytes.push (peekByte memory (address + offset))

/-- `memory` with the bytes that `read` gives at the written ranges. -/
@[specialize] def applyJournalM {m : Type → Type} [Monad m] {width : Nat} (read : Nat → m UInt8)
    (memory : Bap.Memory width) (journal : List (Nat × Nat)) : m (Bap.Memory width) :=
  journal.foldlM (init := memory) fun memory write =>
    (List.range write.2).foldlM (init := memory) fun memory offset => do
      let byte ← read (write.1 + offset)
      pure (Bap.Memory.writeByte memory (BitVec.ofNat width (write.1 + offset)) byte)

/-- The first of `offsets` at which `memory` does not have what `read` gives, patched, with whether there was one. -/
@[specialize] def patchRange {m : Type → Type} [Monad m] {width : Nat} (read : Nat → m UInt8) (start : Nat) :
    List Nat → Bap.Memory width × Bool → m (Bap.Memory width × Bool)
  | [], current => pure current
  | offset :: rest, (memory, changed) => do
    let byte ← read (start + offset)
    let address := BitVec.ofNat width (start + offset)
    if Bap.Memory.readByte memory address == byte then
      patchRange read start rest (memory, changed)
    else
      patchRange read start rest (Bap.Memory.writeByte memory address byte, true)

/-- `memory` with what `read` gives at everything that a computation on it reads, which `reads` works out and
which depends on what it finds. The outcome is a memory on which the computation reads only what `read` gives,
unless that took more than `rounds`. -/
@[specialize] def readThroughM {m : Type → Type} [Monad m] {width : Nat} (reads : Bap.Memory width → m (List (Nat × Nat)))
    (read : Nat → m UInt8) : Nat → Bap.Memory width → m (Option (Bap.Memory width))
  | 0, _ => pure none
  | rounds + 1, memory => do
    let ranges ← reads memory
    let (patched, changed) ← ranges.foldlM (init := (memory, false)) fun current range =>
      patchRange read range.1 (List.range range.2) current
    if changed then readThroughM reads read rounds patched else pure (some memory)

/-- A journal of written ranges, without immediately repeated entries: only the final bytes matter. -/
def journalWrite (journal : List (Nat × Nat)) (address size : Nat) : List (Nat × Nat) :=
  match journal with
  | (first, length) :: _ =>
    if first == address && length == size then journal else (address, size) :: journal
  | [] => [(address, size)]

end Bap.Emu
