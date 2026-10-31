import Bap.Target.RISCV
import Bap.Target.RISCV32
import Bap.Target.X86
import Bap.Target.AArch64
import Bap.Target.MIPS
import Bap.Target.MIPS32
import Bap.Primus.Lifted
import Bap.Primus.Memory
import Bap.Emu.Core
import Std.Sync.Mutex
import Std.Data.HashSet

namespace Bap.Emu

inductive SyscallAbi where
  | riscv | x86_64 | aarch64 | mips
  deriving DecidableEq, Repr

inductive DelayPolicy where
  | none | mips (release6 : Bool)
  deriving DecidableEq, Repr

structure Config where
  disassembler : Disasm.Disassembler
  disassemblerAt : Option (Nat → IO Disasm.Disassembler) := none
  memory : Bap.Var
  endian : Endian := .little
  syscallAbi : SyscallAbi := .riscv
  delayPolicy : DelayPolicy := .none
  /-- How many times an instruction runs in the interpreter, which takes microseconds, before it is compiled, which takes
  hundreds of them: most of a program runs a few times at most. -/
  hotThreshold : Nat := 16
  cacheLimit : Nat := 4096
  /-- How many blocks a compiled range holds. 16 runs tight loops whole, and the cost of compiling a range grows faster than its
  size. A step of 1 has no ranges. -/
  rangeLimit : Nat := 16
  jitCooldown : Nat := 0

abbrev HookId := Nat

inductive SyscallAction where
  | default | returnValue (value : Nat)

inductive IntrinsicAction where
  | default | proceed

structure TraceAccess where
  insn : Nat
  pc : Nat
  address : Nat
  size : Nat
  write : Bool
  value : Option Nat
  thread : ThreadId
  deriving DecidableEq, Repr

private structure TraceState where
  pcsFront : List Nat := []
  pcsBack : List Nat := []
  pcRetained : Nat := 0
  pcCount : Nat := 0
  droppedPcs : Nat := 0
  pcCapacity : Nat := 0
  accesses : List TraceAccess := []
  accessCount : Nat := 0
  droppedAccesses : Nat := 0
  accessCapacity : Nat := 0
  watch : Option (Nat × Nat) := none

private structure CodeHookContext where
  engine : Primus.Lifted.Engine
  state : IO.Ref Bil.State
  pc : IO.Ref Nat
  stopped : IO.Ref Bool
  currentThreadRef : IO.Ref ThreadId
  trace : IO.Ref (Option TraceState)
  lastFault : IO.Ref (Option MemoryFault)
  skipCode : IO.Ref (Option Nat)
  pendingRef : IO.Ref (Option PendingBranch)

structure ReadHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → Nat → IO Unit

structure WriteHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → Nat → Nat → IO Unit

structure IntrinsicHook where
  id : HookId
  name : String
  action : CodeHookContext → Nat → IO IntrinsicAction

structure CodeHook where
  id : HookId
  first : Nat
  last : Nat
  action : CodeHookContext → Nat → IO Unit

structure SyscallHook where
  id : HookId
  action : CodeHookContext → Nat → List Nat → IO SyscallAction

structure Emu where
  config : Config
  engine : Primus.Lifted.Engine
  state : IO.Ref Bil.State
  pc : IO.Ref Nat
  regions : IO.Ref (List Region)
  stopped : IO.Ref Bool
  hooks : IO.Ref (List CodeHook)
  readHooks : IO.Ref (List ReadHook)
  writeHooks : IO.Ref (List WriteHook)
  syscallHooks : IO.Ref (List SyscallHook)
  intrinsicHooks : IO.Ref (List IntrinsicHook)
  nextHook : IO.Ref HookId
  trace : IO.Ref (Option TraceState)
  lastFault : IO.Ref (Option MemoryFault)
  skipCode : IO.Ref (Option Nat)
  breakpointsRef : IO.Ref (List (HookId × Nat))
  threadsRef : IO.Ref (List ThreadContext)
  currentThreadRef : IO.Ref ThreadId
  nextThreadRef : IO.Ref ThreadId
  pendingRef : IO.Ref (Option PendingBranch)
  parallelLock : IO.Ref (Option Std.BaseMutex)
  parallelWorkers : IO.Ref (List (ThreadId × Primus.Lifted.Engine))
  /-- The memory of each address space other than the first, by the id of the space. -/
  processMemory : IO.Ref (Std.HashMap ThreadId Jit.Memory)
  threadControl : IO.Ref (Std.HashMap ThreadId Bool)
  /-- The memory of the threads without their own, while a thread with its own runs. -/
  sharedMemory : IO.Ref (Option Jit.Memory)
  /-- The ranges that a parallel worker wrote. Workers leave the memory of their state behind. -/
  journal : Option (IO.Ref (List (Nat × Nat))) := none
  /-- How many blocks the last step could chain, which says whether its failure is the fault itself. -/
  lastBudget : IO.Ref Nat
  /-- Whether the compiled range that runs started with nothing to observe it. -/
  rangeQuiet : IO.Ref Bool
  /-- How many instructions the next step may run after its first, for `run`: a step on its own runs one. -/
  budget : IO.Ref Nat
  /-- Whether the step that just failed did so to run again as one instruction, at a hook of an access. -/
  restarting : IO.Ref Bool
  /-- The address of the running step until it reaches a code site. -/
  rangeStart : IO.Ref (Option Nat)
  /-- The addresses whose steps met a hook of an access, which run as one instruction from then on. Nothing else depends on
  it: which steps chain changes how fast the emulator runs and not what it does. -/
  watchedSteps : IO.Ref (Std.HashSet Nat)
  /-- The tasks, and which are blocked waiting for others. -/
  taskTable : IO.Ref TaskTable
  /-- Where the instruction that runs goes next, for a system call to know where a new thread starts. -/
  nextPc : IO.Ref Nat

/-- Compiled ranges chain blocks along their branches, which leaves delay slots out. -/
private def rangeLimitOf (config : Config) : Nat :=
  if config.delayPolicy == .none then config.rangeLimit else 1

private def memoryWidth (config : Config) : Except String Nat :=
  match config.memory.typ with
  | .mem width 8 => .ok width
  | _ => .error "Emu memory must have byte-wide cells"

private def overlaps (left right : Region) : Bool :=
  left.address < right.address + right.data.size &&
    right.address < left.address + left.data.size

/-- Whether every byte of `region` is addressable with `width` address bits. -/
def regionInSpace (width : Nat) (region : Region) : Bool :=
  region.address + region.data.size ≤ 2 ^ width

/-- Whether `region` can overlay `mapped`: it replaces a same-sized region at its own address and
touches no other. -/
def overlayConflict (mapped : List Region) (region : Region) : Bool :=
  mapped.any fun current =>
    if current.address = region.address then current.data.size != region.data.size
    else overlaps current region

private def initializeMemory (config : Config) (regions : List Region) : Except String Bil.State := do
  let width ← memoryWidth config
  if regions.any fun left => regions.any fun right => left != right && overlaps left right then
    .error "Emu regions overlap"
  if !regions.all (regionInSpace width) then
    .error "Emu region exceeds the address space"
  let cells := regions.foldl (init := Bap.Memory.empty width) fun cells region =>
    Bap.Memory.writeRegion cells region.address region.data
  .ok { env := [(config.memory, .memory cells)] }

/-- An engine for the emulator. Its memory is native from the start, its observer is `notifyMemory`, which rejects
an access past the end of the address space, and a block that runs off its end goes on with the next one. -/
private def createEngine (config : Config) (deferMemorySync : Bool) : IO Primus.Lifted.Engine :=
  Primus.Lifted.Engine.create config.hotThreshold config.cacheLimit (rangeLimitOf config) 16 config.jitCooldown
    deferMemorySync (persistentFrom := 0) (wrapFaults := true) (chainFallthrough := true)

def create (config : Config) (mapped : List Region) (initial : Bil.State) (entry : Nat) : IO Emu := do
  let initial ← match initializeMemory config mapped with
    | .ok memory => pure { env := memory.env ++ initial.env }
    | .error error => throw <| IO.userError error
  pure {
    config
    engine := ← createEngine config false
    state := ← IO.mkRef initial
    pc := ← IO.mkRef entry
    regions := ← IO.mkRef mapped
    stopped := ← IO.mkRef false
    hooks := ← IO.mkRef []
    readHooks := ← IO.mkRef []
    writeHooks := ← IO.mkRef []
    syscallHooks := ← IO.mkRef []
    intrinsicHooks := ← IO.mkRef []
    nextHook := ← IO.mkRef 0
    trace := ← IO.mkRef none
    lastFault := ← IO.mkRef none
    skipCode := ← IO.mkRef none
    breakpointsRef := ← IO.mkRef []
    threadsRef := ← IO.mkRef [⟨1, initial, entry, false, none, none⟩]
    currentThreadRef := ← IO.mkRef 1
    nextThreadRef := ← IO.mkRef 2
    pendingRef := ← IO.mkRef none
    parallelLock := ← IO.mkRef none
    parallelWorkers := ← IO.mkRef []
    processMemory := ← IO.mkRef {}
    threadControl := ← IO.mkRef {}
    sharedMemory := ← IO.mkRef none
    lastBudget := ← IO.mkRef 0
    rangeQuiet := ← IO.mkRef false
    budget := ← IO.mkRef 0
    restarting := ← IO.mkRef false
    rangeStart := ← IO.mkRef none
    watchedSteps := ← IO.mkRef {}
    taskTable := ← IO.mkRef (TaskTable.initial 1)
    nextPc := ← IO.mkRef 0
  }

/-- The address space of a thread. -/
private def spaceOf (emu : Emu) (id : ThreadId) : IO Nat := do pure ((← emu.taskTable.get).spaceOf id)

private def saveCurrentThread (emu : Emu) : IO Unit := do
  let context : ThreadContext := {
    id := ← emu.currentThreadRef.get
    state := ← emu.state.get
    pc := ← emu.pc.get
    stopped := ← emu.stopped.get
    pending := ← emu.pendingRef.get
    skip := ← emu.skipCode.get
  }
  emu.threadsRef.modify (saveContext · context)

private def captureThreads (emu : Emu) : IO (List ThreadContext) := do
  saveCurrentThread emu
  let state ← emu.state.get
  let memory := match Bil.lookup state.env emu.config.memory with
    | .ok value => some value
    | .error _ => none
  let threads ← emu.threadsRef.get
  let table ← emu.taskTable.get
  let space := table.spaceOf (← emu.currentThreadRef.get)
  pure (threads.map fun thread =>
    if table.spaceOf thread.id != space then thread else
      match memory with
      | some memory => { thread with state := { env := Bil.bind thread.state.env emu.config.memory memory } }
      | none => thread)

private def persistentRegionData (cells : List (Nat × UInt8)) (address size : Nat)
    (output : Array UInt8) : Array UInt8 :=
  if _h : output.size ≥ size then output else
    let expected := address + output.size
    match cells with
    | [] => output ++ Array.replicate (size - output.size) 0
    | (current, value) :: rest =>
      if current < expected then persistentRegionData rest address size output
      else if current = expected then persistentRegionData rest address size (output.push value)
      else persistentRegionData ((current, value) :: rest) address size (output.push 0)
termination_by cells.length + (size - output.size)
decreasing_by
  all_goals simp only [List.length_cons, Array.size_push]
  all_goals omega

private def regionsFromNative (emu : Emu) (native : Jit.Memory) : IO (List Region) := do
  let (addresses, values) ← Jit.dumpMemory native
  let cells := (addresses.zip values).toList.map fun cell => (cell.1.toNat, cell.2)
  let mapped ← emu.regions.get
  pure (mapped.map fun region =>
    { region with data := ByteArray.mk (persistentRegionData cells region.address region.data.size #[]) })

def snapshot (emu : Emu) : IO Snapshot := do
  let processes ← emu.processMemory.get
  let processMemory ← processes.toList.mapM fun (id, memory) => do
    let regions ← regionsFromNative emu memory
    pure (id, regions)
  pure {
    state := ← emu.state.get
    pc := ← emu.pc.get
    regions := ← emu.regions.get
    stopped := ← emu.stopped.get
    threads := ← captureThreads emu
    currentThread := ← emu.currentThreadRef.get
    nextThread := ← emu.nextThreadRef.get
    pending := ← emu.pendingRef.get
    processMemory
    skip := ← emu.skipCode.get
    table := ← emu.taskTable.get
  }

private def snapshotBlock (emu : Emu) : IO Snapshot := do
  pure {
    state := ← emu.state.get
    pc := ← emu.pc.get
    regions := ← emu.regions.get
    stopped := ← emu.stopped.get
    threads := ← emu.threadsRef.get
    currentThread := ← emu.currentThreadRef.get
    nextThread := ← emu.nextThreadRef.get
    pending := ← emu.pendingRef.get
    skip := ← emu.skipCode.get
    table := ← emu.taskTable.get
  }

private def restoreThreads (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  emu.state.set snapshot.state
  emu.pc.set snapshot.pc
  emu.regions.set snapshot.regions
  emu.stopped.set snapshot.stopped
  emu.threadsRef.set snapshot.threads
  emu.currentThreadRef.set snapshot.currentThread
  emu.nextThreadRef.set snapshot.nextThread
  emu.pendingRef.set snapshot.pending
  emu.skipCode.set snapshot.skip
  emu.taskTable.set snapshot.table

/-- A native memory with the bytes of the memory variable of `state`. -/
private def nativeFromState (emu : Emu) (state : Bil.State) : IO Jit.Memory := do
  match Bil.lookup state.env emu.config.memory with
  | .ok (.memory memory) =>
    let cells := Bap.Memory.cells memory
    let addresses := (cells.map fun cell => UInt64.ofNat cell.1.toNat).toArray
    let values := (cells.map fun cell => cell.2).toArray
    Jit.createMemory addresses values
  | .ok _ => throw <| IO.userError "Emu memory is not a memory value"
  | .error error => throw <| IO.userError error

/-- Makes `native` the memory of the thread that runs. -/
private def attachMemory (emu : Emu) (native : Jit.Memory) : IO Unit := do
  emu.engine.persistentMemory.set (some native)
  emu.engine.persistentVariable.set (some emu.config.memory)

/-- Undo a failed step. The memory of the state is exact, and a failed block may have written to the
native memory, which the state replaces. Threads created since the step started are gone again, and so
is their memory. A parallel worker leaves all of this to the rollback of its round. -/
private def rollbackBlock (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  let created ← emu.nextThreadRef.get
  restoreThreads emu snapshot
  Primus.Lifted.discardMemory emu.engine
  if !emu.engine.deferMemorySync then
    if created != snapshot.nextThread then
      emu.processMemory.modify fun processes => processes.filter fun id _ => id < snapshot.nextThread
    let space := snapshot.table.spaceOf snapshot.currentThread
    if (← emu.processMemory.get).contains space then
      let native ← nativeFromState emu snapshot.state
      emu.processMemory.modify (·.insert space native)
      attachMemory emu native

def restore (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  restoreThreads emu snapshot
  -- A compiled range holds the code of all of its blocks. A version of it stays, for when those come back.
  Primus.Lifted.forgetRanges emu.engine
  emu.parallelWorkers.set []
  emu.processMemory.set {}
  emu.sharedMemory.set none
  snapshot.processMemory.forM fun (id, regions) => do
    let cells := regions.flatMap fun region =>
      (List.range region.data.size).filterMap fun offset =>
        let value := region.data[offset]!
        if value = 0 then none else some (region.address + offset, value)
    let addresses := (cells.map fun cell => UInt64.ofNat cell.1).toArray
    let values := (cells.map fun cell => cell.2).toArray
    let memory ← Jit.createMemory addresses values
    emu.processMemory.modify (·.insert id memory)
  Primus.Lifted.discardMemory emu.engine
  match (← emu.processMemory.get).get? (snapshot.table.spaceOf snapshot.currentThread) with
  | some native => attachMemory emu native
  | none => pure ()

def thread (emu : Emu) : IO ThreadId := emu.currentThreadRef.get

def threads (emu : Emu) : IO (List ThreadInfo) := do
  let contexts ← captureThreads emu
  pure ((contexts.map fun context => ⟨context.id, context.pc, context.stopped⟩).mergeSort
    (fun left right => left.id ≤ right.id))

/-- Gives the engine the native memory of thread `next`, when it is not the one of `current`. -/
private def switchNativeMemory (emu : Emu) (current next : ThreadId) : IO Unit := do
  let currentSpace ← spaceOf emu current
  let nextSpace ← spaceOf emu next
  if currentSpace != nextSpace then
    let processes ← emu.processMemory.get
    let native ← emu.engine.persistentMemory.get
    match native with
    | some native =>
      if processes.contains currentSpace then emu.processMemory.modify (·.insert currentSpace native)
      else emu.sharedMemory.set (some native)
    | none => pure ()
    let processes ← emu.processMemory.get
    match nativeFor processes (← emu.sharedMemory.get) nextSpace with
    | some native => attachMemory emu native
    | none => Primus.Lifted.discardMemory emu.engine

def switchThread (emu : Emu) (id : ThreadId) : IO Unit := do
  saveCurrentThread emu
  let table ← emu.taskTable.get
  let leaving ← thread emu
  let leavingSpace := table.spaceOf leaving
  if table.spaceOf id != leavingSpace then
    match Bil.lookup (← emu.state.get).env emu.config.memory with
    | .ok memory =>
      emu.threadsRef.modify (parkShared · (fun other => table.spaceOf other != leavingSpace) emu.config.memory memory)
    | .error _ => pure ()
  let contexts ← emu.threadsRef.get
  match contexts.find? fun context => context.id == id with
  | none => throw <| IO.userError s!"unknown Emu thread {id}"
  | some context =>
    let current ← emu.state.get
    let env := if table.spaceOf id != leavingSpace then context.state.env else
      match Bil.lookup current.env emu.config.memory with
      | .ok memory => Bil.bind context.state.env emu.config.memory memory
      | .error _ => context.state.env
    switchNativeMemory emu leaving id
    emu.state.set { env }
    emu.pc.set context.pc
    emu.stopped.set context.stopped
    emu.currentThreadRef.set id
    emu.pendingRef.set context.pending
    emu.skipCode.set context.skip

def resumeThread (emu : Emu) (id : ThreadId) : IO Unit := do
  emu.threadControl.modify (·.insert id false)
  emu.threadsRef.modify (setThreadStopped · id false)
  if (← thread emu) == id then
    emu.stopped.set false

def stopThread (emu : Emu) (id : ThreadId) : IO Unit := do
  emu.threadControl.modify (·.insert id true)
  if (← thread emu) == id then
    emu.stopped.set true
  else
    emu.threadsRef.modify (setThreadStopped · id true)

private def hookContext (emu : Emu) : CodeHookContext := {
  engine := emu.engine
  state := emu.state
  pc := emu.pc
  stopped := emu.stopped
  currentThreadRef := emu.currentThreadRef
  trace := emu.trace
  lastFault := emu.lastFault
  skipCode := emu.skipCode
  pendingRef := emu.pendingRef
}

/-- The emulator a hook sees: its registers, memory and thread are of the thread that runs it. -/
private def withContext (emu : Emu) (context : CodeHookContext) : Emu := {
  emu with
    engine := context.engine
    state := context.state
    pc := context.pc
    stopped := context.stopped
    currentThreadRef := context.currentThreadRef
    trace := context.trace
    lastFault := context.lastFault
    skipCode := context.skipCode
    pendingRef := context.pendingRef
}

private def nextHookId (emu : Emu) : IO HookId := do
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  pure id

/-- Calls `action emu address` before each instruction of the range. -/
def onCode (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu code-hook range"
  let id ← nextHookId emu
  emu.hooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  pure id

/-- Calls `action emu address size` before each load of the range. -/
def onRead (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu read-hook range"
  let id ← nextHookId emu
  emu.readHooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  pure id

/-- Calls `action emu address size value` before each store of the range. -/
def onWrite (emu : Emu) (range : Nat × Nat) (action : Emu → Nat → Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu write-hook range"
  let id ← nextHookId emu
  emu.writeHooks.modify (· ++ [⟨id, range.1, range.2, fun context => action (withContext emu context)⟩])
  pure id

/-- Calls `action emu number arguments` at each system call. -/
def onSyscall (emu : Emu) (action : Emu → Nat → List Nat → IO SyscallAction) : IO HookId := do
  let id ← nextHookId emu
  emu.syscallHooks.modify (· ++ [⟨id, fun context => action (withContext emu context)⟩])
  pure id

/-- Calls `action emu address` at each intrinsic with this name, or at all of them with `"*"`. -/
def onIntrinsic (emu : Emu) (name : String) (action : Emu → Nat → IO IntrinsicAction) : IO HookId := do
  if name.isEmpty then
    throw <| IO.userError "intrinsic hook name is empty"
  let id ← nextHookId emu
  emu.intrinsicHooks.modify (· ++ [⟨id, name, fun context => action (withContext emu context)⟩])
  pure id

def removeHook (emu : Emu) (id : HookId) : IO Unit := do
  emu.hooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.readHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.writeHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.watchedSteps.set {}
  emu.syscallHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.intrinsicHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.breakpointsRef.modify fun breakpoints => breakpoints.filter fun breakpoint => breakpoint.1 != id

def clearHooks (emu : Emu) : IO Unit := do
  emu.hooks.set []
  emu.readHooks.set []
  emu.writeHooks.set []
  emu.watchedSteps.set {}
  emu.syscallHooks.set []
  emu.intrinsicHooks.set []
  emu.breakpointsRef.set []

def addBreakpoint (emu : Emu) (address : Nat) : IO HookId := do
  let id ← onCode emu (address, address) fun current _ => current.stopped.set true
  emu.breakpointsRef.modify fun breakpoints => (id, address) :: breakpoints
  pure id

def removeBreakpoint (emu : Emu) (address : Nat) : IO Unit := do
  let breakpoints ← emu.breakpointsRef.get
  (breakpoints.filter fun breakpoint => breakpoint.2 == address).forM fun breakpoint =>
    removeHook emu breakpoint.1

def breakpoints (emu : Emu) : IO (List Nat) := do
  let current ← emu.breakpointsRef.get
  pure (current.map Prod.snd).reverse

private def traceBeginPc (emu : Emu) (pcCapacity accessCapacity : Nat) (watch : Option (Nat × Nat)) : IO Unit :=
  emu.trace.set (some { pcCapacity, accessCapacity, watch })

private def traceBegin (emu : Emu) (capacity : Nat) (watch : Option (Nat × Nat)) : IO Unit :=
  traceBeginPc emu 0 capacity watch

def traceStart (emu : Emu) : IO Unit := traceBegin emu 0 none

def traceStartCapacity (emu : Emu) (capacity : Nat) : IO Unit := traceBeginPc emu capacity 0 none

def traceStartAccesses (emu : Emu) (capacity : Nat) : IO Unit := traceBegin emu capacity none

def traceStartWatch (emu : Emu) (range : Nat × Nat) (capacity : Nat) : IO Unit := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu trace watch range"
  traceBegin emu capacity (some range)

private def pcList (state : TraceState) : List Nat :=
  state.pcsFront ++ state.pcsBack.reverse

def traceStop (emu : Emu) : IO (List Nat) := do
  let current ← emu.trace.get
  emu.trace.set none
  pure (pcList (current.getD {}))

def tracePcs (emu : Emu) : IO (List Nat) := do
  let current ← emu.trace.get
  pure (pcList (current.getD {}))

def traceDroppedPcs (emu : Emu) : IO Nat := do
  let current ← emu.trace.get
  pure (current.getD {}).droppedPcs

def traceAccesses (emu : Emu) : IO (List TraceAccess) := do
  let current ← emu.trace.get
  pure (current.getD {}).accesses.reverse

def traceAccessesCount (emu : Emu) : IO Nat := do
  let current ← emu.trace.get
  pure (current.getD {}).accessCount

def traceDroppedAccesses (emu : Emu) : IO Nat := do
  let current ← emu.trace.get
  pure (current.getD {}).droppedAccesses

private def serialize (emu : Emu) (action : IO α) : IO α := do
  match ← emu.parallelLock.get with
  | some mutex =>
    Std.BaseMutex.lock mutex
    try action finally Std.BaseMutex.unlock mutex
  | none => action

private def recordTrace (emu : Emu) (address : Nat) : IO Unit := do
  if (← emu.trace.get).isNone then return
  serialize emu <| emu.trace.modify fun current => current.map fun state =>
    if state.pcCapacity = 0 then
      { state with pcsBack := address :: state.pcsBack, pcCount := state.pcCount + 1 }
    else if state.pcRetained < state.pcCapacity then
      { state with
        pcsBack := address :: state.pcsBack
        pcRetained := state.pcRetained + 1
        pcCount := state.pcCount + 1
      }
    else
      let (front, back) := if state.pcsFront.isEmpty then (state.pcsBack.reverse, []) else (state.pcsFront, state.pcsBack)
      match front with
      | [] =>
        { state with pcsBack := [address], pcCount := state.pcCount + 1, droppedPcs := state.droppedPcs + 1 }
      | _ :: rest =>
        { state with
          pcsFront := rest
          pcsBack := address :: back
          pcCount := state.pcCount + 1
          droppedPcs := state.droppedPcs + 1
        }

private def recordAccess (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  if (← emu.trace.get).isNone then return
  let pc ← emu.pc.get
  let thread ← emu.currentThreadRef.get
  emu.trace.modify fun current => current.map fun state =>
    if state.accessCapacity = 0 then state
    else if state.watch.any fun range => !accessTouches range.1 range.2 address size then state
    else
      let access : TraceAccess := {
        insn := state.pcCount - 1
        pc
        address
        size
        write
        value := if write then some value else none
        thread
      }
      let entries := access :: state.accesses
      let retained := entries.take state.accessCapacity
      { state with
        accesses := retained
        accessCount := state.accessCount + 1
        droppedAccesses := state.droppedAccesses + entries.length - retained.length
      }

private def notifyCode (emu : Emu) (address : Nat) : IO Unit := do
  if (← emu.hooks.get).isEmpty then return
  serialize emu <| do
  let hooks ← emu.hooks.get
  let context := hookContext emu
  (hooksForCode (·.first) (·.last) hooks address).forM fun hook =>
    hook.action context address

/-- Whether nothing watches the code that runs. -/
private def rangeIsQuiet (emu : Emu) : IO Bool := do
  pure ((← emu.hooks.get).isEmpty && (← emu.trace.get).isNone)

/-- The code site of a block inside a compiled range, whose first block is the step's. A block with hooks ends the range, with
the block not entered and its hooks not fired: they are the next step's, which has the state that they read. -/
private def observeRangeCode (emu : Emu) (address : Nat) : IO Bool := do
  emu.pc.set address
  let dirty := (← emu.engine.dirtyCode.get).isSome
  let late := (← emu.rangeQuiet.get) && !(← rangeIsQuiet emu)
  let hooked := !(hooksForCode (·.first) (·.last) (← emu.hooks.get) address).isEmpty
  -- A range that ends at its first site has done no good: where it starts, the step runs its one instruction by itself.
  match ← emu.rangeStart.get with
  | some start =>
    emu.rangeStart.set none
    if hooked then emu.watchedSteps.modify (·.insert start)
  | none => pure ()
  if rangeSiteStops dirty late hooked then return true
  recordTrace emu address
  pure false

def failure (emu : Emu) : IO (Option MemoryFault) := emu.lastFault.get

private def recordFault (emu : Emu) (operation : MemoryOperation) (address : Nat) : IO Unit := do
  let pc ← emu.pc.get
  let thread ← emu.currentThreadRef.get
  emu.lastFault.set (some ⟨pc, address, operation, thread⟩)

private def notifyMemory (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  let mapped ← emu.regions.get
  let fault (offset : Nat) : IO Unit := do
    let operation := if write then MemoryOperation.write else MemoryOperation.read
    recordFault emu operation (address + offset)
    throw <| IO.userError s!"Emu {repr operation} fault at {address + offset}"
  let takeBack (hit : Bool) : IO Unit := do
    if accessRestarts hit (← emu.lastBudget.get) emu.engine.deferMemorySync then
      emu.restarting.set true
      throw <| IO.userError s!"Emu step restarts at the watched access at {address}"
  let hooks : IO Unit :=
    if write then do
      match emu.journal with
      | some journal => journal.modify (journalWrite · address size)
      | none => pure ()
      let hit := hooksForAccess (·.first) (·.last) (← emu.writeHooks.get) address size
      takeBack !hit.isEmpty
      hit.forM fun hook => serialize emu <| hook.action (hookContext emu) address size value
    else do
      let hit := hooksForAccess (·.first) (·.last) (← emu.readHooks.get) address size
      takeBack !hit.isEmpty
      hit.forM fun hook => serialize emu <| hook.action (hookContext emu) address size
  notifyAccess mapped write address size fault
    (Primus.Lifted.markDirtyRange emu.engine address (address + size - 1))
    (recordAccess emu write address size value) hooks

private def cells (emu : Emu) (state : Bil.State) : IO (Σ width, Bap.Memory width) := do
  match Bil.lookup state.env emu.config.memory with
  | .ok (.memory memory) => pure ⟨_, memory⟩
  | .ok _ => throw <| IO.userError "Emu memory is not a memory value"
  | .error error => throw <| IO.userError error

def synchronizePersistentMemory (emu : Emu) : IO Unit := do
  match ← emu.engine.persistentMemory.get with
  | none => pure ()
  | some native =>
    let state ← emu.state.get
    let ⟨width, _⟩ ← cells emu state
    let (addresses, values) ← Jit.dumpMemory native
    let memory := Bap.Memory.writeSortedCells (Bap.Memory.empty width) ((addresses.zip values).toList.map fun cell =>
      (BitVec.ofNat width cell.1.toNat, cell.2))
    let contexts ← captureThreads emu
    emu.threadsRef.set (contexts.map fun context =>
      { context with state := { env := Bil.bind context.state.env emu.config.memory (.memory memory) } })
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory memory) }

private def rawByte (emu : Emu) (address : Nat) : IO UInt8 := do
  match ← emu.engine.persistentMemory.get with
  | some memory => Jit.readMemory memory (UInt64.ofNat address)
  | none =>
    let state ← emu.state.get
    let ⟨width, memory⟩ ← cells emu state
    pure (Bap.Memory.readByte memory (BitVec.ofNat width address))

/-- Whether every address in `lower`..`upper` lies in a region. -/
def coversRange (regions : List Region) (lower upper : Nat) : Bool :=
  let rec loop (fuel position : Nat) : Bool :=
    if position ≥ upper then true
    else
      match fuel with
      | 0 => false
      | fuel + 1 =>
        match lookupRegion regions position with
        | some region => loop fuel (region.address + region.data.size)
        | none => false
  loop regions.length lower

private def readByte (emu : Emu) (address : Nat) : IO UInt8 := do
  let regions ← emu.regions.get
  match lookupRegion regions address with
  | none => throw <| IO.userError s!"unmapped Emu address {address}"
  | some region =>
    if !region.protection.readable then
      throw <| IO.userError s!"unreadable Emu address {address}"
    rawByte emu address

def read (emu : Emu) (address size : Nat) : IO ByteArray := do
  -- An absurd size fails right here, instead of allocating before it fails.
  if !coversRange (← emu.regions.get) address (address + size) then
    throw <| IO.userError s!"unmapped Emu address in {size} bytes at {address}"
  let bytes ← (List.range size).mapM fun offset => readByte emu (address + offset)
  pure (ByteArray.mk bytes.toArray)

private def synchronizeWrite (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  let persistent ← emu.engine.persistentMemory.get
  let memoryVar ← emu.engine.persistentVariable.get
  match persistent, memoryVar with
  | some memory, some var =>
    if var = emu.config.memory then
      let addresses := (List.range data.size).map fun offset => UInt64.ofNat (address + offset)
      Jit.writeMemory memory addresses.toArray data.toList.toArray
    else Primus.Lifted.discardMemory emu.engine
  | _, _ => pure ()

private def writeByte (emu : Emu) (address : Nat) (value : UInt8) : IO Unit := do
  let mapped ← emu.regions.get
  match lookupRegion mapped address with
  | none => throw <| IO.userError s!"unmapped Emu address {address}"
  | some region =>
    if !region.protection.writable then
      throw <| IO.userError s!"read-only Emu address {address}"
    let state ← emu.state.get
    let ⟨width, memory⟩ ← cells emu state
    let updated := Bap.Memory.writeByte memory (BitVec.ofNat width address) value
    emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
    if region.protection.executable then Primus.Lifted.discardRange emu.engine address address
    synchronizeWrite emu address (ByteArray.mk #[value])
    emu.regions.set (mapped.map fun current =>
      if current.contains address then
        { current with data := current.data.set! (address - current.address) value }
      else current)

def write (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  if data.size > 0 then
    let mapped ← emu.regions.get
    match lookupRegion mapped address with
    | none => throw <| IO.userError s!"unmapped Emu address {address}"
    | some region =>
      if !region.protection.writable then
        throw <| IO.userError s!"read-only Emu address {address}"
      if address + data.size > region.address + region.data.size then
        throw <| IO.userError s!"Emu write exceeds region at {address}"
      let state ← emu.state.get
      let ⟨_, memory⟩ ← cells emu state
      let updated := Bap.Memory.writeRegion memory address data
      emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
      if region.protection.executable then
        Primus.Lifted.discardRange emu.engine address (address + data.size - 1)
      synchronizeWrite emu address data
      emu.regions.set (mapped.map fun current =>
        if current.contains address then
          let updatedData := (List.range data.size).foldl (init := current.data) fun bytes offset =>
            bytes.set! (address - current.address + offset) data[offset]!
          { current with data := updatedData }
        else current)

private def synchronizeBatch (emu : Emu) (writes : List (Nat × ByteArray)) : IO Unit := do
  let persistent ← emu.engine.persistentMemory.get
  let memoryVar ← emu.engine.persistentVariable.get
  match persistent, memoryVar with
  | some memory, some var =>
    if var = emu.config.memory then
      let addresses := writes.flatMap fun (address, data) =>
        (List.range data.size).map fun offset => UInt64.ofNat (address + offset)
      let bytes := writes.flatMap fun (_, data) => data.toList
      Jit.writeMemory memory addresses.toArray bytes.toArray
    else Primus.Lifted.discardMemory emu.engine
  | _, _ => pure ()

def writeBatch (emu : Emu) (writes : List (Nat × ByteArray)) : IO Unit := do
  let mapped ← emu.regions.get
  writes.forM fun (address, data) => do
    match lookupRegion mapped address with
    | none => throw <| IO.userError s!"unmapped Emu address {address}"
    | some region =>
      if !region.protection.writable then
        throw <| IO.userError s!"read-only Emu address {address}"
      if address + data.size > region.address + region.data.size then
        throw <| IO.userError s!"Emu write exceeds region at {address}"
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  let updated := writes.foldl (init := memory) fun memory (address, data) =>
    Bap.Memory.writeRegion memory address data
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  writes.forM fun (address, data) => do
    match lookupRegion mapped address with
    | some region =>
      if region.protection.executable && data.size > 0 then
        Primus.Lifted.discardRange emu.engine address (address + data.size - 1)
    | none => pure ()
  synchronizeBatch emu writes
  let updatedRegions := writes.foldl (init := mapped) fun regions (address, data) =>
    regions.map fun current =>
      if current.contains address then
        let offset := address - current.address
        { current with data := current.data.extract 0 offset ++ data ++
          current.data.extract (offset + data.size) current.data.size }
      else current
  emu.regions.set updatedRegions

private def checkInSpace (emu : Emu) (region : Region) : IO Unit := do
  match memoryWidth emu.config with
  | .ok width =>
    if !regionInSpace width region then
      throw <| IO.userError s!"Emu region at {region.address} exceeds the address space"
  | .error error => throw <| IO.userError error

def map (emu : Emu) (region : Region) : IO Unit := do
  checkInSpace emu region
  let mapped ← emu.regions.get
  if mapped.any fun current => overlaps current region then
    throw <| IO.userError s!"Emu region overlaps an existing mapping at {region.address}"
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  let updated := Bap.Memory.writeRegion memory region.address region.data
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  if region.protection.executable && region.data.size > 0 then
    Primus.Lifted.discardRange emu.engine region.address (region.address + region.data.size - 1)
  synchronizeWrite emu region.address region.data
  emu.regions.set (region :: mapped)

def overlay (emu : Emu) (region : Region) : IO Unit := do
  checkInSpace emu region
  let mapped ← emu.regions.get
  if overlayConflict mapped region then
    throw <| IO.userError s!"Emu overlay size mismatch at {region.address}"
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  let updated := Bap.Memory.writeRegion memory region.address region.data
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  if region.protection.executable && region.data.size > 0 then
    Primus.Lifted.discardRange emu.engine region.address (region.address + region.data.size - 1)
  synchronizeWrite emu region.address region.data
  emu.regions.set (region :: mapped.filter fun current => current.address != region.address)

private def regionPiece (region : Region) (first last : Nat) (protection : Primus.Protection) : List Region :=
  if first < last then
    [⟨first, region.data.extract (first - region.address) (last - region.address), protection⟩]
  else []

/-- Replace the protection of the bytes of `region` within `lower`..`upper`, keeping the rest. -/
def splitRegion (lower upper : Nat) (protection : Primus.Protection) (region : Region) : List Region :=
  let finish := region.address + region.data.size
  let start := max lower region.address
  let stop := min upper finish
  if stop ≤ start then [region]
  else if start = region.address && stop = finish then [{ region with protection }]
  else
    regionPiece region region.address start region.protection ++ regionPiece region start stop protection ++
      regionPiece region stop finish region.protection

/-- `mprotect`: only the bytes in the range change protection, and all of them must be mapped. -/
def protectRegions (regions : List Region) (address size : Nat) (protection : Primus.Protection) :
    Option (List Region) :=
  if coversRange regions address (address + size) then
    some (regions.flatMap (splitRegion address (address + size) protection))
  else none

def protect (emu : Emu) (address size : Nat) (protection : Primus.Protection) : IO Unit := do
  if size = 0 then pure ()
  else
    match protectRegions (← emu.regions.get) address size protection with
    | some regions =>
      emu.regions.set regions
      -- A compiled range would keep running code that lost its execute permission.
      if !protection.executable then Primus.Lifted.discardRange emu.engine address (address + size - 1)
    | none => throw <| IO.userError s!"unmapped Emu protection range at {address}"

def regions (emu : Emu) : IO (List (Nat × Nat × Primus.Protection)) := do
  let mapped ← emu.regions.get
  pure (mapped.map fun region => (region.address, region.data.size, region.protection))

def reg (emu : Emu) (var : Bap.Var) : IO Bap.Value := do
  let state ← emu.state.get
  match Bil.lookup state.env var with
  | .ok value => pure value
  | .error error => throw <| IO.userError error

def setReg (emu : Emu) (var : Bap.Var) (value : Bap.Value) : IO Unit := do
  if var.typ != value.type then
    throw <| IO.userError s!"register {var.name} has the wrong value type"
  emu.state.modify fun state => { env := Bil.bind state.env var value }
  -- The state now has the memory: what native memory has follows it, on the next access.
  if var == emu.config.memory then
    Primus.Lifted.discardMemory emu.engine
    let space ← spaceOf emu (← emu.currentThreadRef.get)
    if (← emu.processMemory.get).contains space then
      let native ← nativeFromState emu (← emu.state.get)
      emu.processMemory.modify (·.insert space native)
      attachMemory emu native

private def syscallRegisters : SyscallAbi → String × List String × String
  | .riscv => ("X17", ["X10", "X11", "X12", "X13", "X14", "X15"], "X10")
  | .x86_64 => ("RAX", ["RDI", "RSI", "RDX", "R10", "R8", "R9"], "RAX")
  | .aarch64 => ("X8", ["X0", "X1", "X2", "X3", "X4", "X5"], "X0")
  | .mips => ("R2", ["R4", "R5", "R6", "R7", "R8", "R9"], "R2")

private def wordWidth (emu : Emu) : IO Nat :=
  match memoryWidth emu.config with
  | .ok width => pure width
  | .error error => throw <| IO.userError error

private def readWord (emu : Emu) (name : String) : IO Nat := do
  let width ← wordWidth emu
  let value ← reg emu ⟨name, .imm width, 0, false⟩
  match Value.asBits value with
  | .ok value => pure value.2.toNat
  | .error error => throw <| IO.userError error

/-- The task that runs. -/
private def currentTask (emu : Emu) : IO Task := do
  let id ← thread emu
  match (← emu.taskTable.get).find? id with
  | some task => pure task
  | none => throw <| IO.userError s!"Emu thread {id} has no task"

/-- A new thread of the process that runs, in its address space. -/
private def newThread (emu : Emu) : IO ThreadId := do
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  emu.taskTable.modify (·.addTask { task with tid := id, status := none })
  pure id

def spawnThread (emu : Emu) (start : Nat) (arg : Nat) : IO ThreadId := do
  let id ← newThread emu
  let width ← wordWidth emu
  let (_, arguments, _) := syscallRegisters emu.config.syscallAbi
  match arguments.head? with
  | none => throw <| IO.userError "target has no thread argument register"
  | some register =>
    let current ← emu.state.get
    let argument : Bap.Var := ⟨register, .imm width, 0, false⟩
    let context := spawnContext id current argument (.bits (BitVec.ofNat width arg)) start
    emu.threadsRef.modify (context :: ·)
    pure id

def forkThread (emu : Emu) (childPc : Nat) : IO ThreadId := do
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  -- Its address space is that of its parent, until `cloneProcessMemory` gives it its own.
  emu.taskTable.modify (·.addTask { tid := id, group := id, parent := task.group, space := task.space })
  let width ← wordWidth emu
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  let current ← emu.state.get
  let result : Bap.Var := ⟨register, .imm width, 0, false⟩
  let context := forkContext id current result (.bits (BitVec.ofNat width 0)) childPc
  emu.threadsRef.modify (context :: ·)
  pure id

/-- The stack pointer and the thread pointer of a target. -/
private def threadRegisters : SyscallAbi → String × String
  | .riscv => ("X2", "X4")
  | .x86_64 => ("RSP", "FS_BASE")
  | .aarch64 => ("SP", "TPIDR_EL0")
  | .mips => ("R29", "USERLOCAL")

def cloneProcessMemory (emu : Emu) (child : ThreadId) : IO Unit := do
  let parent ← match ← emu.engine.persistentMemory.get with
    | some parent => pure parent
    | none =>
      let parent ← nativeFromState emu (← emu.state.get)
      attachMemory emu parent
      pure parent
  let childMemory ← Jit.cloneMemory parent
  emu.taskTable.modify (·.setSpace child child)
  emu.processMemory.modify (·.insert child childMemory)
  -- The memory of the child's state follows the clone, whatever ran since the fork. A parallel worker has
  -- it in native memory only, and the rest of the emulator expects the state to be exact.
  let state ← emu.state.get
  let memory ← if emu.engine.deferMemorySync then do
      let ⟨width, _⟩ ← cells emu state
      let (addresses, values) ← Jit.dumpMemory childMemory
      pure (.ok (Value.memory (Bap.Memory.writeSortedCells (Bap.Memory.empty width)
        ((addresses.zip values).toList.map fun cell => (BitVec.ofNat width cell.1.toNat, cell.2)))))
    else pure (Bil.lookup state.env emu.config.memory)
  match memory with
  | .ok memory =>
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == child then { context with state := { env := Bil.bind context.state.env emu.config.memory memory } }
      else context
  | .error _ => pure ()
  if (← emu.currentThreadRef.get) == child then
    emu.sharedMemory.set (some parent)
    attachMemory emu childMemory

def threadReg (emu : Emu) (id : ThreadId) (var : Bap.Var) : IO Bap.Value := do
  let contexts ← captureThreads emu
  match contexts.find? fun context => context.id == id with
  | none => throw <| IO.userError s!"unknown Emu thread {id}"
  | some context =>
    match Bil.lookup context.state.env var with
    | .ok value => pure value
    | .error error => throw <| IO.userError error

def setThreadReg (emu : Emu) (id : ThreadId) (var : Bap.Var) (value : Bap.Value) : IO Unit := do
  if (← thread emu) == id then
    setReg emu var value
  else
    if var.typ != value.type then
      throw <| IO.userError s!"register {var.name} has the wrong value type"
    saveCurrentThread emu
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == id then { context with state := { env := Bil.bind context.state.env var value } }
      else context

/-! ### Tasks -/

/-- The process that runs: the id of its group. -/
def pid (emu : Emu) : IO Nat := do pure (← currentTask emu).group

/-- The parent of the process that runs, or 0 for the first. -/
def parentPid (emu : Emu) : IO Nat := do pure (← currentTask emu).parent

def tasks (emu : Emu) : IO (List Task) := do pure (← emu.taskTable.get).tasks

/-- What a new task shares, as the flags of `clone(2)` say it. -/
structure CloneOptions where
  start : Nat
  /-- The stack it runs on. Without one it keeps the stack pointer of its parent, and tasks with the same memory then
  overwrite each other's frames. -/
  stack : Option Nat := none
  threadPointer : Option Nat := none
  /-- `CLONE_VM`: the same address space, and otherwise a copy of it. -/
  shareMemory : Bool := false
  /-- `CLONE_THREAD`: a thread of the same process, and otherwise a process of its own. -/
  sameGroup : Bool := false

/-- A new task, which runs at once with a copy of the registers and sees 0 in the result register. A thread and a process
are this, with different options. -/
def clone (emu : Emu) (options : CloneOptions) : IO ThreadId := do
  if options.sameGroup && !options.shareMemory then
    throw <| IO.userError "a thread of a process shares its memory"
  let task ← currentTask emu
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  let group := if options.sameGroup then task.group else id
  let parent := if options.sameGroup then task.parent else task.group
  emu.taskTable.modify (·.addTask { tid := id, group, parent, space := task.space })
  let width ← wordWidth emu
  let word (value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)
  let var (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
  let (_, _, result) := syscallRegisters emu.config.syscallAbi
  let (stackRegister, threadRegister) := threadRegisters emu.config.syscallAbi
  let current ← emu.state.get
  let bindIn (env : List (Bap.Var × Bap.Value)) (name : String) : Option Nat → List (Bap.Var × Bap.Value)
    | some value => Bil.bind env (var name) (word value)
    | none => env
  let env := bindIn (bindIn current.env stackRegister options.stack) threadRegister options.threadPointer
  emu.threadsRef.modify (spawnContext id { env } (var result) (word 0) options.start :: ·)
  if !options.shareMemory then cloneProcessMemory emu id
  pure id

/-- A new process at `childPc`, with a copy of the memory. -/
def fork (emu : Emu) (childPc : Nat) : IO ThreadId := clone emu { start := childPc }

/-- All of the process has exited: its threads stop, its children go to the first process and it waits as a zombie. -/
private def markExited (emu : Emu) (group status : Nat) : IO Unit := do
  let table ← emu.taskTable.get
  let init := match table.tasks.head? with
    | some first => first.tid
    | none => group
  emu.taskTable.set (table.exitGroup group status init)
  let current ← thread emu
  for task in table.tasks do
    if task.group == group then
      if task.tid == current then emu.stopped.set true
      else emu.threadsRef.modify (setThreadStopped · task.tid true)

/-- The process that runs calls `exit_group` with `code`. -/
def exitProcess (emu : Emu) (code : Nat) : IO Unit := do
  markExited emu (← currentTask emu).group (exitedStatus code)

/-- The thread that runs is over, and its process if that was the last of it. -/
def exitThread (emu : Emu) (code : Nat) : IO Unit := do
  let table ← emu.taskTable.get
  let init := match table.tasks.head? with
    | some first => first.tid
    | none => 0
  emu.taskTable.set (table.exitTask (← thread emu) (exitedStatus code) init)
  emu.stopped.set true

/-- A signal ends the process. Nothing else of signals is modelled. -/
def kill (emu : Emu) (target signal : Nat) : IO Unit := do
  match (← emu.taskTable.get).find? target with
  | some { status := none, .. } => markExited emu target (signaledStatus signal)
  | _ => throw <| IO.userError s!"no running Emu process {target}"

/-- Forgets the threads and the memory of what is no longer in the table. What runs stays until it switches away, since
switching keeps the memory it leaves. -/
private def collectGone (emu : Emu) : IO Unit := do
  let current ← thread emu
  emu.taskTable.modify (·.sweep current)
  let table ← emu.taskTable.get
  emu.threadsRef.modify (·.filter fun context => context.id == current || (table.find? context.id).isSome)
  emu.processMemory.modify (·.filter fun space _ => table.tasks.any (·.space == space))

/-- What `waitpid` reports now, in the process that runs, without blocking. What it reports is gone from the table. -/
def waitpid (emu : Emu) (target : Option Nat := none) : IO WaitResult := do
  let table ← emu.taskTable.get
  let result := table.poll (← currentTask emu).group target
  if let .exited child _ := result then
    emu.taskTable.set (table.reap child)
    collectGone emu
  pure result

/-- A result in the convention of the target: an error is the negated number, except on MIPS, where the register after
the arguments says so. -/
private def setSyscallResult (emu : Emu) (id : ThreadId) (result : Except Nat Nat) : IO Unit := do
  let width ← wordWidth emu
  let word (value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)
  let var (name : String) : Bap.Var := ⟨name, .imm width, 0, false⟩
  let (_, _, register) := syscallRegisters emu.config.syscallAbi
  match emu.config.syscallAbi, result with
  | .mips, .ok value =>
    setThreadReg emu id (var "R7") (word 0)
    setThreadReg emu id (var register) (word value)
  | .mips, .error errno =>
    setThreadReg emu id (var "R7") (word 1)
    setThreadReg emu id (var register) (word errno)
  | _, .ok value => setThreadReg emu id (var register) (word value)
  | _, .error errno => setThreadReg emu id (var register) (word (2 ^ width - errno))

private def echild : Nat := 10
private def efault : Nat := 14
private def einval : Nat := 22
private def enosys (abi : SyscallAbi) : Nat := if abi == .mips then 89 else 38

/-- Writes the 32 bits of a status, and says whether that address could take them. -/
private def writeStatus (emu : Emu) (address status : Nat) : IO Bool := do
  let bytes := [0, 1, 2, 3].map fun index => (status >>> (8 * index)).toUInt8
  let bytes := if emu.config.endian == .big then bytes.reverse else bytes
  try
    write emu address (ByteArray.mk bytes.toArray)
    pure true
  catch _ => pure false

/-- The waiters that can go on, each with its status written in its memory and its result in its registers. Not during a
step: this switches threads. A zombie that runs and that one of them reaps stops being what runs first, as what runs needs
its address space. -/
private def settleWaiters (emu : Emu) : IO Unit := do
  let (table, woken) := (← emu.taskTable.get).settle
  if let some (first, _) := woken.head? then
    if (table.find? (← thread emu)).isNone then switchThread emu first.thread
  emu.taskTable.set table
  for (waiter, found) in woken do
    let result : Except Nat Nat ← match found with
      | .exited child status =>
        match waiter.statusAddress with
        | some address =>
          let home ← thread emu
          switchThread emu waiter.thread
          let written ← writeStatus emu address status
          switchThread emu home
          pure (if written then .ok child else .error efault)
        | none => pure (.ok child)
      | _ => pure (.error echild)
    setSyscallResult emu waiter.thread result
    resumeThread emu waiter.thread
  if !woken.isEmpty then collectGone emu

/-- The numbers of the system calls of processes, as in Linux. -/
private structure ProcessCalls where
  fork : Option Nat := none
  vfork : Option Nat := none
  clone : Nat
  wait4 : Nat
  waitpid : Option Nat := none
  exit : Nat
  exitGroup : Nat
  getpid : Nat
  getppid : Nat
  gettid : Nat
  schedYield : Nat

private def processCalls (abi : SyscallAbi) (width : Nat) : ProcessCalls :=
  match abi with
  | .x86_64 =>
    { fork := some 57, vfork := some 58, clone := 56, wait4 := 61, exit := 60, exitGroup := 231, getpid := 39,
      getppid := 110, gettid := 186, schedYield := 24 }
  | .riscv | .aarch64 =>
    { clone := 220, wait4 := 260, exit := 93, exitGroup := 94, getpid := 172, getppid := 173, gettid := 178,
      schedYield := 124 }
  | .mips =>
    if width == 32 then
      { fork := some 4002, clone := 4120, wait4 := 4114, waitpid := some 4007, exit := 4001, exitGroup := 4246,
        getpid := 4020, getppid := 4064, gettid := 4222, schedYield := 4162 }
    else
      { fork := some 5056, vfork := some 5057, clone := 5055, wait4 := 5059, exit := 5058, exitGroup := 5205,
        getpid := 5038, getppid := 5108, gettid := 5178, schedYield := 5023 }

/-- `SyscallAction` of a result. -/
private def syscallReturn (emu : Emu) (result : Except Nat Nat) : IO SyscallAction := do
  let width ← wordWidth emu
  match emu.config.syscallAbi, result with
  | .mips, .ok value =>
    setThreadReg emu (← thread emu) ⟨"R7", .imm width, 0, false⟩ (.bits (BitVec.ofNat width 0))
    pure (.returnValue value)
  | .mips, .error errno =>
    setThreadReg emu (← thread emu) ⟨"R7", .imm width, 0, false⟩ (.bits (BitVec.ofNat width 1))
    pure (.returnValue errno)
  | _, .ok value => pure (.returnValue value)
  | _, .error errno => pure (.returnValue (2 ^ width - errno))

/-- `wait4` without the usage of what it reports, and process groups, which aren't modelled. A thread that has to wait
stops here, and `runProcesses` gives it its result. -/
private def serveWait (emu : Emu) (target status options usage : Nat) : IO SyscallAction := do
  let width ← wordWidth emu
  let wanted : Option (Option Nat) :=
    if target == 2 ^ width - 1 then some none
    else if 0 < target && target < 2 ^ (width - 1) then some (some target)
    else none
  match wanted with
  | none => syscallReturn emu (.error einval)
  | some wanted =>
    if usage != 0 then syscallReturn emu (.error einval) else
    let table ← emu.taskTable.get
    let found := table.poll (← currentTask emu).group wanted
    match found with
    | .noChild => syscallReturn emu (.error echild)
    | .exited child value =>
      if status != 0 then
        if !(← writeStatus emu status value) then
          return ← syscallReturn emu (.error efault)
      emu.taskTable.set (table.reap child)
      collectGone emu
      syscallReturn emu (.ok child)
    | .running =>
      -- WNOHANG
      if options &&& 1 != 0 then syscallReturn emu (.ok 0)
      else
        emu.taskTable.set { table with waiters := table.waiters ++ [{
          thread := ← thread emu, target := wanted, statusAddress := if status != 0 then some status else none }] }
        emu.stopped.set true
        syscallReturn emu (.ok 0)

/-- `clone`. `CLONE_CHILD_CLEARTID` is taken and has no effect: there is no futex to wake, so a thread that waits on it is a
system call that nothing serves. `CLONE_VFORK` isn't taken. -/
private def serveClone (emu : Emu) (flags stack parentTid threadPointer childTid : Nat) : IO SyscallAction := do
  let cloneVm := 0x100
  let cloneThreadFlag := 0x10000
  let setTls := 0x80000
  let setParentTid := 0x100000
  let setChildTid := 0x1000000
  let known := 0xff ||| cloneVm ||| 0x200 ||| 0x400 ||| 0x800 ||| cloneThreadFlag ||| 0x40000 ||| setTls ||| setParentTid |||
    0x200000 ||| setChildTid
  let has (flag : Nat) : Bool := flags &&& flag != 0
  let abi := emu.config.syscallAbi
  let tidBytes (id : Nat) : ByteArray :=
    let bytes := [0, 1, 2, 3].map fun index => (id >>> (8 * index)).toUInt8
    ByteArray.mk (if emu.config.endian == .big then bytes.reverse else bytes).toArray
  if flags ||| known != known then
    syscallReturn emu (.error (enosys abi))
  else if has cloneThreadFlag && !has cloneVm then
    syscallReturn emu (.error einval)
  else
    let next ← emu.nextPc.get
    let options : CloneOptions := {
      start := next
      stack := if stack != 0 then some stack else none
      threadPointer := if has setTls then some threadPointer else none
      shareMemory := has cloneVm
      sameGroup := has cloneThreadFlag }
    if has cloneVm || !has setChildTid then
      let id ← clone emu options
      if has setParentTid then write emu parentTid (tidBytes id)
      if has setChildTid then write emu childTid (tidBytes id)
      syscallReturn emu (.ok id)
    else
      -- The copy holds the id of the child, and the parent keeps what was there.
      let before ← read emu childTid 4
      write emu childTid (tidBytes (← emu.nextThreadRef.get))
      let id ← clone emu options
      write emu childTid before
      if has setParentTid then write emu parentTid (tidBytes id)
      syscallReturn emu (.ok id)

/-- The system calls of processes, as Linux has them, for programs that `runProcesses` runs: `fork`, `vfork`, which is
`fork` as the standard allows, `clone`, `wait4`, `waitpid`, `exit`, `exit_group`, `getpid`, `getppid`, `gettid` and
`sched_yield`, which goes on until the quantum ends. Parallel rounds can't serve them, since a worker has no thread table
to block in, and a call from one fails. -/
def serveProcessCalls (emu : Emu) : IO HookId := do
  let width ← wordWidth emu
  let calls := processCalls emu.config.syscallAbi width
  let threadPointerIndex := if emu.config.syscallAbi == .x86_64 then 4 else 3
  let childTidIndex := if emu.config.syscallAbi == .x86_64 then 3 else 4
  onSyscall emu fun current number args => do
    let arg (index : Nat) : Nat := args.getD index 0
    let known := [some calls.clone, some calls.wait4, calls.waitpid, calls.fork, calls.vfork, some calls.exit,
      some calls.exitGroup, some calls.getpid, some calls.getppid, some calls.gettid, some calls.schedYield]
    if !known.contains (some number) then
      pure .default
    else
      if current.engine.deferMemorySync then
        throw <| IO.userError "process system calls need runProcesses, not a parallel round"
      if some number == calls.fork || some number == calls.vfork then
        syscallReturn current (.ok (← fork current (← current.nextPc.get)))
      else if number == calls.clone then
        serveClone current (arg 0) (arg 1) (arg 2) (arg threadPointerIndex) (arg childTidIndex)
      else if number == calls.wait4 then
        serveWait current (arg 0) (arg 1) (arg 2) (arg 3)
      else if some number == calls.waitpid then
        serveWait current (arg 0) (arg 1) (arg 2) 0
      else if number == calls.exit then
        exitThread current (arg 0)
        syscallReturn current (.ok 0)
      else if number == calls.exitGroup then
        exitProcess current (arg 0)
        syscallReturn current (.ok 0)
      else if number == calls.getpid then
        syscallReturn current (.ok (← pid current))
      else if number == calls.getppid then
        syscallReturn current (.ok (← parentPid current))
      else if number == calls.gettid then
        syscallReturn current (.ok (← thread current))
      else
        syscallReturn current (.ok 0)

private def dispatchSyscall (emu : Emu) : IO (Option Nat) := serialize emu <| do
  let hooks ← emu.syscallHooks.get
  if hooks.isEmpty then
    pure none
  else
    let width ← wordWidth emu
    let (numberRegister, argumentRegisters, resultRegister) := syscallRegisters emu.config.syscallAbi
    let number ← readWord emu numberRegister
    let args ← argumentRegisters.mapM (readWord emu)
    let context := hookContext emu
    let rec serve : List SyscallHook → IO (Option Nat)
      | [] => pure none
      | hook :: rest => do
        match ← hook.action context number args with
        | .returnValue value =>
          setReg emu ⟨resultRegister, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))
          pure (some value)
        | .default => serve rest
    serve hooks

private def dispatchIntrinsic (emu : Emu) (name : String) : IO Bool := serialize emu <| do
  let address ← emu.pc.get
  let hooks ← emu.intrinsicHooks.get
  let selected := hooks.filter fun hook => hook.name == "*" || hook.name == name
  let rec serve : List IntrinsicHook → IO Bool
    | [] => pure false
    | hook :: rest => do
      match ← hook.action (hookContext emu) address with
      | .proceed => pure true
      | .default => serve rest
  serve selected

def pc (emu : Emu) : IO Nat := emu.pc.get

def setPc (emu : Emu) (address : Nat) : IO Unit := do
  emu.pc.set address
  emu.pendingRef.set none
  emu.skipCode.set none

def stop (emu : Emu) : IO Unit := emu.stopped.set true

def resume (emu : Emu) : IO Unit := emu.stopped.set false

def stopped (emu : Emu) : IO Bool := emu.stopped.get

/-- How many bytes from `address` may be fetched, up to `limit`, through adjacent executable regions.
Only execute permission matters: instruction fetch does not read data. -/
def fetchSpan (regions : List Region) (address limit : Nat) : Except String Nat :=
  let rec extend (fuel position : Nat) : Nat :=
    if position ≥ address + limit then limit
    else
      match fuel, lookupRegion regions position with
      | fuel + 1, some region =>
        if region.protection.executable then extend fuel (region.address + region.data.size)
        else position - address
      | _, _ => position - address
  match lookupRegion regions address with
  | none => .error s!"unmapped Emu instruction address {address}"
  | some region =>
    if !region.protection.executable then
      .error s!"non-executable Emu instruction address {address}"
    else
      .ok (extend regions.length (region.address + region.data.size))

private def fetch (emu : Emu) (address : Nat) : IO ByteArray := do
  try
    let limit := match emu.config.syscallAbi with | .x86_64 => 16 | _ => 4
    match fetchSpan (← emu.regions.get) address limit with
    | .error error => throw <| IO.userError error
    | .ok span =>
      match ← emu.engine.persistentMemory.get with
      | some memory =>
        (List.range span).foldlM (init := ByteArray.emptyWithCapacity span) fun bytes offset => do
          pure (bytes.push (← Jit.readMemory memory (UInt64.ofNat (address + offset))))
      | none =>
        let ⟨_, memory⟩ ← cells emu (← emu.state.get)
        pure (peekBytes memory address span)
  catch error =>
    recordFault emu .fetch address
    throw error

private def lift (emu : Emu) (address : Nat) (code : ByteArray) : IO Primus.Lifted.Block := do
  let disassembler ← match emu.config.disassemblerAt with
    | some create => create address
    | none => pure emu.config.disassembler
  let decoded ← disassembler.decode address code
  match decoded with
  | .error error => throw <| IO.userError s!"Emu instruction at {address}: {error}"
  | .ok insn => pure ⟨insn.address, insn.next, insn.bil⟩

def refreshRegions (emu : Emu) : IO Unit := do
  let mapped ← emu.regions.get
  let state ← emu.state.get
  let ⟨_, memory⟩ ← cells emu state
  emu.regions.set (mapped.map fun region =>
    { region with data := Bap.Memory.readRegion memory region.address region.data.size })

def refreshPersistentRegions (emu : Emu) : IO Unit := do
  match ← emu.engine.persistentMemory.get with
  | none => refreshRegions emu
  | some native =>
    emu.regions.set (← regionsFromNative emu native)

/-- Refreshes the regions with the bytes of the memory that threads without their own memory share. -/
def refreshSharedRegions (emu : Emu) : IO Unit := do
  let processes ← emu.processMemory.get
  let table ← emu.taskTable.get
  if !processes.contains (table.spaceOf (← emu.currentThreadRef.get)) then
    refreshPersistentRegions emu
  else
    match ← emu.sharedMemory.get with
    | some native => emu.regions.set (← regionsFromNative emu native)
    | none =>
      let threads ← emu.threadsRef.get
      match threads.find? fun context => !processes.contains (table.spaceOf context.id) with
      | some context =>
        let ⟨_, memory⟩ ← cells emu context.state
        emu.regions.modify (·.map fun region =>
          { region with data := Bap.Memory.readRegion memory region.address region.data.size })
      | none => pure ()

private def mipsWord (code : ByteArray) (address : Nat) : Option Nat :=
  if address + 4 > code.size then none
  else
    some ((List.range 4).foldl (init := 0) fun word offset =>
      word * 256 + code[address + offset]!.toNat)

private def mipsDelayed (release6 : Bool) (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  let funct := word % 64
  match op with
  | 0x02 | 0x03 | 0x04 | 0x05 => true
  | 0x06 | 0x07 => !release6 || rt = 0
  | 0x14 | 0x15 | 0x16 | 0x17 => !release6
  | 0x01 =>
    (if release6 then [0x00, 0x01, 0x10, 0x11]
     else [0x00, 0x01, 0x02, 0x03, 0x10, 0x11, 0x12, 0x13]).contains rt
  | 0x00 => funct = 0x08 || funct = 0x09
  | 0x11 => if release6 then rs = 0x09 || rs = 0x0D else rs = 0x08
  | _ => false

private def mipsLikely (release6 : Bool) (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  !release6 && match op with
  | 0x14 | 0x15 | 0x16 | 0x17 => true
  | 0x01 => [0x02, 0x03, 0x12, 0x13].contains rt
  | 0x11 => rs = 0x08 && rt &&& 2 != 0
  | _ => false

private def mipsCompact (word : Nat) : Bool :=
  let op := (word / 2 ^ 26) % 64
  let rs := (word / 2 ^ 21) % 32
  let rt := (word / 2 ^ 16) % 32
  match op with
  | 0x06 | 0x07 | 0x16 | 0x17 => rt != 0
  | 0x08 | 0x18 => true
  | 0x36 | 0x3E => rs != 0
  | _ => false

private def delayFor (emu : Emu) (address : Nat) : IO DelayKind := do
  match emu.config.delayPolicy with
  | .none => pure .none
  | .mips release6 =>
    let code ← fetch emu address
    -- `mipsWord` reads the most significant byte first
    let code := if emu.config.endian == .little then ByteArray.mk (code.extract 0 4).toList.reverse.toArray else code
    match mipsWord code 0 with
    | none => pure .none
    | some word =>
      if mipsLikely release6 word then pure .likely
      else if mipsDelayed release6 word then pure .delayed
      else if release6 && mipsCompact word then pure .forbidden
      else pure .none

private def dispatchSpecial (emu : Emu) (name : String) : IO Bool := do
  if name == "syscall" || name == "svc" then
    match ← dispatchSyscall emu with
    | some _ => pure true
    | none => dispatchIntrinsic emu name
  else
    dispatchIntrinsic emu name

/-- The references of a step that may run a range. -/
@[inline] private def rangeCells (emu : Emu) : RangeCells IO where
  budget := emu.budget.get
  setBudget := emu.budget.set
  lastBudget := emu.lastBudget.get
  setLastBudget := emu.lastBudget.set
  chained := emu.engine.chained.get
  setChained := emu.engine.chained.set
  watched := fun address => do pure ((← emu.watchedSteps.get).contains address)
  watch := fun address => emu.watchedSteps.modify (·.insert address)
  restarting := emu.restarting.get
  setRestarting := emu.restarting.set
  pc := emu.pc.get
  pending := emu.pendingRef.get
  accessHooks := do pure !((← emu.readHooks.get).isEmpty && (← emu.writeHooks.get).isEmpty)
  deferred := emu.engine.deferMemorySync

/-- A run of the instruction at `address` that may chain as many as `budget` after it, on the state of the emulator. -/
private def runRange (emu : Emu) (address budget : Nat) : IO (Nat × Bil.Effect) := do
  let state ← emu.state.get
  let quiet ← rangeIsQuiet emu
  emu.rangeQuiet.set quiet
  emu.rangeStart.set (some address)
  let result ← Primus.Lifted.runBlockObserved emu.engine (fetch emu) (lift emu) state address
    (some (notifyMemory emu)) (some (observeRangeCode emu)) (!quiet) budget
  Primus.Lifted.flushDirtyRange emu.engine
  emu.state.set result.state
  emu.lastFault.set none
  pure (result.next, result.effect)

/-- The instruction at `address`, on the state of the emulator. -/
private def executeBlock (emu : Emu) (address : Nat) : IO (Nat × Bil.Effect) :=
  executeRangeM (rangeCells emu) (runRange emu) address

/-- The references that say where the thread of the emulator is. -/
@[inline] private def controlCells (emu : Emu) : ControlCells IO where
  stopped := emu.stopped.get
  setStopped := emu.stopped.set
  pc := emu.pc.get
  skip := emu.skipCode.get
  setSkip := emu.skipCode.set
  pending := emu.pendingRef.get
  setControl := fun pc pending => do
    emu.pc.set pc
    emu.pendingRef.set pending

/-- The references of the emulator as the environment of `stepM`. -/
@[inline] private def stepOps (emu : Emu) : StepOps IO (Snapshot × Option TraceState) :=
  stepOpsOf (controlCells emu) (notifyCode emu) (do pure (← snapshotBlock emu, ← emu.trace.get)) (delayFor emu)
    (recordTrace emu)
    (fun address => do
      let result ← executeBlock emu address
      emu.nextPc.set result.1
      pure result)
    (dispatchSpecial emu)
    (fun before => do
      rollbackBlock emu before.1
      emu.trace.set before.2)
    (fun pc => do
      match ← emu.lastFault.get with
      | some fault => emu.lastFault.set (some { fault with pc })
      | none => pure ())

/-- One instruction, whatever a run that a hook stopped had left for its next step. -/
def step (emu : Emu) : IO Bool := do
  emu.budget.set 0
  stepM (ε := IO.Error) (stepOps emu)

/-- Up to `maxSteps` instructions. Those of a compiled range count as well, and it stops where they run out. A fault in a
range leaves everything as single steps do. A worker of a parallel round leaves that to the rollback of its round. -/
def run (emu : Emu) (maxSteps : Nat := 100000) : IO Nat :=
  if rangeLimitOf emu.config ≤ 1 then
    runM (stepM (ε := IO.Error) (stepOps emu)) maxSteps 0
  else
    runPreciseM (runChainedM (restartM (stepM (ε := IO.Error) (stepOps emu)) (rangeRestartM (rangeCells emu))) (rangeAllowM (rangeCells emu))
        (rangeCells emu).chained maxSteps maxSteps 0)
      (step emu) (rangeAgainM (rangeCells emu)) (maxSteps + 1)

private def switchNextThread (emu : Emu) : IO Bool := do
  saveCurrentThread emu
  let current ← thread emu
  match pickNext (← emu.threadsRef.get) current with
  | some id =>
    switchThread emu id
    pure true
  | none => pure !(← stopped emu)

def resumeNext (emu : Emu) : IO Unit := do
  if ← stopped emu then
    let _ ← switchNextThread emu
    pure ()
  else
    resume emu

def runQuantum (emu : Emu) (quantum : Nat) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  let steps ← run emu quantum
  let _ ← switchNextThread emu
  pure steps

def runPreemptive (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  preemptiveM (run emu ·) (stopped emu) (switchNextThread emu) quantum fuel (fuel + 1) fuel 0

/-- How a run of processes ended. -/
inductive ScheduleOutcome where
  /-- Nothing can run, and the first process ended with this status. -/
  | finished (status : Nat)
  /-- Nothing can run, and these threads wait for what never happens. -/
  | deadlock (waiting : List ThreadId)
  /-- The thread stopped for a reason of its own, such as a breakpoint, and it is the current one. -/
  | stopped (id : ThreadId)
  | outOfFuel
  deriving DecidableEq, Repr

/-- Whether the thread stopped because it waits or is over, which is for the scheduler to deal with. -/
private def blockedOrOver (emu : Emu) (id : ThreadId) : IO Bool := do
  let table ← emu.taskTable.get
  if table.waiters.any (·.thread == id) then pure true
  else
    match table.find? id with
    | some task => pure task.status.isSome
    | none => pure true

/-- A guest that faults gets SIGSEGV, which ends its process and not the others. Anything else isn't the guest's doing. -/
private def runGuest (emu : Emu) (steps : Nat) : IO Nat := do
  try
    run emu steps
  catch error =>
    if (← failure emu).isSome then
      markExited emu (← currentTask emu).group (signaledStatus 11)
      emu.lastFault.set none
      pure 1
    else
      throw error

private def scheduleLoop (emu : Emu) (quantum : Nat) : Nat → Nat → IO ScheduleOutcome
  | 0, _ => pure .outOfFuel
  | rounds + 1, fuel => do
    settleWaiters emu
    let current ← thread emu
    if ← stopped emu then
      if !(← blockedOrOver emu current) then
        pure (.stopped current)
      else
        saveCurrentThread emu
        match pickNext (← emu.threadsRef.get) current with
        | some id =>
          switchThread emu id
          collectGone emu
          scheduleLoop emu quantum rounds fuel
        | none =>
          let table ← emu.taskTable.get
          if !table.waiters.isEmpty then
            pure (.deadlock (table.waiters.map (·.thread)))
          else
            match table.tasks.head? with
            | some { status := some status, .. } => pure (.finished status)
            | _ => pure (.stopped current)
    else if fuel == 0 then
      pure .outOfFuel
    else
      let steps ← runGuest emu (min quantum fuel)
      if !(← stopped emu) then
        let _ ← switchNextThread emu
      scheduleLoop emu quantum rounds (fuel - steps)

/-- Runs the processes and their threads in turns of `quantum` instructions, until nothing can run, a thread stops for a
reason of its own or `fuel` instructions have run. A thread blocked in `waitpid` goes on when what it waits for has
happened. A process that faults ends with SIGSEGV. The fuel is that of a `runPreemptive`, and each turn runs at least one
instruction or moves on from a thread that can't, so that the rounds are enough. -/
def runProcesses (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO ScheduleOutcome := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  scheduleLoop emu quantum (2 * fuel + 2 * (← emu.threadsRef.get).length + 8) fuel

private def workerMemory (emu : Emu) (context : ThreadContext) (fallback : Jit.Memory) : IO Jit.Memory := do
  let memories ← emu.processMemory.get
  pure (memories.getD (← spaceOf emu context.id) fallback)

private def resumeParallelWorker (emu : Emu) (context : ThreadContext) (shared : Jit.Memory) : IO Emu := do
  let existing ← emu.parallelWorkers.get
  let engine ← match existing.find? fun worker => worker.1 = context.id with
    | some (_, engine) => pure engine
    | none =>
      createEngine emu.config true
  engine.persistentMemory.set (some (← workerMemory emu context shared))
  engine.persistentVariable.set (some emu.config.memory)
  pure {
    emu with
    engine
    state := ← IO.mkRef context.state
    pc := ← IO.mkRef context.pc
    stopped := ← IO.mkRef context.stopped
    currentThreadRef := ← IO.mkRef context.id
    trace := ← IO.mkRef none
    lastFault := ← IO.mkRef none
    skipCode := ← IO.mkRef context.skip
    pendingRef := ← IO.mkRef context.pending
    journal := some (← IO.mkRef [])
    lastBudget := ← IO.mkRef 0
    rangeQuiet := ← IO.mkRef false
    budget := ← IO.mkRef 0
    restarting := ← IO.mkRef false
    rangeStart := ← IO.mkRef none
  }

/-- `memory` with the bytes of `native` at the written ranges. -/
private def applyJournal {width : Nat} (memory : Bap.Memory width) (native : Jit.Memory)
    (journal : List (Nat × Nat)) : IO (Bap.Memory width) :=
  applyJournalM (fun address => Jit.readMemory native (UInt64.ofNat address)) memory journal

/-- Workers write to native memories and not to their states, so that the memory of the states follows
after the round. Afterwards it is exact again, which a rollback, and anything else that reads the state's
memory, relies on. -/
private def synchronizeRound (emu : Emu) (merged : List ThreadContext)
    (workers : List (ThreadContext × Emu)) (shared : Jit.Memory) : IO (List ThreadContext) := do
  let processes ← emu.processMemory.get
  let table ← emu.taskTable.get
  let memoryVar := emu.config.memory
  let writesIn (inSpace : ThreadId → Bool) : IO (List (Nat × Nat)) :=
    workers.foldlM (init := []) fun writes worker =>
      match worker.2.journal with
      | some journal => if inSpace worker.1.id then do pure ((← journal.get) ++ writes) else pure writes
      | none => pure writes
  -- One memory value for all threads of the first address space.
  let sharedValue ← (merged.find? fun context => !processes.contains (table.spaceOf context.id)).mapM fun context => do
    let ⟨width, memory⟩ ← cells emu context.state
    let writes ← writesIn fun id => !processes.contains (table.spaceOf id)
    let memory ← applyJournal memory shared writes
    pure (Value.memory (addressWidth := width) memory)
  merged.mapM fun context => do
    let space := table.spaceOf context.id
    match processes.get? space with
    | some native =>
      let ⟨_, memory⟩ ← cells emu context.state
      let memory ← applyJournal memory native (← writesIn fun id => table.spaceOf id == space)
      pure { context with state := { env := Bil.bind context.state.env memoryVar (.memory memory) } }
    | none =>
      match sharedValue with
      | some value => pure { context with state := { env := Bil.bind context.state.env memoryVar value } }
      | none => pure context

def runPreemptiveParallel (emu : Emu) (quantum : Nat := 100) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  if (← emu.parallelLock.get).isNone then
    emu.parallelLock.set (some (← Std.BaseMutex.new))
  let contexts ← captureThreads emu
  let active := activeThreads contexts
  if active.length ≤ 1 then
    -- A stopped thread does not hold up the others of a parallel round.
    match active with
    | [only] => if only.id != (← thread emu) then switchThread emu only.id
    | _ => pure ()
    runPreemptive emu quantum quantum
  else
    emu.threadControl.set {}
    roundM (ε := IO.Error) (snapshot emu) (restore emu)
      (do
        let current ← emu.currentThreadRef.get
        let processes ← emu.processMemory.get
        let attached ← emu.engine.persistentMemory.get
        let parked ← emu.sharedMemory.get
        let table ← emu.taskTable.get
        let shared ← match (if processes.contains (table.spaceOf current) then parked else attached) with
          | some memory => pure memory
          | none =>
            match contexts.find? fun context => !processes.contains (table.spaceOf context.id) with
            | some context => nativeFromState emu context.state
            | none => nativeFromState emu (← emu.state.get)
        let workers ← active.mapM fun context => do
          let worker ← resumeParallelWorker emu context shared
          pure (context, worker)
        pure (current, shared, workers))
      (fun (_, _, workers) => do
        -- Workers need threads of their own: once the task manager shuts down, nothing runs queued
        -- tasks, and waiting for one would block the process exit forever.
        let tasks ← workers.tail.mapM fun worker => IO.asTask (prio := .dedicated) (run worker.2 quantum)
        -- The first worker runs here, which saves a thread each round.
        let first ← (workers.head?.elim (pure 0) fun worker => run worker.2 quantum).toBaseIO
        -- Every worker finishes before the round is judged, so none outlives a rollback.
        let results ← tasks.mapM fun task => IO.wait task
        pure (first :: results))
      (fun (_, _, workers) => do
        -- The fault of the first failing worker, whose state the rollback discards.
        let faults ← workers.filterMapM fun worker => worker.2.lastFault.get
        if let some fault := faults.head? then emu.lastFault.set (some fault))
      (fun (current, shared, workers) => do
        let statistics ← workers.mapM fun worker => Primus.Lifted.stats worker.2.engine
        let previous ← emu.engine.statistics.get
        emu.engine.statistics.set (statistics.foldl (init := previous) fun total current => {
          cacheHits := total.cacheHits + current.cacheHits
          lifts := total.lifts + current.lifts
          nativeCompilations := total.nativeCompilations + current.nativeCompilations
          nativeRuns := total.nativeRuns + current.nativeRuns
          interpretedRuns := total.interpretedRuns + current.interpretedRuns
          compileMs := total.compileMs + current.compileMs
          versionSaves := total.versionSaves + current.versionSaves
          versionHits := total.versionHits + current.versionHits
          invalidations := total.invalidations + current.invalidations
          evictions := total.evictions + current.evictions
          graphBlocks := total.graphBlocks + current.graphBlocks
        })
        let control ← emu.threadControl.get
        let workerResults ← workers.mapM fun worker => do
          pure ({
            id := worker.1.id
            state := ← worker.2.state.get
            pc := ← worker.2.pc.get
            stopped := ← worker.2.stopped.get
            pending := ← worker.2.pendingRef.get
            skip := ← worker.2.skipCode.get
          } : WorkerResult)
        let merged := mergeRound contexts (← emu.threadsRef.get) workerResults control
        let merged ← synchronizeRound emu merged workers shared
        emu.threadsRef.set merged
        match merged.find? fun context => context.id = current with
        | some context =>
          emu.state.set context.state
          emu.pc.set context.pc
          emu.stopped.set context.stopped
          emu.pendingRef.set context.pending
          emu.skipCode.set context.skip
        | none => pure ()
        match (← emu.processMemory.get).get? (← spaceOf emu current) with
        | some native =>
          emu.sharedMemory.set (some shared)
          attachMemory emu native
        | none => attachMemory emu shared
        emu.parallelWorkers.set (workers.map fun worker => (worker.1.id, worker.2.engine))
        let _ ← switchNextThread emu
        pure ())

def runUntil (emu : Emu) (address : Nat) (fuel : Nat := 100000) : IO Nat := do
  let rec loop (remaining : Nat) (total : Nat) : IO Nat :=
    match remaining with
    | 0 => throw <| IO.userError "Emu run-until fuel exhausted"
    | remaining + 1 => do
      if (← pc emu) == address then
        pure total
      else if ← step emu then
        loop remaining (total + 1)
      else pure total
  loop fuel 0

private def restoreRegisters (emu : Emu) (saved : Snapshot) : IO Unit := do
  let current ← emu.state.get
  let memory := current.env.filter fun binding => binding.1 == emu.config.memory
  emu.state.set { env := memory ++ saved.state.env }
  emu.pc.set saved.pc
  emu.stopped.set saved.stopped
  emu.pendingRef.set saved.pending

/-- The stack pointer after an x86-64 push, which wraps like the hardware. -/
def stackAfterPush (sp : Nat) : Nat := (sp + 2 ^ 64 - 8) % 2 ^ 64

private def callAbi : SyscallAbi → List String × String × String × Bool
  | .riscv => (["X10", "X11", "X12", "X13", "X14", "X15", "X16", "X17"], "X1", "X10", false)
  | .aarch64 => (["X0", "X1", "X2", "X3", "X4", "X5", "X6", "X7"], "X30", "X0", false)
  | .mips => (["R4", "R5", "R6", "R7", "R8", "R9", "R10", "R11"], "R31", "R2", false)
  | .x86_64 => (["RDI", "RSI", "RDX", "RCX", "R8", "R9"], "", "RAX", true)

def call (emu : Emu) (address returnTo : Nat) (args : List UInt64) (fuel : Nat := 100000) :
    IO Bap.Value := do
  let (arguments, link, result, stackReturn) := callAbi emu.config.syscallAbi
  if args.length > arguments.length then
    throw <| IO.userError "Emu.call has too many integer arguments for the target ABI"
  let saved ← snapshot emu
  let skipped ← emu.skipCode.get
  try
    (List.range args.length).forM fun index => do
      let var : Bap.Var := ⟨arguments[index]!, .imm 64, 0, false⟩
      setReg emu var (.bits (BitVec.ofNat 64 args[index]!.toNat))
    if stackReturn then
      let sp := stackAfterPush (← readWord emu "RSP")
      write emu sp (ByteArray.mk ((List.range 8).map fun index =>
        UInt8.ofNat (returnTo / 256 ^ index % 256)).toArray)
      setReg emu ⟨"RSP", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 sp))
    else
      setReg emu ⟨link, .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 returnTo))
    setPc emu address
    let _ ← runUntil emu returnTo fuel
    let reached ← pc emu
    if reached != returnTo then
      throw <| IO.userError s!"Emu.call stopped before returning at {reached}"
    let result ← reg emu ⟨result, .imm 64, 0, false⟩
    restoreRegisters emu saved
    emu.skipCode.set skipped
    pure result
  catch error =>
    restoreRegisters emu saved
    emu.skipCode.set skipped
    throw error

def stub (emu : Emu) (address returnTo : Nat) (args : List UInt64) (fuel : Nat := 100000) :
    IO Bap.Value :=
  call emu address returnTo args fuel

/-- Decoding with the semantics loaded once. `lift` decodes at each address, which is the base of the bytes it
fetched, and loading the semantics takes far longer than all that follows it. -/
private def decodeAt (decode : Nat → Nat → ByteArray → IO Disasm.Insn) (base address : Nat) (data : ByteArray) :
    IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← decode base address data))
  catch error =>
    pure (.error (toString error))

/-- The decoders at each base for RISC-V 64, which all share their semantics. -/
def riscv64Decoders : IO (Nat → IO Disasm.Disassembler) := do
  let environment ← Target.LLVMLift.riscvEnvironment
  pure fun base => pure
    { name := "riscv64-llvm-primus", decode := decodeAt (Target.LLVMLift.decodeRISCVWith environment) base }

def riscv64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let decoders ← riscv64Decoders
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create (adjust config) [region] {} entry

def riscv32 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let environment ← Target.LLVMLift.riscv32Environment
  let decoders (base : Nat) : IO Disasm.Disassembler := pure
    { name := "riscv32-llvm-primus", decode := decodeAt (Target.LLVMLift.decodeRISCV32With environment) base }
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create (adjust config) [region] {} entry

def x86_64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.X86.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.X86.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .x86_64
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create (adjust config) [region] {} entry

def aarch64 (code : ByteArray) (base entry : Nat) (adjust : Config → Config := id) : IO Emu := do
  let disassembler ← Target.AArch64.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.AArch64.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .aarch64
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create (adjust config) [region] {} entry

private def mipsOf (variant : Target.LLVMLift.MipsVariant) (code : ByteArray) (base entry : Nat) (adjust : Config → Config) : IO Emu := do
  let environment ← Target.LLVMLift.mipsEnvironmentOf variant
  let decoders (base : Nat) : IO Disasm.Disassembler := pure {
    name := if variant.bits == 64 then "mips64-llvm-primus" else "mips-llvm-primus"
    decode := decodeAt (Target.LLVMLift.decodeMIPSOf variant environment) base
    hasDelaySlot := Target.LLVMLift.mipsHasDelaySlot
    annulsSlot := Target.LLVMLift.mipsAnnulsSlot }
  let disassembler ← decoders base
  let config : Config := {
    disassembler
    disassemblerAt := some decoders
    memory := ⟨"mem", .mem variant.bits 8, 0, false⟩
    endian := variant.endian
    syscallAbi := .mips
    delayPolicy := .mips variant.release6
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create (adjust config) [region] {} entry

def mips64 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) (endian : Endian := .big) (adjust : Config → Config := id) : IO Emu :=
  mipsOf { bits := 64, endian, release6 } code base entry adjust

def mips32 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) (endian : Endian := .big) (adjust : Config → Config := id) : IO Emu :=
  mipsOf { bits := 32, endian, release6 } code base entry adjust

end Bap.Emu
