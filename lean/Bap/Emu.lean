import Bap.Target.RISCV
import Bap.Target.RISCV32
import Bap.Target.X86
import Bap.Target.AArch64
import Bap.Target.MIPS
import Bap.Target.MIPS32
import Bap.Primus.Lifted
import Bap.Primus.Memory

namespace Bap.Emu

structure Region where
  address : Nat
  data : ByteArray
  protection : Primus.Protection
  deriving DecidableEq

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
  hotThreshold : Nat := 1

abbrev HookId := Nat

inductive MemoryOperation where
  | read | write | fetch
  deriving DecidableEq, Repr

structure MemoryFault where
  pc : Nat
  address : Nat
  operation : MemoryOperation
  thread : Nat := 1
  deriving DecidableEq, Repr

structure CodeHook where
  id : HookId
  first : Nat
  last : Nat
  action : Nat → IO Unit

structure ReadHook where
  id : HookId
  first : Nat
  last : Nat
  action : Nat → Nat → IO Unit

structure WriteHook where
  id : HookId
  first : Nat
  last : Nat
  action : Nat → Nat → Nat → IO Unit

inductive SyscallAction where
  | default | returnValue (value : Nat)

structure SyscallHook where
  id : HookId
  action : Nat → List Nat → IO SyscallAction

inductive IntrinsicAction where
  | default | proceed

structure IntrinsicHook where
  id : HookId
  name : String
  action : Nat → IO IntrinsicAction

inductive DelayKind where
  | none | delayed | likely | forbidden
  deriving DecidableEq, Repr

structure PendingBranch where
  branch : Nat
  target : Nat
  deriving DecidableEq, Repr

abbrev ThreadId := Nat

structure ThreadContext where
  id : ThreadId
  state : Bil.State
  pc : Nat
  stopped : Bool
  pending : Option PendingBranch := none
  deriving Repr

structure ThreadInfo where
  id : ThreadId
  pc : Nat
  stopped : Bool
  deriving DecidableEq, Repr

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
  pcs : List Nat := []
  pcCount : Nat := 0
  accesses : List TraceAccess := []
  accessCount : Nat := 0
  droppedAccesses : Nat := 0
  accessCapacity : Nat := 0
  watch : Option (Nat × Nat) := none

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

namespace Region

def contains (region : Region) (address : Nat) : Bool :=
  region.address ≤ address && address < region.address + region.data.size

end Region

private def memoryWidth (config : Config) : Except String Nat :=
  match config.memory.typ with
  | .mem width 8 => .ok width
  | _ => .error "Emu memory must have byte-wide cells"

private def overlaps (left right : Region) : Bool :=
  left.address < right.address + right.data.size &&
    right.address < left.address + left.data.size

private def initializeMemory (config : Config) (regions : List Region) : Except String Bil.State := do
  let width ← memoryWidth config
  if regions.any fun left => regions.any fun right => left != right && overlaps left right then
    .error "Emu regions overlap"
  let cells := regions.foldl (init := Bap.Memory.empty width) fun cells region =>
    (List.range region.data.size).foldl (init := cells) fun cells offset =>
      Bap.Memory.writeByte cells (BitVec.ofNat width (region.address + offset)) region.data[offset]!
  .ok { env := [(config.memory, .memory cells)] }

def create (config : Config) (mapped : List Region) (initial : Bil.State) (entry : Nat) : IO Emu := do
  let initial ← match initializeMemory config mapped with
    | .ok memory => pure { env := memory.env ++ initial.env }
    | .error error => throw <| IO.userError error
  pure {
    config
    engine := ← Primus.Lifted.Engine.create config.hotThreshold
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
    threadsRef := ← IO.mkRef [⟨1, initial, entry, false, none⟩]
    currentThreadRef := ← IO.mkRef 1
    nextThreadRef := ← IO.mkRef 2
    pendingRef := ← IO.mkRef none
  }

private def saveCurrentThread (emu : Emu) : IO Unit := do
  let context : ThreadContext := {
    id := ← emu.currentThreadRef.get
    state := ← emu.state.get
    pc := ← emu.pc.get
    stopped := ← emu.stopped.get
    pending := ← emu.pendingRef.get
  }
  emu.threadsRef.modify fun threads => context :: threads.filter fun thread => thread.id != context.id

private def captureThreads (emu : Emu) : IO (List ThreadContext) := do
  saveCurrentThread emu
  let state ← emu.state.get
  let memory := match Bil.lookup state.env emu.config.memory with
    | .ok value => some value
    | .error _ => none
  let threads ← emu.threadsRef.get
  pure (threads.map fun thread =>
    match memory with
    | some memory => { thread with state := { env := Bil.bind thread.state.env emu.config.memory memory } }
    | none => thread)

structure Snapshot where
  state : Bil.State
  pc : Nat
  regions : List Region
  stopped : Bool
  threads : List ThreadContext
  currentThread : ThreadId
  nextThread : ThreadId
  pending : Option PendingBranch

def snapshot (emu : Emu) : IO Snapshot := do
  pure {
    state := ← emu.state.get
    pc := ← emu.pc.get
    regions := ← emu.regions.get
    stopped := ← emu.stopped.get
    threads := ← captureThreads emu
    currentThread := ← emu.currentThreadRef.get
    nextThread := ← emu.nextThreadRef.get
    pending := ← emu.pendingRef.get
  }

def restore (emu : Emu) (snapshot : Snapshot) : IO Unit := do
  emu.state.set snapshot.state
  emu.pc.set snapshot.pc
  emu.regions.set snapshot.regions
  emu.stopped.set snapshot.stopped
  emu.threadsRef.set snapshot.threads
  emu.currentThreadRef.set snapshot.currentThread
  emu.nextThreadRef.set snapshot.nextThread
  emu.pendingRef.set snapshot.pending
  emu.skipCode.set none

def thread (emu : Emu) : IO ThreadId := emu.currentThreadRef.get

def threads (emu : Emu) : IO (List ThreadInfo) := do
  let contexts ← captureThreads emu
  pure ((contexts.map fun context => ⟨context.id, context.pc, context.stopped⟩).mergeSort
    (fun left right => left.id ≤ right.id))

def switchThread (emu : Emu) (id : ThreadId) : IO Unit := do
  saveCurrentThread emu
  let contexts ← emu.threadsRef.get
  match contexts.find? fun context => context.id == id with
  | none => throw <| IO.userError s!"unknown Emu thread {id}"
  | some context =>
    let current ← emu.state.get
    let env := match Bil.lookup current.env emu.config.memory with
      | .ok memory => Bil.bind context.state.env emu.config.memory memory
      | .error _ => context.state.env
    emu.state.set { env }
    emu.pc.set context.pc
    emu.stopped.set context.stopped
    emu.currentThreadRef.set id
    emu.pendingRef.set context.pending
    emu.skipCode.set none

def resumeThread (emu : Emu) (id : ThreadId) : IO Unit := do
  if (← thread emu) == id then
    emu.stopped.set false
  else
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == id then { context with stopped := false } else context

def stopThread (emu : Emu) (id : ThreadId) : IO Unit := do
  if (← thread emu) == id then
    emu.stopped.set true
  else
    emu.threadsRef.modify fun threads => threads.map fun context =>
      if context.id == id then { context with stopped := true } else context

def onCode (emu : Emu) (range : Nat × Nat) (action : Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu code-hook range"
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  emu.hooks.modify fun hooks => ⟨id, range.1, range.2, action⟩ :: hooks
  pure id

def onRead (emu : Emu) (range : Nat × Nat) (action : Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu read-hook range"
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  emu.readHooks.modify fun hooks => ⟨id, range.1, range.2, action⟩ :: hooks
  pure id

def onWrite (emu : Emu) (range : Nat × Nat) (action : Nat → Nat → Nat → IO Unit) : IO HookId := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu write-hook range"
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  emu.writeHooks.modify fun hooks => ⟨id, range.1, range.2, action⟩ :: hooks
  pure id

def onSyscall (emu : Emu) (action : Nat → List Nat → IO SyscallAction) : IO HookId := do
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  emu.syscallHooks.modify fun hooks => ⟨id, action⟩ :: hooks
  pure id

def onIntrinsic (emu : Emu) (name : String) (action : Nat → IO IntrinsicAction) : IO HookId := do
  if name.isEmpty then
    throw <| IO.userError "intrinsic hook name is empty"
  let id ← emu.nextHook.get
  emu.nextHook.set (id + 1)
  emu.intrinsicHooks.modify fun hooks => ⟨id, name, action⟩ :: hooks
  pure id

def removeHook (emu : Emu) (id : HookId) : IO Unit := do
  emu.hooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.readHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.writeHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.syscallHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.intrinsicHooks.modify fun hooks => hooks.filter fun hook => hook.id != id
  emu.breakpointsRef.modify fun breakpoints => breakpoints.filter fun breakpoint => breakpoint.1 != id

def clearHooks (emu : Emu) : IO Unit := do
  emu.hooks.set []
  emu.readHooks.set []
  emu.writeHooks.set []
  emu.syscallHooks.set []
  emu.intrinsicHooks.set []
  emu.breakpointsRef.set []

def addBreakpoint (emu : Emu) (address : Nat) : IO HookId := do
  let id ← onCode emu (address, address) fun _ => emu.stopped.set true
  emu.breakpointsRef.modify fun breakpoints => (id, address) :: breakpoints
  pure id

def removeBreakpoint (emu : Emu) (address : Nat) : IO Unit := do
  let breakpoints ← emu.breakpointsRef.get
  (breakpoints.filter fun breakpoint => breakpoint.2 == address).forM fun breakpoint =>
    removeHook emu breakpoint.1

def breakpoints (emu : Emu) : IO (List Nat) := do
  let current ← emu.breakpointsRef.get
  pure (current.map Prod.snd).reverse

private def traceBegin (emu : Emu) (capacity : Nat) (watch : Option (Nat × Nat)) : IO Unit :=
  emu.trace.set (some { accessCapacity := capacity, watch })

def traceStart (emu : Emu) : IO Unit := traceBegin emu 0 none

def traceStartAccesses (emu : Emu) (capacity : Nat) : IO Unit := traceBegin emu capacity none

def traceStartWatch (emu : Emu) (range : Nat × Nat) (capacity : Nat) : IO Unit := do
  if range.1 > range.2 then
    throw <| IO.userError "invalid Emu trace watch range"
  traceBegin emu capacity (some range)

def traceStop (emu : Emu) : IO (List Nat) := do
  let current ← emu.trace.get
  emu.trace.set none
  pure (current.getD {}).pcs.reverse

def tracePcs (emu : Emu) : IO (List Nat) := do
  let current ← emu.trace.get
  pure (current.getD {}).pcs.reverse

def traceAccesses (emu : Emu) : IO (List TraceAccess) := do
  let current ← emu.trace.get
  pure (current.getD {}).accesses.reverse

def traceAccessesCount (emu : Emu) : IO Nat := do
  let current ← emu.trace.get
  pure (current.getD {}).accessCount

def traceDroppedAccesses (emu : Emu) : IO Nat := do
  let current ← emu.trace.get
  pure (current.getD {}).droppedAccesses

private def recordTrace (emu : Emu) (address : Nat) : IO Unit :=
  emu.trace.modify fun current => current.map fun state =>
    { state with pcs := address :: state.pcs, pcCount := state.pcCount + 1 }

private def recordAccess (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  let pc ← emu.pc.get
  let thread ← emu.currentThreadRef.get
  emu.trace.modify fun current => current.map fun state =>
    if state.accessCapacity = 0 then state
    else if state.watch.any fun range => address < range.1 || range.2 < address then state
    else
      let access : TraceAccess := {
        insn := state.pcCount
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
  let hooks ← emu.hooks.get
  (hooks.filter fun hook => hook.first ≤ address && address ≤ hook.last).forM fun hook =>
    hook.action address

def failure (emu : Emu) : IO (Option MemoryFault) := emu.lastFault.get

private def recordFault (emu : Emu) (operation : MemoryOperation) (address : Nat) : IO Unit := do
  let pc ← emu.pc.get
  emu.lastFault.set (some ⟨pc, address, operation, 1⟩)

private def notifyMemory (emu : Emu) (write : Bool) (address size value : Nat) : IO Unit := do
  let mapped ← emu.regions.get
  let invalid := (List.range size).find? fun offset =>
    let current := address + offset
    match mapped.find? fun region => region.contains current with
    | none => true
    | some region => if write then !region.protection.writable else !region.protection.readable
  match invalid with
  | some offset =>
    let operation := if write then MemoryOperation.write else MemoryOperation.read
    recordFault emu operation (address + offset)
    throw <| IO.userError s!"Emu {repr operation} fault at {address + offset}"
  | none =>
    recordAccess emu write address size value
    if write then
      let hooks ← emu.writeHooks.get
      (hooks.filter fun hook => hook.first ≤ address && address ≤ hook.last).forM fun hook =>
        hook.action address size value
    else
      let hooks ← emu.readHooks.get
      (hooks.filter fun hook => hook.first ≤ address && address ≤ hook.last).forM fun hook =>
        hook.action address size

private def memoryObserver (emu : Emu) : IO (Option Jit.MemoryObserver) :=
  pure (some (notifyMemory emu))

private def lookupRegion (regions : List Region) (address : Nat) : Option Region :=
  regions.find? fun region => region.contains address

private def cells (emu : Emu) (state : Bil.State) : IO (Σ width, Bap.Memory width) := do
  match Bil.lookup state.env emu.config.memory with
  | .ok (.memory memory) => pure ⟨_, memory⟩
  | .ok _ => throw <| IO.userError "Emu memory is not a memory value"
  | .error error => throw <| IO.userError error

private def readByte (emu : Emu) (address : Nat) : IO UInt8 := do
  let regions ← emu.regions.get
  match lookupRegion regions address with
  | none => throw <| IO.userError s!"unmapped Emu address {address}"
  | some region =>
    if !region.protection.readable then
      throw <| IO.userError s!"unreadable Emu address {address}"
    let state ← emu.state.get
    let ⟨width, memory⟩ ← cells emu state
    pure (Bap.Memory.readByte memory (BitVec.ofNat width address))

def read (emu : Emu) (address size : Nat) : IO ByteArray := do
  let bytes ← (List.range size).mapM fun offset => readByte emu (address + offset)
  pure (ByteArray.mk bytes.toArray)

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
    emu.regions.set (mapped.map fun current =>
      if current.contains address then
        { current with data := current.data.set! (address - current.address) value }
      else current)

def write (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  (List.range data.size).forM fun offset => writeByte emu (address + offset) data[offset]!

def map (emu : Emu) (region : Region) : IO Unit := do
  let mapped ← emu.regions.get
  if mapped.any fun current => overlaps current region then
    throw <| IO.userError s!"Emu region overlaps an existing mapping at {region.address}"
  let state ← emu.state.get
  let ⟨width, memory⟩ ← cells emu state
  let updated := (List.range region.data.size).foldl (init := memory) fun memory offset =>
    Bap.Memory.writeByte memory (BitVec.ofNat width (region.address + offset)) region.data[offset]!
  emu.state.set { env := Bil.bind state.env emu.config.memory (.memory updated) }
  emu.regions.set (region :: mapped)

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

def spawnThread (emu : Emu) (start : Nat) (arg : Nat) : IO ThreadId := do
  saveCurrentThread emu
  let id ← emu.nextThreadRef.get
  emu.nextThreadRef.set (id + 1)
  let width ← wordWidth emu
  let (_, arguments, _) := syscallRegisters emu.config.syscallAbi
  match arguments.head? with
  | none => throw <| IO.userError "target has no thread argument register"
  | some register =>
    let current ← emu.state.get
    let argument : Bap.Var := ⟨register, .imm width, 0, false⟩
    let state : Bil.State := { env := Bil.bind current.env argument (.bits (BitVec.ofNat width arg)) }
    emu.threadsRef.modify fun threads => ⟨id, state, start, false, none⟩ :: threads
    pure id

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

private def dispatchSyscall (emu : Emu) : IO (Option Nat) := do
  let hooks ← emu.syscallHooks.get
  if hooks.isEmpty then
    pure none
  else
    let width ← wordWidth emu
    let (numberRegister, argumentRegisters, resultRegister) := syscallRegisters emu.config.syscallAbi
    let number ← readWord emu numberRegister
    let args ← argumentRegisters.mapM (readWord emu)
    let rec serve : List SyscallHook → IO (Option Nat)
      | [] => pure none
      | hook :: rest => do
        match ← hook.action number args with
        | .returnValue value =>
          setReg emu ⟨resultRegister, .imm width, 0, false⟩ (.bits (BitVec.ofNat width value))
          pure (some value)
        | .default => serve rest
    serve hooks.reverse

private def dispatchIntrinsic (emu : Emu) (name : String) : IO Bool := do
  let address ← emu.pc.get
  let hooks ← emu.intrinsicHooks.get
  let selected := hooks.reverse.filter fun hook => hook.name == "*" || hook.name == name
  let rec serve : List IntrinsicHook → IO Bool
    | [] => pure false
    | hook :: rest => do
      match ← hook.action address with
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

private def fetch (emu : Emu) (address : Nat) : IO ByteArray := do
  try
    let mapped ← emu.regions.get
    match lookupRegion mapped address with
    | none => throw <| IO.userError s!"unmapped Emu instruction address {address}"
    | some region =>
      if !region.protection.executable then
        throw <| IO.userError s!"non-executable Emu instruction address {address}"
      let data ← read emu region.address region.data.size
      pure ((ByteArray.mk (List.replicate region.address 0).toArray) ++ data)
  catch error =>
    recordFault emu .fetch address
    throw error

private def lift (emu : Emu) (address : Nat) (code : ByteArray) : IO Primus.Lifted.Block := do
  let decoded ← emu.config.disassembler.decode address code
  match decoded with
  | .error error => throw <| IO.userError s!"Emu instruction at {address}: {error}"
  | .ok insn => pure ⟨insn.address, insn.next, insn.bil⟩

private def syncRegions (emu : Emu) (mapped : List Region) (state : Bil.State) : IO Unit := do
  let ⟨width, memory⟩ ← cells emu state
  emu.regions.set (mapped.map fun region =>
    let data := (List.range region.data.size).map fun offset =>
      Bap.Memory.readByte memory (BitVec.ofNat width (region.address + offset))
    { region with data := ByteArray.mk data.toArray })

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
    match mipsWord code address with
    | none => pure .none
    | some word =>
      if mipsLikely release6 word then pure .likely
      else if mipsDelayed release6 word then pure .delayed
      else if release6 && mipsCompact word then pure .forbidden
      else pure .none

private def advanceControl (emu : Emu) (address next : Nat) (result : Primus.Lifted.Result)
    (delay : DelayKind) (pending : Option PendingBranch) : IO Bool := do
  match result.effect with
  | .normal =>
    match pending with
    | some branch =>
      emu.pendingRef.set none
      emu.pc.set branch.target
    | none =>
      emu.pc.set (if delay == .likely then next + 4 else next)
    pure true
  | .jump target =>
    match pending with
    | some _ => emu.pendingRef.set none
    | none =>
      match delay with
      | .delayed | .likely => emu.pendingRef.set (some ⟨address, target.toNat⟩)
      | .none | .forbidden => pure ()
    match pending with
    | some _ => emu.pc.set target.toNat
    | none => emu.pc.set (if delay == .delayed || delay == .likely then next else target.toNat)
    pure true
  | .special name =>
    let handled ← if name == "syscall" || name == "svc" then
      match ← dispatchSyscall emu with
      | some _ => pure true
      | none => dispatchIntrinsic emu name
    else
      dispatchIntrinsic emu name
    if handled then
      match pending with
      | some branch =>
        emu.pendingRef.set none
        emu.pc.set branch.target
      | none => emu.pc.set next
      pure true
    else
      match pending with
      | some branch =>
        emu.pendingRef.set none
        emu.pc.set branch.target
      | none => emu.pc.set address
      stop emu
      pure false
  | .cpuExn _ =>
    match pending with
    | some branch =>
      emu.pendingRef.set none
      emu.pc.set branch.target
    | none => emu.pc.set address
    stop emu
    pure false

def step (emu : Emu) : IO Bool := do
  if ← stopped emu then
    pure false
  else
    let address ← pc emu
    let skipped ← emu.skipCode.get
    if skipped == some address then
      emu.skipCode.set none
    else
      notifyCode emu address
    if ← stopped emu then
      if skipped != some address then
        emu.skipCode.set (some address)
      pure false
    else
      let before ← snapshot emu
      let pendingBefore ← emu.pendingRef.get
      try
        let state ← emu.state.get
        let observer ← memoryObserver emu
        let delay ← match pendingBefore with
          | some _ => pure .none
          | none => delayFor emu address
        let result ← Primus.Lifted.runBlockObserved emu.engine (fetch emu) (lift emu) state address observer
        emu.state.set result.state
        syncRegions emu before.regions result.state
        emu.lastFault.set none
        recordTrace emu address
        advanceControl emu address result.next result delay pendingBefore
      catch error =>
        restore emu before
        match pendingBefore with
        | some branch =>
          match ← emu.lastFault.get with
          | some fault => emu.lastFault.set (some { fault with pc := branch.branch })
          | none => pure ()
          emu.pc.set branch.branch
          emu.pendingRef.set none
        | none => pure ()
        throw error

def run (emu : Emu) (maxSteps : Nat := 100000) : IO Nat := do
  let rec loop : Nat → IO Nat
    | 0 => pure 0
    | fuel + 1 => do
      if ← step emu then
        let steps ← loop fuel
        pure (steps + 1)
      else pure 0
  loop maxSteps

private def switchNextThread (emu : Emu) : IO Bool := do
  saveCurrentThread emu
  let current ← thread emu
  let contexts ← emu.threadsRef.get
  let ordered := contexts.mergeSort (fun left right => left.id ≤ right.id)
  let candidates := ordered.filter fun context => context.id != current && !context.stopped
  let next := match candidates.find? fun context => current < context.id with
    | some context => some context
    | none => candidates.head?
  match next with
  | some context =>
    switchThread emu context.id
    pure true
  | none => pure !(← stopped emu)

def runQuantum (emu : Emu) (quantum : Nat) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  let steps ← run emu quantum
  let _ ← switchNextThread emu
  pure steps

def runPreemptive (emu : Emu) (quantum : Nat := 100) (fuel : Nat := 100000) : IO Nat := do
  if quantum = 0 then
    throw <| IO.userError "Emu thread quantum must be positive"
  let rec loop (remaining : Nat) (total : Nat) (rounds : Nat) : IO Nat := do
    if remaining = 0 || rounds = 0 then
      pure total
    else
      let steps ← run emu (min quantum remaining)
      let total := total + steps
      if total = fuel then
        pure total
      else if ← switchNextThread emu then
        loop (remaining - steps) total (rounds - 1)
      else
        pure total
    termination_by rounds
    decreasing_by
      simp_all
      omega
  loop fuel 0 (fuel + 1)

def runUntil (emu : Emu) (address : Nat) (fuel : Nat := 100000) : IO Nat := do
  let rec loop : Nat → IO Nat
    | 0 => throw <| IO.userError "Emu run-until fuel exhausted"
    | fuel + 1 => do
      if (← pc emu) == address then
        pure 0
      else if ← step emu then
        let steps ← loop fuel
        pure (steps + 1)
      else pure 0
  loop fuel

private def restoreRegisters (emu : Emu) (saved : Snapshot) : IO Unit := do
  let current ← emu.state.get
  let memory := current.env.filter fun binding => binding.1 == emu.config.memory
  emu.state.set { env := memory ++ saved.state.env }
  emu.pc.set saved.pc
  emu.stopped.set saved.stopped

def call (emu : Emu) (address returnTo : Nat) (args : List UInt64) (fuel : Nat := 100000) :
    IO Bap.Value := do
  if args.length > 8 then
    throw <| IO.userError "Emu.call supports at most eight integer arguments"
  let saved ← snapshot emu
  try
    (List.range args.length).forM fun index => do
      let var : Bap.Var := ⟨s!"X{10 + index}", .imm 64, 0, false⟩
      setReg emu var (.bits (BitVec.ofNat 64 args[index]!.toNat))
    setReg emu ⟨"X1", .imm 64, 0, false⟩ (.bits (BitVec.ofNat 64 returnTo))
    setPc emu address
    let _ ← runUntil emu returnTo fuel
    let result ← reg emu ⟨"X10", .imm 64, 0, false⟩
    restoreRegisters emu saved
    pure result
  catch error =>
    restoreRegisters emu saved
    throw error

def stub (emu : Emu) (address returnTo : Nat) (args : List UInt64) (fuel : Nat := 100000) :
    IO Bap.Value :=
  call emu address returnTo args fuel

def riscv64 (code : ByteArray) (base entry : Nat) : IO Emu := do
  let disassembler ← Target.RISCV.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.RISCV.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

def riscv32 (code : ByteArray) (base entry : Nat) : IO Emu := do
  let disassembler ← Target.RISCV32.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.RISCV32.disassembler base)
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .little
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

def x86_64 (code : ByteArray) (base entry : Nat) : IO Emu := do
  let disassembler ← Target.X86.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.X86.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .x86_64
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

def aarch64 (code : ByteArray) (base entry : Nat) : IO Emu := do
  let disassembler ← Target.AArch64.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.AArch64.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .little
    syscallAbi := .aarch64
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

def mips64 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) : IO Emu := do
  let disassembler ← Target.MIPS.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.MIPS.disassembler base)
    memory := ⟨"mem", .mem 64 8, 0, false⟩
    endian := .big
    syscallAbi := .mips
    delayPolicy := .mips release6
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

def mips32 (code : ByteArray) (base entry : Nat) (release6 : Bool := false) : IO Emu := do
  let disassembler ← Target.MIPS32.disassembler base
  let config : Config := {
    disassembler
    disassemblerAt := some (fun base => Target.MIPS32.disassembler base)
    memory := ⟨"mem", .mem 32 8, 0, false⟩
    endian := .big
    syscallAbi := .mips
    delayPolicy := .mips release6
  }
  let region : Region := ⟨base, code, ⟨true, true, true⟩⟩
  create config [region] {} entry

end Bap.Emu
