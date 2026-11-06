import Bap.Emu
import Bap.Bil.Wire
import Bap.Linux.Wire

namespace Bap.Emu

private structure Writer where
  data : ByteArray := ByteArray.empty

private def putBytes (writer : Writer) (bytes : ByteArray) : Writer :=
  { data := writer.data ++ bytes }

private def putByte (writer : Writer) (value : Nat) : Writer :=
  putBytes writer (ByteArray.mk #[UInt8.ofNat value])

private def natBytes (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => UInt8.ofNat (value / 256 ^ index % 256)).toArray

private def putNat (writer : Writer) (value : Nat) : Writer :=
  putBytes writer (natBytes value)

private def putBool (writer : Writer) (value : Bool) : Writer :=
  putByte writer (if value then 1 else 0)

private def putText (writer : Writer) (text : String) : Writer :=
  putBytes (putNat writer text.utf8ByteSize) text.toUTF8

private def putPendingBin (writer : Writer) (pending : Option PendingBranch) : Writer :=
  match pending with
  | none => putByte writer 0
  | some pending => putNat (putNat (putByte writer 1) pending.branch) pending.target

private def putSkipBin (writer : Writer) (skip : Option Nat) : Writer :=
  match skip with
  | none => putByte writer 0
  | some address => putNat (putByte writer 1) address

private def putTypBin (writer : Writer) (typ : Typ) : Writer :=
  match typ with
  | .unknown => putByte writer 0
  | .unit => putByte writer 1
  | .mem addressWidth valueWidth => putNat (putNat (putByte writer 2) addressWidth) valueWidth
  | .imm width => putNat (putByte writer 3) width

private def putCellsBin (writer : Writer) (cells : List (BitVec width × UInt8)) : Writer :=
  cells.foldl (init := putNat writer cells.length) fun writer cell =>
    putByte (putNat writer cell.1.toNat) cell.2.toNat

/-- The bytes that a value of `width` bits takes. -/
def valueBytes (width : Nat) : Nat := (width + 7) / 8

private def putValueBin (writer : Writer) (value : Value) : Writer :=
  match value with
  | .undefined => putByte writer 0
  | @Value.bits width value =>
    let valueBytes := (List.range (valueBytes width)).foldl (init := ByteArray.empty) fun bytes index =>
      bytes.push (UInt8.ofNat (value.toNat / 256 ^ index % 256))
    putBytes (putNat (putByte writer 1) width) valueBytes
  | @Value.memory addressWidth memory =>
    putCellsBin (putNat (putByte writer 2) addressWidth) (Memory.cells memory)

private def putBindingBin (writer : Writer) (binding : Bap.Var × Value) : Writer :=
  let (var, value) := binding
  putValueBin (putBool (putNat (putTypBin (putText writer var.name) var.typ) var.index) var.isVirtual) value

private def putPieceBin (writer : Writer) (piece : Nat × ByteArray) : Writer :=
  putBytes (putNat (putNat writer piece.1) piece.2.size) piece.2

/-- A region as its size and what of it isn't zeros, which is all that a region that a program mapped and hardly used has. -/
private def putRegionBin (writer : Writer) (region : Region) : Writer :=
  let writer := putNat writer region.address
  let writer := putBool writer region.protection.readable
  let writer := putBool writer region.protection.writable
  let writer := putBool writer region.protection.executable
  let pieces := Jit.pieces region.data
  pieces.foldl putPieceBin (putNat (putNat writer region.data.size) pieces.length)

private def putThreadBin (writer : Writer) (context : ThreadContext) : Writer :=
  let writer := putNat writer context.id
  let writer := putNat writer context.pc
  let writer := putBool writer context.stopped
  let writer := putNat writer context.state.env.length
  let writer := context.state.env.foldl putBindingBin writer
  putSkipBin (putPendingBin writer context.pending) context.skip

private def putProcessBin (writer : Writer) (process : ThreadId × List Region) : Writer :=
  let writer := putNat writer process.1
  let writer := putNat writer process.2.length
  process.2.foldl putRegionBin writer

private def putTask (writer : Writer) (task : Tasks.Entry) : Writer :=
  let writer := putNat writer task.tid
  let writer := putNat writer task.group
  let writer := putNat writer task.parent
  let writer := putNat writer task.space
  putSkipBin (putSkipBin (putSkipBin writer task.status) task.clearTid) task.exitSignal

private def putFutex (writer : Writer) (waiter : Tasks.FutexWaiter) : Writer :=
  let writer := putNat writer waiter.thread
  let writer := putNat writer waiter.space
  let writer := putNat writer waiter.address
  let writer := putNat writer waiter.bitset
  putSkipBin (putBool writer waiter.timed) waiter.deadline

private def putWaiter (writer : Writer) (waiter : Tasks.Waiter) : Writer :=
  let writer := putNat writer waiter.thread
  let writer := putSkipBin writer waiter.target
  putSkipBin writer waiter.statusAddress

private structure Reader where
  data : ByteArray
  offset : Nat := 0

private def takeBytes (reader : Reader) (count : Nat) : Except String (ByteArray × Reader) := do
  if reader.offset + count > reader.data.size then
    .error "truncated binary checkpoint"
  else
    .ok (reader.data.extract reader.offset (reader.offset + count), { reader with offset := reader.offset + count })

private def getByte (reader : Reader) : Except String (Nat × Reader) := do
  let (bytes, reader) ← takeBytes reader 1
  .ok (bytes[0]!.toNat, reader)

private def getNat (reader : Reader) : Except String (Nat × Reader) := do
  let (bytes, reader) ← takeBytes reader 8
  let value := (List.range 8).foldl (init := 0) fun value index => value + bytes[index]!.toNat * 256 ^ index
  .ok (value, reader)

private def getBool (reader : Reader) : Except String (Bool × Reader) := do
  let (value, reader) ← getByte reader
  match value with
  | 0 => .ok (false, reader)
  | 1 => .ok (true, reader)
  | _ => .error "invalid binary checkpoint boolean"

private def getText (reader : Reader) : Except String (String × Reader) := do
  let (size, reader) ← getNat reader
  let (bytes, reader) ← takeBytes reader size
  .ok (String.fromUTF8! bytes, reader)

private def getList (reader : Reader) (decode : Reader → Except String (α × Reader)) :
    Except String (List α × Reader) := do
  let (count, reader) ← getNat reader
  let rec loop (remaining : Nat) (reader : Reader) (result : List α) := do
    match remaining with
    | 0 => .ok (result.reverse, reader)
    | remaining + 1 =>
      let (value, reader) ← decode reader
      loop remaining reader (value :: result)
  loop count reader []

private def getPendingBin (reader : Reader) : Except String (Option PendingBranch × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (none, reader)
  | 1 =>
    let (branch, reader) ← getNat reader
    let (target, reader) ← getNat reader
    .ok (some ⟨branch, target⟩, reader)
  | _ => .error "invalid binary checkpoint pending branch"

private def getSkipBin (reader : Reader) : Except String (Option Nat × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (none, reader)
  | 1 =>
    let (address, reader) ← getNat reader
    .ok (some address, reader)
  | _ => .error "invalid binary checkpoint skip marker"

private def getTypBin (reader : Reader) : Except String (Typ × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (.unknown, reader)
  | 1 => .ok (.unit, reader)
  | 2 =>
    let (addressWidth, reader) ← getNat reader
    let (valueWidth, reader) ← getNat reader
    .ok (.mem addressWidth valueWidth, reader)
  | 3 =>
    let (width, reader) ← getNat reader
    .ok (.imm width, reader)
  | _ => .error "invalid binary checkpoint type"

private def getValueBin (reader : Reader) : Except String (Value × Reader) := do
  let (tag, reader) ← getByte reader
  match tag with
  | 0 => .ok (.undefined, reader)
  | 1 =>
    let (width, reader) ← getNat reader
    let (bytes, reader) ← takeBytes reader (valueBytes width)
    let value := (List.range (valueBytes width)).foldl (init := 0) fun value index =>
      value + bytes[index]!.toNat * 256 ^ index
    .ok (.bits (BitVec.ofNat width value), reader)
  | 2 =>
    let (width, reader) ← getNat reader
    let (cells, reader) ← getList reader fun reader => do
      let (address, reader) ← getNat reader
      let (value, reader) ← getByte reader
      .ok ((BitVec.ofNat width address, UInt8.ofNat value), reader)
    .ok (.memory (Memory.ofCells cells), reader)
  | _ => .error "invalid binary checkpoint value"

private def getBindingBin (reader : Reader) : Except String ((Bap.Var × Value) × Reader) := do
  let (name, reader) ← getText reader
  let (typ, reader) ← getTypBin reader
  let (index, reader) ← getNat reader
  let (isVirtual, reader) ← getBool reader
  let (value, reader) ← getValueBin reader
  .ok ((⟨name, typ, index, isVirtual⟩, value), reader)

private def getPieceBin (reader : Reader) : Except String ((Nat × ByteArray) × Reader) := do
  let (start, reader) ← getNat reader
  let (size, reader) ← getNat reader
  let (bytes, reader) ← takeBytes reader size
  .ok ((start, bytes), reader)

private def getRegionBin (reader : Reader) : Except String (Region × Reader) := do
  let (address, reader) ← getNat reader
  let (readable, reader) ← getBool reader
  let (writable, reader) ← getBool reader
  let (executable, reader) ← getBool reader
  let (size, reader) ← getNat reader
  if size ≥ Jit.fillLimit then .error "a region of the binary checkpoint is too big" else
  let (pieces, reader) ← getList reader getPieceBin
  .ok (⟨address, Jit.fill size pieces, ⟨readable, writable, executable⟩⟩, reader)

/-- A region as `BAPCKPT5` has it, with all its bytes. -/
private def getRegionV5 (reader : Reader) : Except String (Region × Reader) := do
  let (address, reader) ← getNat reader
  let (readable, reader) ← getBool reader
  let (writable, reader) ← getBool reader
  let (executable, reader) ← getBool reader
  let (size, reader) ← getNat reader
  let (data, reader) ← takeBytes reader size
  .ok (⟨address, data, ⟨readable, writable, executable⟩⟩, reader)

private def getThreadBin (reader : Reader) : Except String (ThreadContext × Reader) := do
  let (id, reader) ← getNat reader
  let (pc, reader) ← getNat reader
  let (stopped, reader) ← getBool reader
  let (env, reader) ← getList reader getBindingBin
  let (pending, reader) ← getPendingBin reader
  let (skip, reader) ← getSkipBin reader
  .ok (⟨id, { env := env }, pc, stopped, pending, skip⟩, reader)

private def getProcessBin (getRegion : Reader → Except String (Region × Reader)) (reader : Reader) :
    Except String ((ThreadId × List Region) × Reader) := do
  let (id, reader) ← getNat reader
  let (regions, reader) ← getList reader getRegion
  .ok ((id, regions), reader)

/-- A task, with its exit signal if `signal` says the format has it: a task of a format before it sends SIGCHLD. -/
private def getTask (signal : Bool) (reader : Reader) : Except String (Tasks.Entry × Reader) := do
  let (tid, reader) ← getNat reader
  let (group, reader) ← getNat reader
  let (parent, reader) ← getNat reader
  let (space, reader) ← getNat reader
  let (status, reader) ← getSkipBin reader
  let (clearTid, reader) ← getSkipBin reader
  let (exitSignal, reader) ← if signal then getSkipBin reader else .ok (none, reader)
  .ok (⟨tid, group, parent, space, status, clearTid, exitSignal⟩, reader)

private def getFutex (reader : Reader) : Except String (Tasks.FutexWaiter × Reader) := do
  let (thread, reader) ← getNat reader
  let (space, reader) ← getNat reader
  let (address, reader) ← getNat reader
  let (bitset, reader) ← getNat reader
  let (timed, reader) ← getBool reader
  let (deadline, reader) ← getSkipBin reader
  .ok (⟨thread, space, address, bitset, timed, deadline⟩, reader)

private def getWaiter (reader : Reader) : Except String (Tasks.Waiter × Reader) := do
  let (thread, reader) ← getNat reader
  let (target, reader) ← getSkipBin reader
  let (statusAddress, reader) ← getSkipBin reader
  .ok (⟨thread, target, statusAddress⟩, reader)

private def binaryMagic : ByteArray := "BAPCKPT7".toUTF8

/-- What checkpoints were before tasks had their exit signal, which are still read. -/
private def binaryMagicV6 : ByteArray := "BAPCKPT6".toUTF8

/-- What checkpoints were before regions had only what isn't zeros, which are still read. -/
private def binaryMagicV5 : ByteArray := "BAPCKPT5".toUTF8

private def encodeBinaryUnchecked (snapshot : Snapshot) : ByteArray :=
  let writer := putBytes ⟨binaryMagic⟩ (natBytes snapshot.pc)
  let writer := putBool writer snapshot.stopped
  let writer := putNat writer snapshot.regions.length
  let writer := snapshot.regions.foldl putRegionBin writer
  let writer := putNat writer snapshot.state.env.length
  let writer := snapshot.state.env.foldl putBindingBin writer
  let writer := putNat writer snapshot.threads.length
  let writer := snapshot.threads.foldl putThreadBin writer
  let writer := putNat writer snapshot.currentThread
  let writer := putNat writer snapshot.nextThread
  let writer := putPendingBin writer snapshot.pending
  let writer := putNat writer snapshot.processMemory.length
  let writer := putSkipBin (snapshot.processMemory.foldl putProcessBin writer) snapshot.skip
  let writer := putNat writer snapshot.table.tasks.length
  let writer := snapshot.table.tasks.foldl putTask writer
  let writer := putNat writer snapshot.table.waiters.length
  let writer := snapshot.table.waiters.foldl putWaiter writer
  let writer := putNat writer snapshot.table.futexes.length
  (snapshot.table.futexes.foldl putFutex writer).data

private def fitsWord (value : Nat) : Bool := value < 2 ^ 64

private def pendingFits : Option PendingBranch → Bool
  | none => true
  | some pending => fitsWord pending.branch && fitsWord pending.target

private def skipFits : Option Nat → Bool
  | none => true
  | some address => fitsWord address

private def typFits : Typ → Bool
  | .mem addressWidth valueWidth => fitsWord addressWidth && fitsWord valueWidth
  | .imm width => fitsWord width
  | _ => true

private def valueFits : Value → Bool
  | .undefined => true
  | @Value.bits width _ => fitsWord width
  | @Value.memory addressWidth memory => addressWidth ≤ 64 && fitsWord (Memory.cells memory).length

private def bindingFits (binding : Bap.Var × Value) : Bool :=
  fitsWord binding.1.name.utf8ByteSize && typFits binding.1.typ && fitsWord binding.1.index && valueFits binding.2

private def regionFits (region : Region) : Bool :=
  fitsWord region.address && decide (region.data.size < Jit.fillLimit)

private def threadFits (context : ThreadContext) : Bool :=
  fitsWord context.id && fitsWord context.pc && fitsWord context.state.env.length &&
    context.state.env.all bindingFits && pendingFits context.pending && skipFits context.skip

private def processFits (process : ThreadId × List Region) : Bool :=
  fitsWord process.1 && fitsWord process.2.length && process.2.all regionFits

private def taskFits (task : Tasks.Entry) : Bool :=
  fitsWord task.tid && fitsWord task.group && fitsWord task.parent && fitsWord task.space && skipFits task.status &&
    skipFits task.clearTid && skipFits task.exitSignal

private def futexFits (waiter : Tasks.FutexWaiter) : Bool :=
  fitsWord waiter.thread && fitsWord waiter.space && fitsWord waiter.address && fitsWord waiter.bitset && skipFits waiter.deadline

private def waiterFits (waiter : Tasks.Waiter) : Bool :=
  fitsWord waiter.thread && skipFits waiter.target && skipFits waiter.statusAddress

/-- Whether the fixed-width fields of the binary format can hold every part of the snapshot. -/
def binaryFits (snapshot : Snapshot) : Bool :=
  fitsWord snapshot.pc &&
    fitsWord snapshot.regions.length && snapshot.regions.all regionFits &&
    fitsWord snapshot.state.env.length && snapshot.state.env.all bindingFits &&
    fitsWord snapshot.threads.length && snapshot.threads.all threadFits &&
    fitsWord snapshot.currentThread && fitsWord snapshot.nextThread && pendingFits snapshot.pending &&
    fitsWord snapshot.processMemory.length && snapshot.processMemory.all processFits && skipFits snapshot.skip &&
    fitsWord snapshot.table.tasks.length && snapshot.table.tasks.all taskFits &&
    fitsWord snapshot.table.waiters.length && snapshot.table.waiters.all waiterFits &&
    fitsWord snapshot.table.futexes.length && snapshot.table.futexes.all futexFits

/-- Encode a snapshot, refusing one that the binary format could only store truncated. -/
def encodeBinarySnapshot (snapshot : Snapshot) : Except String ByteArray :=
  if binaryFits snapshot then .ok (encodeBinaryUnchecked snapshot)
  else .error "snapshot has a value too wide for the binary checkpoint format"

/-- The snapshot that `encodeBinarySnapshot` made, of either format that it has made, with its memory variable left out as it was. -/
def decodeBinarySnapshot (data : ByteArray) : Except String Snapshot := do
  let (getRegion, signal) ← if data.extract 0 binaryMagic.size == binaryMagic then pure (getRegionBin, true)
    else if data.extract 0 binaryMagicV6.size == binaryMagicV6 then pure (getRegionBin, false)
    else if data.extract 0 binaryMagicV5.size == binaryMagicV5 then pure (getRegionV5, false)
    else .error "not a binary checkpoint"
  do
    let reader : Reader := { data, offset := binaryMagic.size }
    let (pc, reader) ← getNat reader
    let (stopped, reader) ← getBool reader
    let (regions, reader) ← getList reader getRegion
    let (env, reader) ← getList reader getBindingBin
    let (threads, reader) ← getList reader getThreadBin
    let (currentThread, reader) ← getNat reader
    let (nextThread, reader) ← getNat reader
    let (pending, reader) ← getPendingBin reader
    let (processMemory, reader) ← getList reader (getProcessBin getRegion)
    let (skip, reader) ← getSkipBin reader
    let (tasks, reader) ← getList reader (getTask signal)
    let (waiters, reader) ← getList reader getWaiter
    let (futexes, reader) ← getList reader getFutex
    if reader.offset != data.size then
      .error "trailing bytes in binary checkpoint"
    else
      .ok ⟨{ env := env }, pc, regions, stopped, threads, currentThread, nextThread, pending, processMemory, skip, ⟨tasks, waiters, futexes⟩⟩

/-- `memory` with what isn't zeros of `data` at `address`, which is `data` there where `memory` has zeros, and takes no more of the host
than what isn't zeros. -/
def writeSparse (memory : Bap.Memory width) (address : Nat) (data : ByteArray) : Bap.Memory width :=
  (Jit.pieces data).foldl (init := memory) fun memory piece => memory.writeRegion (address + piece.1) piece.2

/-- The memory holding the bytes of `regions`. -/
def regionsMemory (width : Nat) (regions : List Region) : Bap.Memory width :=
  regions.foldl (init := Bap.Memory.empty width) fun memory region => writeSparse memory region.address region.data

/-- The bytes of the address space of thread `id`: its own, or else the shared ones. -/
def spaceRegions (snapshot : Snapshot) (id : ThreadId) : List Region :=
  (snapshot.processMemory.lookup (snapshot.table.spaceOf id)).getD snapshot.regions

/-- Gives a loaded snapshot the memory that `save` left out: every thread gets that of its address space,
and a forked process does not get the memory of its parent. -/
def materializeState (memoryVar : Bap.Var) (width : Nat) (snapshot : Snapshot) : Snapshot :=
  let memoryOf (id : ThreadId) : Value := .memory (regionsMemory width (spaceRegions snapshot id))
  { snapshot with
    state := { env := (memoryVar, memoryOf snapshot.currentThread) :: snapshot.state.env }
    threads := snapshot.threads.map fun thread =>
      { thread with state := { env := Bil.bind thread.state.env memoryVar (memoryOf thread.id) } }
  }

/-- The memory of each address space, made once when a thread of it first asks, for all its threads: a process of many threads has one
memory of its own, and not one for each. -/
private def spaceMemories (width : Nat) (snapshot : Snapshot) : List (Nat × Thunk Value) × Thunk Value :=
  (snapshot.processMemory.map fun (id, regions) => (id, Thunk.mk fun _ => .memory (regionsMemory width regions)),
   Thunk.mk fun _ => .memory (regionsMemory width snapshot.regions))

private theorem lookup_spaceMemories (width : Nat) (processes : List (Nat × List Region)) (space : Nat) :
    (processes.map fun (id, regions) => (id, Thunk.mk fun _ => Value.memory (regionsMemory width regions))).lookup space =
      (processes.lookup space).map fun regions => Thunk.mk fun _ => Value.memory (regionsMemory width regions) := by
  induction processes with
  | nil => rfl
  | cons head rest ih =>
    obtain ⟨id, regions⟩ := head
    by_cases h : space = id
    · simp [List.lookup, h]
    · have : (space == id) = false := by simpa using h
      simp [List.lookup, this, ih]

/-- `materializeState`, with the memory of each address space made once. -/
private def materializeStateShared (memoryVar : Bap.Var) (width : Nat) (snapshot : Snapshot) : Snapshot :=
  let (processes, shared) := spaceMemories width snapshot
  let memoryOf (id : ThreadId) : Value := ((processes.lookup (snapshot.table.spaceOf id)).getD shared).get
  { snapshot with
    state := { env := (memoryVar, memoryOf snapshot.currentThread) :: snapshot.state.env }
    threads := snapshot.threads.map fun thread =>
      { thread with state := { env := Bil.bind thread.state.env memoryVar (memoryOf thread.id) } }
  }

@[csimp] private theorem materializeState_csimp : @materializeState = @materializeStateShared := by
  funext memoryVar width snapshot
  have memory (id : ThreadId) : (((spaceMemories width snapshot).1.lookup (snapshot.table.spaceOf id)).getD (spaceMemories width snapshot).2).get =
      Value.memory (regionsMemory width (spaceRegions snapshot id)) := by
    simp only [spaceMemories, lookup_spaceMemories, spaceRegions]
    cases snapshot.processMemory.lookup (snapshot.table.spaceOf id) <;> rfl
  simp only [materializeState, materializeStateShared, memory]

/-- A decoded snapshot with the memory that `withoutMemory` left out, for an emulator to restore: see `materializeState`. -/
def materializeSnapshot (emu : Emu) (snapshot : Snapshot) : IO Snapshot := do
  if snapshot.state.env.any fun binding => binding.1 == emu.config.memory then
    pure snapshot
  else
    let width ← match emu.config.memory.typ with
      | .mem width 8 => pure width
      | _ => throw <| IO.userError "Emu memory must have byte-wide cells"
    pure (materializeState emu.config.memory width snapshot)

/-- What `save` writes: the memory variable stays out, as the regions and processes hold the bytes. -/
def withoutMemory (memoryVar : Bap.Var) (snapshot : Snapshot) : Snapshot :=
  { snapshot with
    state := { env := snapshot.state.env.filter fun binding => binding.1 != memoryVar }
    threads := snapshot.threads.map fun thread =>
      { thread with state := { env := thread.state.env.filter fun binding => binding.1 != memoryVar } }
  }

/-- What the emulator holds that a `Snapshot` doesn't and that a guest or who runs it can tell: how far the turn of the thread that
runs has gone, which fault stopped it, and where it stops of its own. Hooks are functions, and whoever put them there puts them back,
all but the breakpoints, which are only addresses. `threadControl` isn't here, as a parallel round forgets it when it starts, and what
is left is what an instruction holds while it runs, and a checkpoint isn't made during one. -/
structure RunState where
  turnUsed : Nat := 0
  fault : Option MemoryFault := none
  breakpoints : List Nat := []
  deriving DecidableEq, Repr

namespace RunState

private def operationTag : MemoryOperation → Nat
  | .fetch => 0
  | .read => 1
  | .write => 2

private def operationOf : Nat → Except String MemoryOperation
  | 0 => .ok .fetch
  | 1 => .ok .read
  | 2 => .ok .write
  | tag => .error s!"a checkpoint with a memory operation of kind {tag}"

private def putFault (out : ByteArray) (fault : MemoryFault) : ByteArray :=
  Bap.Linux.Wire.putNat (Bap.Linux.Wire.putNat (Bap.Linux.Wire.putNat (Bap.Linux.Wire.putNat out fault.pc) fault.address) (operationTag fault.operation)) fault.thread

private def getFault : Bap.Linux.Wire.Decoder MemoryFault := fun data at_ => do
  let (pc, at_) ← Bap.Linux.Wire.getNat data at_
  let (address, at_) ← Bap.Linux.Wire.getNat data at_
  let (tag, at_) ← Bap.Linux.Wire.getNat data at_
  let operation ← operationOf tag
  let (thread, at_) ← Bap.Linux.Wire.getNat data at_
  .ok (⟨pc, address, operation, thread⟩, at_)

/-- The bytes of a run state, after `out`. -/
def encode (out : ByteArray) (state : RunState) : ByteArray :=
  let out := Bap.Linux.Wire.putNat out state.turnUsed
  let out := Bap.Linux.Wire.putOption putFault out state.fault
  Bap.Linux.Wire.putList Bap.Linux.Wire.putNat out state.breakpoints

/-- A run state from its bytes, and where they end. -/
def decode : Bap.Linux.Wire.Decoder RunState := fun data at_ => do
  let (turnUsed, at_) ← Bap.Linux.Wire.getNat data at_
  let (fault, at_) ← Bap.Linux.Wire.getOption getFault data at_
  let (breakpoints, at_) ← Bap.Linux.Wire.getList Bap.Linux.Wire.getNat data at_
  .ok ({ turnUsed, fault, breakpoints }, at_)

end RunState

/-- What `RunState` says of the emulator now. -/
def runState (emu : Emu) : IO RunState := do
  pure { turnUsed := ← emu.turnUsed.get, fault := ← emu.lastFault.get, breakpoints := ← breakpoints emu }

/-- Puts it back, with the breakpoints that aren't there yet. -/
def setRunState (emu : Emu) (state : RunState) : IO Unit := do
  emu.turnUsed.set state.turnUsed
  emu.lastFault.set state.fault
  let existing ← breakpoints emu
  for address in state.breakpoints do
    unless existing.contains address do
      let _ ← addBreakpoint emu address

private def frameMagic : ByteArray := "BAPEMU01".toUTF8

/-- The bytes of what the emulator holds now: its run state, and a snapshot in the format that `binary_lossless_or_rejecting` is about. -/
def checkpointBytes (emu : Emu) : IO ByteArray := do
  if ← emu.serving.get then
    throw <| IO.userError "a checkpoint can't be made in the middle of an instruction, by a hook of a system call, an intrinsic or an access: stop the thread, and make it once the run returns"
  if emu.engine.deferMemorySync then
    throw <| IO.userError "a checkpoint can't be made by a worker of a parallel round, as the others are still running: stop the thread, and make it once the round is over"
  let originalRegions ← emu.regions.get
  refreshSharedRegions emu
  let snapshot ← snapshot emu
  let encoded := encodeBinarySnapshot (withoutMemory emu.config.memory snapshot)
  setRegions emu originalRegions
  pure (Bap.Linux.Wire.putBytes (RunState.encode frameMagic (← runState emu)) (← IO.ofExcept encoded))

/-- The two parts of `checkpointBytes`. -/
private def splitFrame (data : ByteArray) : Except String (RunState × ByteArray) := do
  if data.extract 0 frameMagic.size != frameMagic then
    .error "not a binary checkpoint"
  else
    let (state, at_) ← RunState.decode data frameMagic.size
    let (snapshot, at_) ← Bap.Linux.Wire.getBytes data at_
    Bap.Linux.Wire.expectEnd data at_
    .ok (state, snapshot)

/-- Writes the whole of a file or none of it, so that a run that dies while it saves leaves the checkpoint that was there. -/
def writeAtomically (path : System.FilePath) (data : ByteArray) : IO Unit := do
  let unfinished : System.FilePath := path.toString ++ ".partial"
  try
    IO.FS.writeBinFile unfinished data
    IO.FS.rename unfinished path
  catch error =>
    -- What is left of it is no use to anyone, and looks like something that a run might have been in the middle of.
    try IO.FS.removeFile unfinished catch _ => pure ()
    throw error

/-- Writes the checkpoint of an emulator to a file, all of it or none. -/
def save (emu : Emu) (path : String) : IO Unit := do
  writeAtomically path (← checkpointBytes emu)

/-- A snapshot from the bytes of `checkpointBytes`. -/
def snapshotOfBytes (emu : Emu) (data : ByteArray) : IO Snapshot := do
  let (_, snapshot) ← IO.ofExcept (splitFrame data)
  materializeSnapshot emu (← IO.ofExcept (decodeBinarySnapshot snapshot))

/-- The snapshot in the bytes of `checkpointBytes` as it was saved, without the memory that `materializeSnapshot` gives it, for
looking at what it has without an emulator. -/
def snapshotOfFrame (data : ByteArray) : Except String Snapshot := do
  let (_, snapshot) ← splitFrame data
  decodeBinarySnapshot snapshot

/-- The run state from the bytes of `checkpointBytes`. -/
def runStateOfBytes (data : ByteArray) : IO RunState := do
  pure (← IO.ofExcept (splitFrame data)).1

/-- The snapshot in a checkpoint file, for this emulator, without restoring it. -/
def loadSnapshot (emu : Emu) (path : String) : IO Snapshot := do
  snapshotOfBytes emu (← IO.FS.readBinFile path)

/-- Puts an emulator where a checkpoint file has it, with its run state and breakpoints. -/
def load (emu : Emu) (path : String) : IO Unit := do
  let data ← IO.FS.readBinFile path
  restore emu (← snapshotOfBytes emu data)
  setRunState emu (← runStateOfBytes data)

end Bap.Emu
