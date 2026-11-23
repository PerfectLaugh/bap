import Bap.Analysis.DynamicTaint
import Bap.Emu.Tasks
import Bap.Emu.Checkpoint
import Bap.Linux.Calls
import Bap.Linux.Signals
import Bap.Linux.Ptrace
import Bap.Linux.Seccomp
import Bap.Linux.Timers
import Bap.Linux.Poll
import Bap.Linux.Identity
import Bap.Linux.Tty
import Bap.Linux.Files
import Bap.Linux.Notify
import Bap.Linux.SysV
import Bap.Linux.Mqueue
import Bap.Linux.Ring
import Bap.Linux.GuestHeap
import Bap.Linux.LoadedLibrary
import Bap.Linux.Image
import Bap.Linux.Sockets
import Bap.Linux.Proc
import Bap.Linux.Elf
import Bap.Float
import Bap.PowerPC
import Bap.Crypto.AES

/-! # A Linux machine

The virtual kernel of `Bap.Linux.Kernel` behind the system calls of the emulator, and what the kernel does to start a program:
its segments, and those of the interpreter that it asks for, in pages, and the stack that it starts on. No request ever
reaches the machine that this runs on: a program has what was put in its kernel. For x86, ARM, RISC-V, MIPS and PowerPC. What
is in here is in 64 bits whatever the guest has, with an error as its negative, as on x86-64, until `kernelCall` hands it over. -/

namespace Bap.Linux

open Bap.Emu
open Bap.Tasks (ScheduleOutcome)

private def word (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def bits (width value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)

/-- The clock of the machine at boot, which `CNTVCT_EL0` and the uptime count from. -/
private def bootClock : Nat := 1700000000 * 1000000000

/-- How long an instruction takes, in nanoseconds, as on a device of 1 GHz that runs one each cycle. -/
private def instructionNanos : Nat := 1

/-- A tick of `CNTFRQ_EL0`, 62.5 MHz, in nanoseconds, which `CNTVCT_EL0` counts. -/
private def counterNanos : Nat := 16

/-- A model that a machine has, with what it holds. -/
structure AttachedModel where
  id : String
  version : Nat
  state : ModelState
  /-- The tracker of taint that the model holds, if it is that model: see `RuntimeModel.tracker?`. -/
  tracker? : IO (Option Bap.Analysis.DynamicTaint.Tracker) := pure none

/-- What is in the kernel, in the emulator and in the models at once. -/
structure Machine.Kept where
  emulator : Snapshot
  run : RunState
  kernel : Kernel
  /-- What each model held, by its id, with the version that its bytes are of. -/
  models : List (String × Nat × ByteArray)

/-- What `Machine.stepBack` goes back with: where a run is, and what it was at some of the places that it has been. -/
structure Machine.History where
  /-- How many instructions apart what is kept is, at most, which is how many a step back may have to run again. -/
  every : Nat
  /-- How many of them are kept, of which the oldest go. -/
  limit : Nat
  /-- Where it is: how many instructions of all threads `Machine.run` has run since it started keeping this. -/
  position : Nat := 0
  /-- Where each was, the quantum of the run that went on from there, and what it was, the latest last. -/
  saved : Array (Nat × Nat × Machine.Kept) := #[]

/-- What a machine is, to go back to, with what it could step back to then: a machine that goes back to it is where that was, and steps back from there. -/
structure Machine.Saved extends Machine.Kept where
  history : Option Machine.History := none

/-- What a machine keeps of its tasks that is neither of the kernel's files nor of the emulator's table: what `set_robust_list` and
`prctl` say of them, and which processes share their descriptors. -/
structure TaskNotes where
  /-- The head of the robust list of each thread that has one, as `set_robust_list` gave it. -/
  robust : Std.HashMap Nat Nat := {}
  /-- The signal that each thread is sent when its parent ends, `PR_SET_PDEATHSIG`, of those that asked for one. -/
  deathSignals : Std.HashMap Nat Nat := {}
  /-- Of each process that isn't dumpable as a process is at first, what `PR_SET_DUMPABLE` made it. -/
  dumpable : Std.HashMap Nat Nat := {}
  /-- The processes that take in the children of their descendants that end, `PR_SET_CHILD_SUBREAPER`. -/
  subreapers : List Nat := []
  /-- The processes that have one table of descriptors between them, as `CLONE_FILES` made them, by sets of them. -/
  files : List (List Nat) := []
  /-- The children that a process had as its last thread ended, for what hears that it is over: they have another parent then. -/
  children : Std.HashMap Nat (List Nat) := {}
  /-- Of each thread, the flags of the `clone` that it is making, and the number of the system call that it last made. -/
  cloning : Std.HashMap Nat Nat := {}
  calls : Std.HashMap Nat Nat := {}

namespace TaskNotes

private def putPair (out : ByteArray) (entry : Nat × Nat) : ByteArray := Wire.putNat (Wire.putNat out entry.1) entry.2

private def getPair : Wire.Decoder (Nat × Nat) := fun data at_ => do
  let (first, at_) ← Wire.getNat data at_
  let (second, at_) ← Wire.getNat data at_
  .ok ((first, second), at_)

private def sorted (map : Std.HashMap Nat Nat) : List (Nat × Nat) := map.toList.mergeSort fun left right => left.1 ≤ right.1

/-- What a checkpoint has of it: all but what is of a call that is being served, as none is when a checkpoint is made. -/
def encode (notes : TaskNotes) : ByteArray :=
  let out := Wire.putList putPair ByteArray.empty (sorted notes.robust)
  let out := Wire.putList putPair out (sorted notes.deathSignals)
  let out := Wire.putList putPair out (sorted notes.dumpable)
  let out := Wire.putList Wire.putNat out notes.subreapers
  let out := Wire.putList (Wire.putList Wire.putNat) out notes.files
  Wire.putList putPair out (sorted notes.calls)

def decode (data : ByteArray) : Except String TaskNotes := do
  if data.isEmpty then return {}
  let (robust, at_) ← Wire.getList getPair data 0
  let (deathSignals, at_) ← Wire.getList getPair data at_
  let (dumpable, at_) ← Wire.getList getPair data at_
  let (subreapers, at_) ← Wire.getList Wire.getNat data at_
  let (files, at_) ← Wire.getList (Wire.getList Wire.getNat) data at_
  let (calls, at_) ← Wire.getList getPair data at_
  Wire.expectEnd data at_
  .ok { robust := .ofList robust, deathSignals := .ofList deathSignals, dumpable := .ofList dumpable, subreapers, files, calls := .ofList calls }

end TaskNotes

structure Machine where
  architecture : Architecture
  emu : Emu
  kernel : IO.Ref Kernel
  /-- The models of the runtime that it has, in the order that they were attached. -/
  models : IO.Ref (List AttachedModel)
  /-- What it was started from, which a checkpoint says: see `targetDigest`. -/
  target : Nat := 0
  /-- Whether it was given a `SyscallHandler`, which has to be given again to go on from a checkpoint. -/
  handled : Bool := false
  /-- What its processes do with signals, and what is pending. -/
  signals : Signals
  /-- What is traced and stopped, and what serves `ptrace` and the waits: see `Machine.servePtrace`. -/
  ptrace : Ptrace
  /-- The timers and the deadlines of the calls that wait with a timeout: see `Bap.Linux.Timers`. -/
  timers : Timers
  /-- What finds what `inotify` has to say after each call: see `Bap.Linux.Notify`. -/
  notifier : Notify.Notifier
  /-- The directories of the host that it sees, each as the path of the host and that of the tree: see `Machine.mountHost`, and
  `Kernel.hostSeen` of what it has brought in from there. -/
  hostMounts : IO.Ref (List (String × String))
  /-- What AIO and io_uring have: see `Bap.Linux.Ring`. -/
  rings : IO.Ref Ring.State
  /-- How many calls that may let go of something there were since what nothing holds was let go of: see `Kernel.collect`. -/
  releases : IO.Ref Nat
  /-- How many instructions had run (`Emu.retired`) at the last fault of mappings that are together, how many times in a row there
  was one with as many, and where the last of them that was a store was: see `siblingFault`. -/
  siblingFaults : IO.Ref (Nat × Nat × Option Nat)
  /-- What `Machine.malloc` has given out, by address space. -/
  heaps : IO.Ref (Std.HashMap Nat GuestHeap)
  /-- What `Machine.loadLibrary` has loaded, by address space. -/
  libraries : IO.Ref (Std.HashMap Nat (List LoadedLibrary))
  /-- What it goes back with, if it is kept. -/
  history : IO.Ref (Option Machine.History)
  /-- What hears that the machine was put back to what it was, by `restore`, `stepBack` or a checkpoint, with what put it back. -/
  restored : IO.Ref (List (String → IO Unit))
  /-- The directory that was last read, for the next piece of it: all the paths that it is of, which it is good for as long as those are the same object, its inode, what it has, and whether it is of `/proc`. -/
  listing : IO.Ref (Option (Std.HashMap String Nat × Nat × Array (Nat × Nat × String) × Bool))
  /-- The hook that serves each stub of a host function, by its address, so that a handler given again takes the place of the one
  before. -/
  hostHooks : IO.Ref (Std.HashMap Nat HookId)
  /-- Of each library that an import of was redirected, by where it is and its path: the slots of each name that it imports, as where
  each is from its base and what is added to what goes there, which reading its file once says. -/
  importSlots : IO.Ref (Std.HashMap (Nat × String) (Std.HashMap String (List (Nat × Nat))))
  /-- How many of the instructions that the emulator has run (`Emu.retired`) the clock of the kernel has gone on by: see
  `Machine.advanceClock`. -/
  clockCounted : IO.Ref Nat
  /-- What `set_robust_list`, `prctl` and `CLONE_FILES` said of its tasks: see `TaskNotes`. -/
  notes : IO.Ref TaskNotes

/-- A model of a runtime that isn't in the kernel or the emulator: pthreads served by hooks, a debugger, a managed language.
`id` is what a checkpoint knows it by, so that it stays the same, and `version` says what its bytes mean.

`attach` runs when a machine starts and again when one goes on from a checkpoint, as what it registers are functions, which can't be
in a file. It puts its hooks on `machine.emu`, in front of the kernel, and gives what holds its state. It should do nothing else to
the guest, whose memory is already what the checkpoint says when it runs again. -/
structure RuntimeModel where
  id : String
  version : Nat := 1
  attach : Machine → IO ModelState
  /-- The tracker of taint that the model holds once it is attached, for the model of taint. `ModelState` is only `save` and `load`,
  and a machine that goes on from a checkpoint has attached the model and loaded what was kept into what it holds before a caller
  sees it, so this is the only way to that tracker, rather than a second one that attaching again would make. -/
  tracker? : IO (Option Bap.Analysis.DynamicTaint.Tracker) := pure none

/-- Attaches a model, as `start` and `Machine.ofCheckpoint` do those that they are given, or to a machine that runs already: what it
holds is in a checkpoint from then on, which then needs the model to go on from. Its id can't be one that the machine has. -/
def Machine.attachModel (machine : Machine) (model : RuntimeModel) : IO ModelState := do
  if (← machine.models.get).any (·.id == model.id) then
    throw <| IO.userError s!"two models of a runtime are called {model.id}"
  let state ← model.attach machine
  machine.models.modify (· ++ [{ id := model.id, version := model.version, state, tracker? := model.tracker? }])
  pure state

private unsafe def sameObjectImpl {α : Type} (left right : α) : Bool := ptrAddrUnsafe left == ptrAddrUnsafe right

/-- Whether two things are one object, by which what was found out about it is still good. It may say no when they are only equal. -/
@[implemented_by sameObjectImpl] private def sameObject {α : Type} (_ _ : α) : Bool := false

/-- A signed word of `width` bits, as whether it is negative and how far from zero it is. -/
private def signed (width value : Nat) : Bool × Nat :=
  if value ≥ 2 ^ (width - 1) then (true, 2 ^ width - value) else (false, value)

/-- `AT_FDCWD`. -/
private def atCwd (value : Nat) : Bool := value == 2 ^ 64 - 100 || value == 2 ^ 32 - 100

private def pageUp (value : Nat) : Nat := (value + 4095) / 4096 * 4096
private def pageDown (value : Nat) : Nat := value / 4096 * 4096

/-- Bytes of a guest up to a zero, a page at a time, of at most `limit` bytes: one that has no zero by then is that much of it, which a path
of `PATH_MAX` makes `ENAMETOOLONG` of. -/
private def readString (emu : Emu) (address : Nat) (limit : Nat := 4096) : IO String := do
  let rec go : Nat → Nat → ByteArray → IO ByteArray
    | 0, _, out => pure out
    | fuel + 1, from_, out => do
      if out.size ≥ limit then return out.extract 0 limit
      let bytes ← read emu from_ (pageUp (from_ + 1) - from_)
      match bytes.data.findIdx? (· == 0) with
      | some index => pure ((out ++ bytes.extract 0 index).extract 0 limit)
      | none => go fuel (from_ + bytes.size) (out ++ bytes)
  pure (textOf (← go (limit / 4096 + 2) address ByteArray.empty))

/-- Writes across as many mappings as it takes, which a buffer on the program break or the stack may. -/
private def writeGuest (emu : Emu) (address : Nat) (data : ByteArray) : IO Unit := do
  let rec go : Nat → Nat → Nat → IO Unit
    | 0, _, _ => pure ()
    | fuel + 1, at_, done => do
      if done < data.size then
        let stop := min (pageDown at_ + 4096) (address + data.size)
        write emu at_ (data.extract done (done + stop - at_))
        go fuel stop (done + stop - at_)
  go (data.size / 4096 + 2) address 0

/-- A successful result, with the bytes it leaves at an address the guest gave: of one that isn't there, NULL too, `EFAULT`. -/
private def returning (emu : Emu) (address : Nat) (data : ByteArray) (value : Nat := 0) : IO SyscallAction := do
  try
    if !data.isEmpty then writeGuest emu address data
    pure (.returnValue value)
  catch _ => pure (.returnValue (2 ^ 64 - Errno.efault))

/-- `returning`, of a call that may be given NULL for what it says, which it then doesn't say. -/
private def returningIf (emu : Emu) (address : Nat) (data : ByteArray) (value : Nat := 0) : IO SyscallAction :=
  if address == 0 then pure (.returnValue value) else returning emu address data value

private def errorOf (errno : Nat) : SyscallAction := .returnValue (2 ^ 64 - errno)

/-- What of `count` bytes at an address the guest gave may be read, from the first: all of them, or those before the first page that
can't be, as `copy_from_user` gives up there, so that what is written of them is what a write writes. -/
private def readPrefix (emu : Emu) (address count : Nat) : IO ByteArray := do
  match ← (read emu address count).toBaseIO with
  | .ok bytes => pure bytes
  | .error _ =>
    let mut out := ByteArray.empty
    while out.size < count do
      let size := min (4096 - (address + out.size) % 4096) (count - out.size)
      match ← (read emu (address + out.size) size).toBaseIO with
      | .ok bytes => out := out ++ bytes
      | .error _ => break
    pure out

/-- What a read gives of `data` at an address the guest gave: as many bytes as fit before the first page that can't be written, as
`copy_to_user` gives up there, and of none, `EFAULT`. -/
private def returningPrefix (emu : Emu) (address : Nat) (data : ByteArray) : IO SyscallAction := do
  let done ← match ← (writeGuest emu address data).toBaseIO with
    | .ok _ => pure data.size
    | .error _ => do
      let mut done := 0
      while done < data.size do
        let size := min (4096 - (address + done) % 4096) (data.size - done)
        match ← (write emu (address + done) (data.extract done (done + size))).toBaseIO with
        | .ok _ => done := done + size
        | .error _ => break
      pure done
  pure (if done == 0 && data.size > 0 then errorOf Errno.efault else .returnValue done)

/-- Runs a change of the kernel, whose output goes where the machine says. -/
private def apply (machine : Machine) (change : Kernel → Result Kernel) (value : Nat := 0) : IO SyscallAction := do
  match change (← machine.kernel.get) with
  | .ok kernel =>
    machine.kernel.set kernel
    pure (.returnValue value)
  | .error errno => pure (errorOf errno)

private def applyNat (machine : Machine) (change : Kernel → Result (Kernel × Nat)) : IO SyscallAction := do
  match change (← machine.kernel.get) with
  | .ok (kernel, value) =>
    machine.kernel.set kernel
    pure (.returnValue value)
  | .error errno => pure (errorOf errno)

/-- The bits of a protection, as `mmap` has them. -/
private def protectionBits (protection : Primus.Protection) : Nat :=
  (if protection.readable then 1 else 0) + (if protection.writable then 2 else 0) + (if protection.executable then 4 else 0)

/-- `MAP_SHARED` or `MAP_SHARED_VALIDATE`. -/
private def mapsShared (flags : Nat) : Bool := flags &&& 1 != 0

/-- `MAP_GROWSDOWN`, which MIPS numbers apart. -/
private def Architecture.mapGrowsDown : Architecture → Nat
  | .mips .. => 0x1000
  | _ => 0x100

/-- The task that runs, if it is still in the table. -/
private def runningGroup (emu : Emu) : IO (Option Nat) := do
  pure (((← emu.taskTable.get).find? (← thread emu)).map (·.group))

/-- Pieces of `size` bytes from `start`, the last of what is left. -/
private def chunksOf (start size : Nat) (piece : Nat := 65536) : List (Nat × Nat) :=
  (List.range ((size + piece - 1) / piece)).map fun index => (start + index * piece, min piece (size - index * piece))

/-- Where a mapping of `size` bytes at `start` may have something to look at: the `extent` of it that is of the file, a piece at a time,
and of the rest, which is zeros but where it was written, the pages that native memory has, which are all that were. What the host has of
a mapping is then of what the file has and of what was written, however large the mapping. -/
private def piecesOf (emu : Emu) (start size extent : Nat) : IO (List (Nat × Nat)) := do
  let extent := min extent size
  let chunks := chunksOf start extent
  if extent == size then return chunks
  match ← emu.engine.persistentMemory.get with
  | some memory =>
    let pageSize := (Jit.pageSize ()).toNat
    let pages ← Jit.pagesIn memory (UInt64.ofNat (start + extent)) (UInt64.ofNat (start + size - 1))
    pure (chunks ++ pages.toList.map fun page =>
      let first := max page.toNat (start + extent)
      (first, min (page.toNat + pageSize) (start + size) - first))
  | none => pure (chunks ++ chunksOf (start + extent) (size - extent))

/-- A mapping has what the file has, in the pages where it has something else. -/
private def refreshMapping (emu : Emu) (kernel : Kernel) (mapping : FileMapping) : IO Unit := do
  let extent := kernel.inodeExtent mapping.inode mapping.offset mapping.size
  for (at_, length) in ← piecesOf emu mapping.start mapping.size extent do
    let wanted := kernel.inodeBytes mapping.inode (mapping.offset + (at_ - mapping.start)) length
    let memory ← peek emu at_ length
    if wanted != memory then
      for (first, size) in chunksOf 0 length 4096 do
        let page := wanted.extract first (first + size)
        if page != memory.extract first (first + size) then
          poke emu (at_ + first) page (known := true)

/-- Where a mapping is of what is in a file, before or after: past that it is zeros of both. -/
private def extentOfBoth (before after : Kernel) (mapping : FileMapping) : Nat :=
  max (before.inodeExtent mapping.inode mapping.offset mapping.size) (after.inodeExtent mapping.inode mapping.offset mapping.size)

/-- A private mapping has what the file has now in the pages that are as the file was, which are those that the process hasn't written,
as Linux copies a page of one when it is written and until then has the file's. A page that was written with what was there is taken
for one that wasn't. -/
private def refreshUntouched (emu : Emu) (before after : Kernel) (mapping : FileMapping) : IO Unit := do
  -- What is the same object as it was is unchanged, which is what most calls leave a file.
  if let (some old, some new) := (before.inodes.get? mapping.inode, after.inodes.get? mapping.inode) then
    if sameObject old.content new.content then return
  for (at_, length) in chunksOf mapping.start (extentOfBoth before after mapping) do
    let offset := mapping.offset + (at_ - mapping.start)
    let was := before.inodeBytes mapping.inode offset length
    let now := after.inodeBytes mapping.inode offset length
    if was != now then
      let memory ← peek emu at_ length
      for (first, size) in chunksOf 0 length 4096 do
        let old := was.extract first (first + size)
        let page := now.extract first (first + size)
        if page != old && memory.extract first (first + size) == old then
          poke emu (at_ + first) page (known := true)
          for mirrored in ← emu.memoryMirrored.get do mirrored (at_ + first) size (Kernel.fileSpace + mapping.inode) (offset + first) true

/-- What a process wrote to its shared mappings goes to their files, which is how any other mapping or a `read` sees it. A running
process is the only one that can have written since it came to run, and whatever else it has mapped of a file is as the file was, so
that what differs from the file is what it wrote: it happens before any system call and when another process is to run. -/
private def flushShared (machine : Machine) (emu : Emu) : IO Unit := do
  let some group ← runningGroup emu | return
  -- What was written, of which file, where, what the file had there and what memory has: each of what the file had as the process
  -- came to run, as another mapping of it that hasn't written there has that, and isn't to undo what one that has wrote.
  let (mappings, changes) ← do
    let start ← machine.kernel.get
    let mappings := (start.process group).mappings
    let mut changes : Array (Nat × Nat × ByteArray × ByteArray) := #[]
    -- A piece at a time, and of native memory only the pages that it has, which are all that was written: what nothing wrote is as the
    -- file was, and a large mapping that little of is written takes little.
    let native ← emu.engine.persistentMemory.get
    let pageSize := (Jit.pageSize ()).toNat
    for mapping in mappings do
      if mapping.shared && mapping.mayWrite then
        let size := start.inodeExtent mapping.inode mapping.offset mapping.size
        if size > 0 then
          let pieces : List (Nat × Nat) ← match native with
            | some memory => do
              let pages ← Jit.pagesIn memory (UInt64.ofNat mapping.start) (UInt64.ofNat (mapping.start + size - 1))
              pure (pages.toList.map fun page =>
                let first := max page.toNat mapping.start
                (first, min (page.toNat + pageSize) (mapping.start + size) - first))
            | none => pure (chunksOf mapping.start size)
          for (at_, length) in pieces do
            let offset := mapping.offset + (at_ - mapping.start)
            let memory ← peek emu at_ length
            let before := start.inodeBytes mapping.inode offset length
            if memory != before then changes := changes.push (mapping.inode, offset, before, memory)
    pure (mappings, changes)
  if changes.isEmpty then return
  -- The kernel as it was is let go of before the files are written, so that what is written is written in place, rather than in a copy
  -- of all of a file.
  for (inode, offset, before, memory) in changes do
    machine.kernel.modify (·.writeChanges inode offset before memory)
  -- Another mapping of the same file sees it, and a private one where the process hasn't written it: a page of one that is as the file
  -- was before has what it is now.
  let flushed ← machine.kernel.get
  for mapping in mappings do
    if mapping.shared then refreshMapping emu flushed mapping
    else
      for (inode, offset, before, _) in changes do
        let first := max offset mapping.offset
        let last := min (offset + before.size) (mapping.offset + mapping.size)
        if inode == mapping.inode && first < last then
          for (at_, size) in chunksOf first (last - first) 4096 do
            let old := before.extract (at_ - offset) (at_ - offset + size)
            let page := flushed.inodeBytes inode at_ size
            let address := mapping.start + (at_ - mapping.offset)
            if page != old && (← peek emu address size) == old then
              poke emu address page (known := true)
              for mirrored in ← emu.memoryMirrored.get do mirrored address size (Kernel.fileSpace + inode) at_ false

/-- What the files of a process's shared mappings hold, for when it comes to run. -/
private def refreshShared (machine : Machine) (emu : Emu) : IO Unit := do
  let some group ← runningGroup emu | return
  let kernel ← machine.kernel.get
  for mapping in (kernel.process group).mappings do
    if mapping.shared then refreshMapping emu kernel mapping

/-- A call changed a file: its mappings have that now. Only those, as a call may have left something in a mapping itself. -/
private def refreshChanged (machine : Machine) (emu : Emu) (before : Kernel) : IO Unit := do
  let some group ← runningGroup emu | return
  let kernel ← machine.kernel.get
  for mapping in (kernel.process group).mappings do
    if !mapping.shared then refreshUntouched emu before kernel mapping
    else if (chunksOf mapping.start (extentOfBoth before kernel mapping)).any fun (at_, length) =>
        let offset := mapping.offset + (at_ - mapping.start)
        kernel.inodeBytes mapping.inode offset length != before.inodeBytes mapping.inode offset length then
      refreshMapping emu kernel mapping

/-- Where a thread that waits on a pipe waits, which is no address space, of which there are as many as tasks. -/
private def pipeSpace : Nat := 2 ^ 61

/-- Everyone that waits on a pipe tries again, as something has changed, whichever it was. -/
private def wakePipeReaders (emu : Emu) : IO Unit := do
  let table ← emu.taskTable.get
  -- Not those of shared futexes, from `Kernel.fileSpace`, which only a wake of their word wakes.
  let waiting := (table.futexes.filter fun waiter => pipeSpace ≤ waiter.space && waiter.space < Kernel.fileSpace).map (·.space) |>.eraseDups
  for space in waiting do
    let (table, woken) := (← emu.taskTable.get).futexWake space 0 (2 ^ 32 - 1) (2 ^ 32)
    emu.taskTable.set table
    for thread in woken do wakeThread emu thread

/-- `mmap` of memory that a child goes on sharing, which is a file that nothing else can open. -/
private def serveSharedMemory (machine : Machine) (group address size bits flags : Nat) : IO SyscallAction := do
  -- Of nothing, or what would grow, which only what is private does, as `do_mmap` has it.
  if size == 0 || flags &&& machine.architecture.mapGrowsDown != 0 then
    return errorOf Errno.einval
  let pages := pageUp size
  let (address, fixed) ← match ← mmapPlace machine.emu address pages flags with
    | .ok place => pure place
    | .error errno => return errorOf errno
  try
    let start ← placeZeros machine.emu address fixed pages bits
    machine.kernel.modify fun kernel =>
      let (kernel, inode) := kernel.anonymousInode (Jit.zeros pages)
      (kernel.dropMappings group start (start + pages)).addMapping group
        { start, size := pages, inode, offset := 0, shared := true, mayWrite := true }
    pure (.returnValue start)
  catch _ => pure (errorOf Errno.enomem)

/-- `mmap`: of a file, here, of which a shared one writes back. What is anonymous is for `serveTaskCalls`. -/
private def serveFileMap (machine : Machine) (group address size bits flags fd offset : Nat) : IO SyscallAction := do
  let emu := machine.emu
  if size == 0 || offset % 4096 != 0 || flags &&& 3 == 0 then
    return errorOf Errno.einval
  let kernel ← machine.kernel.get
  match kernel.mappingSource group fd with
  | .error errno => pure (errorOf errno)
  | .ok (inode, canRead, canWrite) =>
    -- Of a file, nothing grows, as `do_mmap` has it; and what would end past the largest offset that a file has is `EOVERFLOW`, as
    -- `file_mmap_ok` has it.
    if flags &&& machine.architecture.mapGrowsDown != 0 then return errorOf Errno.einval
    if offset + pageUp size > 2 ^ 63 - 1 then return errorOf 75
    let (address, fixed) ← match ← mmapPlace emu address (pageUp size) flags with
      | .ok place => pure place
      | .error errno => return errorOf errno
    let shared := mapsShared flags
    if !canRead || (shared && bits &&& 2 != 0 && !canWrite) then
      return errorOf Errno.eacces
    -- Of a file that has no `mmap`, `ENODEV`; `/dev/zero` maps what `mmap` of no file does, private or shared, as `mmap_zero` has it.
    match (kernel.inodes.get? inode).map Inode.content with
    | some (.device 1) =>
      if shared then return ← serveSharedMemory machine group address size bits flags
      let pages := pageUp size
      try
        let start ← placeZeros emu address fixed pages bits
        machine.kernel.modify (·.dropMappings group start (start + pages))
        return .returnValue start
      catch _ => return errorOf Errno.enomem
    | some (.file _) | some .directory | none => pure ()
    | some _ => return errorOf Errno.enodev
    -- `F_SEAL_WRITE` and `F_SEAL_FUTURE_WRITE`.
    if shared && bits &&& 2 != 0 && (kernel.inodes.get? inode).any (·.details.seals &&& 0x18 != 0) then
      return errorOf Errno.eperm
    match kernel.mappedBytes group fd offset (pageUp size) with
    | .error errno => pure (errorOf errno)
    | .ok data =>
      try
        -- Zeros that the host makes only as they are written, as of `mmap` of no file, with what the file has of it on them: a mapping
        -- larger than its file costs the host no more than the file.
        let pages := pageUp size
        let start ← placeZeros emu address fixed pages bits
        if !data.isEmpty then poke emu start data (known := shared)
        machine.kernel.modify fun kernel =>
          (kernel.dropMappings group start (start + pages)).addMapping group
            { start, size := pages, inode, offset, shared, mayWrite := canWrite }
        pure (.returnValue start)
      catch _ => pure (errorOf Errno.enomem)

/-- What `MADV_DONTNEED` leaves of `address`..`address + pages`: zeros, with what a file behind them has on them. -/
private def zapPages (machine : Machine) (group address pages : Nat) : IO Unit := do
  let emu := machine.emu
  let kernel ← machine.kernel.get
  clearMapped emu address pages
  for mapping in (kernel.process group).mappings.filter (·.overlaps address (address + pages)) do
    let first := max mapping.start address
    let stop := min (mapping.start + mapping.size) (address + pages)
    poke emu first (kernel.inodeBytes mapping.inode (mapping.offset + (first - mapping.start)) (stop - first)) (known := mapping.shared)

/-- The bits of a `Guard` that keeps nothing from being accessed and only says something of where it is, which `/proc/PID/maps` and a
fault go by: that it was asked for to be written and not read, `PROT_WRITE` alone, which is mapped so that it can be read, as the
page tables have it; and that it is a mapping of `MAP_GROWSDOWN`, from where it starts now. -/
private def Guard.writeOnly : Nat := 32
private def Guard.growsDown : Nat := 64
private def Guard.isNote (guard : Guard) : Bool := guard.bits &&& (Guard.writeOnly ||| Guard.growsDown) != 0

/-- The guards of a process with one that only says something, of `bits`, of `lower`..`upper`, in place of what said that of any of it. -/
private def noted (kernel : Kernel) (group lower upper bits : Nat) (holds : Bool) : Kernel :=
  let process := kernel.process group
  let (said, rest) := process.guards.partition fun guard => guard.bits == bits
  let holds := holds && lower < upper
  if said.isEmpty && !holds then kernel
  else kernel.setProcess group { process with
    guards := rest ++ said.flatMap (·.without lower upper) ++ (if holds then [{ start := lower, size := upper - lower, bits }] else []) }

/-- The pieces of `lower`..`upper` by the protection that each has, as `mprotect` has its bits, of what is mapped. -/
private def protectionsOf (regions : List Region) (lower upper : Nat) : List Guard := Id.run do
  let mut out := []
  let mut position := lower
  for _ in [0:regions.length + 1] do
    if position ≥ upper then break
    match lookupRegion regions position with
    | some region =>
      let stop := min upper (region.address + region.data.size)
      let bits := (if region.protection.readable then 1 else 0) ||| (if region.protection.writable then 2 else 0) |||
        (if region.protection.executable then 4 else 0)
      out := out ++ [{ start := position, size := stop - position, bits }]
      position := stop
    | none => break
  pure out

/-- `MADV_REMOVE`, `MADV_GUARD_INSTALL` and `MADV_GUARD_REMOVE` of `address`..`upper`, which is mapped. `MADV_REMOVE` punches a hole in
what is shared, as `madvise_remove` has it: of what isn't, `EINVAL`, and of what may not be written, `EACCES`. A guard, as
`madvise_guard_install` puts it on, leaves what was there as `MADV_DONTNEED` does and keeps it from being read, written or run until it is
taken off, which gives back the protection it had. -/
private def serveRemoval (machine : Machine) (group address upper advice : Nat) : IO SyscallAction := do
  let emu := machine.emu
  let kernel ← machine.kernel.get
  let process := kernel.process group
  let pieces := protectionsOf (← emu.regions.get) address upper
  match advice with
  | 9 =>
    let shared := process.mappings.filter fun mapping => mapping.shared && mapping.overlaps address upper
    -- Each byte of it is of a shared mapping.
    let covered := Id.run do
      let mut position := address
      for _ in [0:shared.length + 1] do
        match shared.find? fun mapping => mapping.start ≤ position && position < mapping.start + mapping.size with
        | some mapping => position := mapping.start + mapping.size
        | none => break
      pure (decide (position ≥ upper))
    if !covered then return errorOf Errno.einval
    if pieces.any (·.bits &&& 2 == 0) then return errorOf Errno.eacces
    machine.kernel.modify fun kernel => shared.foldl (init := kernel) fun kernel mapping =>
      let first := max mapping.start address
      let stop := min (mapping.start + mapping.size) upper
      kernel.punch mapping.inode (mapping.offset + (first - mapping.start)) (stop - first)
    clearMapped emu address (upper - address)
    pure (.returnValue 0)
  | 102 =>
    -- What has a guard already keeps the protection that it had before.
    let fresh := (process.guards.filter (!·.isNote)).foldl (init := pieces) fun pieces guard =>
      pieces.flatMap (·.without guard.start (guard.start + guard.size))
    zapPages machine group address (upper - address)
    protect emu address (upper - address) ⟨false, false, false⟩
    machine.kernel.modify fun kernel =>
      let process := kernel.process group
      kernel.setProcess group { process with guards := process.guards ++ fresh }
    pure (.returnValue 0)
  | _ =>
    let (notes, guards) := process.guards.partition (·.isNote)
    for guard in guards do
      let first := max guard.start address
      let stop := min (guard.start + guard.size) upper
      if first < stop then
        protect emu first (stop - first) ⟨guard.bits &&& 1 != 0, guard.bits &&& 2 != 0, guard.bits &&& 4 != 0⟩
    machine.kernel.set (kernel.setProcess group { process with guards := notes ++ guards.flatMap (·.without address upper) })
    pure (.returnValue 0)

/-- Where a mapping of a file is past the last page that the file has any of, if it is anywhere. -/
private def pastEnd (kernel : Kernel) (mapping : FileMapping) : Option (Nat × Nat) :=
  match kernel.inodes.get? mapping.inode with
  | some { content := .file data, .. } =>
    let within := min mapping.size (pageUp (data.size - mapping.offset))
    if within < mapping.size then some (mapping.start + within, mapping.start + mapping.size) else none
  | _ => none

/-- Ranges in order, with those that touch or overlap as one. -/
private def mergeRanges (ranges : List (Nat × Nat)) : List (Nat × Nat) :=
  let sorted := (ranges.toArray.qsort fun first second => first.1 < second.1).toList
  (sorted.foldl (init := []) fun merged (lower, upper) =>
    match merged with
    | (start, stop) :: rest => if lower ≤ stop then (start, max stop upper) :: rest else (lower, upper) :: merged
    | [] => [(lower, upper)]).reverse

/-- Ranges without what is in any of `others`. -/
private def rangesWithout (ranges others : List (Nat × Nat)) : List (Nat × Nat) :=
  others.foldl (init := ranges) fun ranges (lower, upper) => ranges.flatMap fun (start, stop) =>
    if stop ≤ lower || upper ≤ start then [(start, stop)]
    else (if start < lower then [(start, lower)] else []) ++ (if upper < stop then [(upper, stop)] else [])

/-- Where the shared mappings of a process have pages of a file that another shared mapping of it has too, as a segment attached
twice or a file mapped twice does: what is written through one is what the other reads, at once. -/
private def siblingRanges (process : Process) : List (Nat × Nat) :=
  let shared := process.mappings.filter (·.shared)
  if shared.length < 2 then [] else
    mergeRanges <| shared.flatMap fun mapping => shared.filterMap fun other =>
      let lower := max mapping.offset other.offset
      let upper := min (mapping.offset + mapping.size) (other.offset + other.size)
      if other.inode == mapping.inode && other.start != mapping.start && lower < upper then
        some (mapping.start + (lower - mapping.offset), mapping.start + (upper - mapping.offset))
      else none

private def Guard.isPastEnd (guard : Guard) : Bool := guard.bits &&& Guard.pastEnd != 0
private def Guard.isSibling (guard : Guard) : Bool := guard.bits &&& Guard.sibling != 0
private def Guard.protection (guard : Guard) (writable : Bool := true) : Primus.Protection :=
  ⟨guard.bits &&& 1 != 0, writable && guard.bits &&& 2 != 0, guard.bits &&& 4 != 0⟩

/-- The pages of a file that a guard of `Guard.sibling` is of: the file, and from where to where of it. -/
private def Guard.pagesOf (process : Process) (guard : Guard) : Option (Nat × Nat × Nat) :=
  (process.mappings.find? fun mapping => mapping.shared && mapping.start ≤ guard.start && guard.start < mapping.start + mapping.size).map
    fun mapping => (mapping.inode, mapping.offset + (guard.start - mapping.start), mapping.offset + (guard.start - mapping.start) + guard.size)

/-- The guards of `Guard.sibling` of the process that runs. -/
private def siblingsOf (machine : Machine) (emu : Emu) : IO (List Guard) := do
  let some group ← runningGroup emu | return []
  let guards := ((← machine.kernel.get).process group).guards
  pure (if guards.isEmpty then [] else guards.filter (·.isSibling))

/-- Every mapping that has the pages of another has the protection that it was given, as a system call goes by, or that without
writing, as the program runs from when all of them hold the same: see `settleMappings`. -/
private def protectSiblings (machine : Machine) (emu : Emu) (writable : Bool) : IO Unit := do
  for guard in ← siblingsOf machine emu do
    try protect emu guard.start guard.size (guard.protection writable) catch _ => pure ()

/-- The mappings of the process that runs are as their files are now, in two ways, each of which is a guard that says what the
protection of the pages was given as, while they have another.

A page that is wholly past the end of its file can't be read, written or run, an access of which is `SIGBUS`, as Linux has it of a
mapping longer than its file or of a file that was cut short, and what was written there is gone; a page that the file has again has
the protection that it had, and what the file has: `Guard.pastEnd`.

Two shared mappings of the same pages of a file are the same memory on Linux, and here each has bytes of its own, which a system call
makes the same (`flushShared`). Between calls they are kept the same by their protection (`Guard.sibling`): none can be written while
all hold the same; the first that is written, which faults, then can be, and the others can't be accessed at all; and an access of
one of those, which faults, copies to them what was written and starts again (`siblingFault`). A system call finds them with what
they were given, and leaves them as at the start. -/
private def settleMappings (machine : Machine) (emu : Emu) : IO Unit := do
  let some group ← runningGroup emu | return
  let kernel ← machine.kernel.get
  let process := kernel.process group
  if process.mappings.isEmpty then return
  let ends := process.mappings.filterMap (pastEnd kernel)
  let siblings := rangesWithout (siblingRanges process) ends
  let (heldEnds, rest) := process.guards.partition (·.isPastEnd)
  let (heldSiblings, guards) := rest.partition (·.isSibling)
  if ends.isEmpty && siblings.isEmpty && heldEnds.isEmpty && heldSiblings.isEmpty then return
  let rangeOf (guard : Guard) : Nat × Nat := (guard.start, guard.start + guard.size)
  let outside (held : List Guard) (wanted : List (Nat × Nat)) : List Guard :=
    wanted.foldl (init := held) fun pieces (lower, upper) => pieces.flatMap (·.without lower upper)
  let inside (held : List Guard) (wanted : List (Nat × Nat)) : List Guard :=
    held.flatMap fun guard => wanted.filterMap fun (lower, upper) =>
      let first := max guard.start lower
      let stop := min (guard.start + guard.size) upper
      if first < stop then some { guard with start := first, size := stop - first } else none
  let freed := outside heldEnds ends ++ outside heldSiblings siblings
  let freshEnds := rangesWithout ends (heldEnds.map rangeOf)
  let freshSiblings := rangesWithout siblings (heldSiblings.map rangeOf)
  if freed.isEmpty && freshEnds.isEmpty && freshSiblings.isEmpty then return
  let piecesOf (ranges : List (Nat × Nat)) (bit : Nat) : IO (List Guard) := do
    let regions ← emu.regions.get
    pure (ranges.flatMap fun (lower, upper) => (protectionsOf regions lower upper).map fun piece => { piece with bits := piece.bits ||| bit })
  try
    -- What is a guard no longer, and what stays one of mappings that are together, have what they were given, which is what a
    -- new guard keeps of what it takes the place of.
    for guard in freed ++ inside heldSiblings siblings do protect emu guard.start guard.size guard.protection
    let newEnds ← piecesOf freshEnds Guard.pastEnd
    for piece in newEnds do
      clearMapped emu piece.start piece.size
      protect emu piece.start piece.size ⟨false, false, false⟩
    let newSiblings ← piecesOf freshSiblings Guard.sibling
    machine.kernel.set (kernel.setProcess group { process with
      guards := guards ++ inside heldEnds ends ++ newEnds ++ inside heldSiblings siblings ++ newSiblings })
  catch _ => pure ()

/-- What `settleMappings` keeps with another protection in `lower`..`upper` has the one that it was given, and isn't kept, for a call
that goes by what the pages were given, as `mremap` does: `settleMappings` keeps anew what is there after it. -/
private def releaseMappings (machine : Machine) (emu : Emu) (group lower upper : Nat) : IO Unit := do
  let kernel ← machine.kernel.get
  let process := kernel.process group
  let (kept, guards) := process.guards.partition fun guard => guard.isPastEnd || guard.isSibling
  if !kept.any fun guard => guard.start < upper && lower < guard.start + guard.size then return
  for guard in kept do
    let first := max guard.start lower
    let stop := min (guard.start + guard.size) upper
    if first < stop then
      try protect emu first (stop - first) guard.protection catch _ => pure ()
  machine.kernel.set (kernel.setProcess group { process with guards := guards ++ kept.flatMap (·.without lower upper) })

/-- A fault of the process that runs below a mapping of `MAP_GROWSDOWN`, with nothing mapped between them: the mapping grows down to
the page of the fault, as `expand_stack` has it, and the instruction runs again. Not past what `RLIMIT_STACK` lets a stack be, nor
to within the gap that Linux keeps below a stack, of 256 pages, of a mapping that can be accessed and doesn't grow itself. -/
private def growStack (machine : Machine) (emu : Emu) (fault : MemoryFault) : IO Bool := do
  let some group ← runningGroup emu | return false
  let kernel ← machine.kernel.get
  let process := kernel.process group
  let growing := process.guards.filter (·.bits == Guard.growsDown)
  if growing.isEmpty then return false
  let address := emu.config.untag fault.address
  let start := pageDown address
  let some guard := (growing.filter fun guard => address < guard.start).foldl (init := none) (fun (best : Option Guard) guard =>
    if best.all (guard.start < ·.start) then some guard else best) | return false
  let regions ← emu.regions.get
  -- What is mapped first above the fault is the mapping that grows.
  if regions.any fun region => region.data.size > 0 && region.address + region.data.size > address && region.address < guard.start then
    return false
  let some above := lookupRegion regions guard.start | return false
  if start < 0x10000 || guard.start + guard.size - start > (kernel.limitOf group 3).1 then return false
  let gap := 256 * 4096
  let near := regions.any fun region =>
    let finish := region.address + region.data.size
    region.data.size > 0 && finish ≤ start && start - finish < gap &&
      (region.protection.readable || region.protection.writable || region.protection.executable) &&
      !growing.any fun other => other.start ≤ region.address && region.address < other.start + other.size
  if near then return false
  try
    mapZeros emu start (guard.start - start) above.protection
    machine.kernel.set (kernel.setProcess group { process with
      guards := process.guards.map fun other =>
        if other == guard then { guard with start, size := guard.size + (guard.start - start) } else other })
    pure true
  catch _ => pure false

/-- Whether an address of the process that runs is of a mapping where its file has no page, as `settleMappings` keeps it. -/
private def isPastEnd (machine : Machine) (emu : Emu) (address : Nat) : IO Bool := do
  let some group ← runningGroup emu | return false
  pure (((← machine.kernel.get).process group).guards.any fun guard =>
    guard.isPastEnd && guard.start ≤ address && address < guard.start + guard.size)

/-- A fault of the process that runs, if it is one of mappings that have the pages of another and are kept the same by their
protection, as `settleMappings` has it, rather than one of the program's: whether it was, and then the instruction runs again.

- A store to one of them while all hold the same: it can be written from now, and those that have pages of it can't be accessed.
- An access while one can be written: what that one has goes to those that have its pages, and all hold the same again.
- An instruction that comes here a third time without having run, as one that copies from one to another, or that is itself in
  one and stores to another, is run by itself with all of them as they were given, and what it stored goes to the others. -/
private def siblingFault (machine : Machine) (emu : Emu) (fault : MemoryFault) : IO Bool := do
  let some group ← runningGroup emu | return false
  let process := (← machine.kernel.get).process group
  if process.guards.isEmpty then return false
  let guards := process.guards.filter (·.isSibling)
  let some guard := guards.find? fun guard => guard.start ≤ fault.address && fault.address < guard.start + guard.size | return false
  let needed := match fault.operation with
    | .read => 1
    | .write => 2
    | .fetch => 4
  -- What it was never given is the program's fault.
  if guard.bits &&& needed == 0 then return false
  let together (other : Guard) : Bool := other.start != guard.start && match guard.pagesOf process, other.pagesOf process with
    | some (inode, lower, upper), some (inode', lower', upper') => inode == inode' && lower < upper' && lower' < upper
    | _, _ => false
  -- What `owner` has goes to each of the others where they have its pages.
  let copyFrom (owner : Guard) : IO Unit := do
    let some (inode, lower, upper) := owner.pagesOf process | return
    for other in guards do
      let some (inode', lower', upper') := other.pagesOf process | continue
      if other.start == owner.start || inode != inode' then continue
      let first := max lower lower'
      let stop := min upper upper'
      if first < stop then
        for (at_, length) in chunksOf first (stop - first) do
          let bytes ← peek emu (owner.start + (at_ - lower)) length
          if bytes != (← peek emu (other.start + (at_ - lower')) length) then
            poke emu (other.start + (at_ - lower')) bytes (known := true)
  let regions ← emu.regions.get
  let owners := guards.filter fun other => (lookupRegion regions other.start).any (·.protection.writable)
  let retired ← emu.retired.get
  let (last, times, stored) ← machine.siblingFaults.get
  let times := if last == retired then times + 1 else 1
  let stored := if fault.operation == .write then some fault.address else if last == retired then stored else none
  machine.siblingFaults.set (retired, times, stored)
  if times ≥ 3 then
    for owner in owners do copyFrom owner
    protectSiblings machine emu true
    emu.lastFault.set none
    let stepped ← (step emu).toBaseIO
    protectSiblings machine emu false
    match stepped with
    | .ok _ =>
      -- What it stored is in the one that it faulted of storing to.
      let written := stored.bind fun address => guards.find? fun other => other.start ≤ address && address < other.start + other.size
      copyFrom (written.getD guard)
      return true
    -- What it does with them as they were given is the program's fault.
    | .error _ => return false
  if !owners.isEmpty then
    for owner in owners do copyFrom owner
    protectSiblings machine emu false
    return true
  if fault.operation != .write then
    -- None can be written, and this one can't be accessed, as of a machine that was kept so: they hold the same.
    protectSiblings machine emu false
    return true
  protect emu guard.start guard.size guard.protection
  for other in guards.filter together do protect emu other.start other.size ⟨false, false, false⟩
  pure true

/-- `madvise`, for what has a file behind it: `MADV_DONTNEED` leaves what the file has, and zeros elsewhere. A shared mapping has been
written back by now, so that for it nothing changes. The segments of a program and of a library aren't known as files here and get zeros. -/
private def serveAdvice (machine : Machine) (group address size advice : Nat) : IO SyscallAction := do
  let emu := machine.emu
  let pages := pageUp size
  let kernel ← machine.kernel.get
  let mappings := (kernel.process group).mappings.filter (·.overlaps address (address + pages))
  if advice != 4 || mappings.isEmpty then return .default
  if address % 4096 != 0 then return errorOf Errno.einval
  if !coversRange (← emu.regions.get) address (address + pages) then return errorOf Errno.enomem
  zapPages machine group address pages
  pure (.returnValue 0)

/-- Where the memory of a process ends, as `access_ok` has it: `TASK_SIZE_MAX` of x86-64, 48 bits of the other 64-bit targets, and all
of 32 bits. -/
private def userLimit (architecture : Architecture) : Nat :=
  if architecture.bits == 32 then 2 ^ 32 else if architecture matches .x86_64 then 0x7ffffffff000 else 2 ^ 48

/-- Whether `size` bytes that would be a process's own to write are more than the machine could ever give, as Linux's
`__vm_enough_memory` has it where it guesses, which is how it starts: more than all the memory and the swap that there is. What is
only read, or of a file that takes the writes, or asked for with `MAP_NORESERVE`, isn't counted, and is given whatever its size. -/
private def overcommitted (size : Nat) : Bool := size / 4096 > Abi.memory / 4096

/-- Whether `growth` more bytes of memory would be more than a process may have, as `may_expand_vm` has `RLIMIT_AS`: all that is mapped
in its space, and that. -/
private def addressSpaceFull (machine : Machine) (group growth : Nat) : IO Bool := do
  let limit := ((← machine.kernel.get).limitOf group 9).1
  if growth == 0 || limit ≥ 2 ^ 63 then return false
  let total := (← machine.emu.regions.get).foldl (· + ·.data.size) 0
  pure (total + growth > limit)

/-- `mremap`, of one mapping as Linux has it: what is the same protection in one piece, and the same file throughout or none. It shrinks
in place, grows in place if nothing is in the way, and otherwise moves if it may, which takes a second mapping of a shared one if the old size is 0,
and of `MREMAP_DONTUNMAP` leaves where it was mapped, without what was written there. -/
private def serveRemap (machine : Machine) (group old oldSize newSize flags target : Nat) : IO SyscallAction := do
  let emu := machine.emu
  let mayMove := flags &&& 1 != 0
  let fixed := flags &&& 2 != 0
  let keep := flags &&& 4 != 0
  let oldPages := pageUp oldSize
  let newPages := pageUp newSize
  if old % 4096 != 0 || newPages == 0 || flags ≥ 8 || (fixed && !mayMove) || (keep && (!mayMove || oldPages != newPages)) then
    return errorOf Errno.einval
  if fixed && (target % 4096 != 0 || (target < old + oldPages && old < target + newPages)) then
    return errorOf Errno.einval
  -- More than a process can have, as `mremap` has `TASK_SIZE`.
  if newSize > userLimit machine.architecture || (fixed && target > userLimit machine.architecture - newPages) then
    return errorOf Errno.einval
  -- What it adds, of all of it where the old stays as it is.
  if ← addressSpaceFull machine group (if keep || oldPages == 0 then newPages else newPages - oldPages) then
    return errorOf Errno.enomem
  let kernel ← machine.kernel.get
  let mappings := (kernel.process group).mappings
  let placed (start : Nat) (mapping : FileMapping) (offset : Nat) : FileMapping :=
    { mapping with start, size := newPages, offset }
  if oldPages == 0 then
    match mappings.find? (fun mapping => mapping.shared && mapping.overlaps old (old + 1)) with
    | some mapping =>
      if !mayMove then return errorOf Errno.einval
      let offset := mapping.offset + (old - mapping.start)
      let some region := lookupRegion (← emu.regions.get) old | return errorOf Errno.efault
      try
        let start ← placeZeros emu target fixed newPages (protectionBits region.protection)
        poke emu start (kernel.inodeBytes mapping.inode offset (kernel.inodeExtent mapping.inode offset newPages)) (known := true)
        machine.kernel.modify fun kernel => (kernel.dropMappings group start (start + newPages)).addMapping group (placed start mapping offset)
        return .returnValue start
      catch _ => return errorOf Errno.enomem
    | none => return errorOf Errno.einval
  let regions ← emu.regions.get
  if !coversRange regions old (old + min oldPages newPages) then return errorOf Errno.efault
  if !fixed && !keep && newPages ≤ oldPages then
    if newPages < oldPages then
      unmap emu (old + newPages) (oldPages - newPages)
      machine.kernel.modify (·.dropMappings group (old + newPages) (old + oldPages))
    return .returnValue old
  if !coversRange regions old (old + oldPages) then return errorOf Errno.efault
  let some first := lookupRegion regions old | return errorOf Errno.efault
  let touching := regions.filter fun region => region.address < old + oldPages && old < region.address + region.data.size
  if touching.any (·.protection != first.protection) then return errorOf Errno.efault
  -- What it grows by of memory that is the process's own to write is counted, as `mremap` has `VM_ACCOUNT`: more than the machine
  -- could ever give is refused.
  if newPages > oldPages && first.protection.writable && overcommitted (newPages - oldPages) then return errorOf Errno.enomem
  let behind := mappings.filter (·.overlaps old (old + oldPages))
  let mapping ← match behind with
    | [] => pure none
    | [mapping] =>
      if mapping.start ≤ old && old + oldPages ≤ mapping.start + mapping.size then pure (some mapping)
      else return errorOf Errno.efault
    | _ => return errorOf Errno.efault
  let offset := match mapping with
    | some mapping => mapping.offset + (old - mapping.start)
    | none => 0
  -- What it grows by: zeros, and of a file, what the file has of it, which is all that the host makes of it.
  let tail : ByteArray := if newPages ≤ oldPages then ByteArray.empty else
    match mapping with
    | some mapping => kernel.inodeBytes mapping.inode (offset + oldPages) (kernel.inodeExtent mapping.inode (offset + oldPages) (newPages - oldPages))
    | none => ByteArray.empty
  -- What was advised for a child goes with the pages, and stays where they were if they are kept there.
  let note (start : Nat) : IO Unit :=
    machine.kernel.modify fun kernel =>
      let advice := kernel.movedAdvice group old (min oldPages newPages) start
      let kernel := if keep then kernel else kernel.dropMappings group old (old + oldPages)
      let kernel := kernel.dropMappings group start (start + newPages)
      let process := kernel.process group
      let kernel := kernel.setProcess group { process with forkAdvice := advice ++ process.forkAdvice }
      match mapping with
      | some mapping => kernel.addMapping group (placed start mapping offset)
      | none => kernel
  let free := !regions.any fun region => region.address < old + newPages && old + oldPages < region.address + region.data.size
  try
    if !fixed && !keep && free then
      mapZeros emu (old + oldPages) (newPages - oldPages) first.protection
      poke emu (old + oldPages) tail (known := true)
      note old
      return .returnValue old
    if !mayMove then return errorOf Errno.enomem
    -- Zeros, and over them what was written of where it was, a piece at a time: what the host has of it is what it had.
    let start ← placeZeros emu target fixed newPages (protectionBits first.protection)
    let kept := min oldPages newPages
    for (at_, length) in ← piecesOf emu old kept 0 do
      poke emu (start + (at_ - old)) (← peek emu at_ length) (known := true)
    if newPages > oldPages then poke emu (start + oldPages) tail (known := true)
    -- What hears of copies hears of this one, as of `realloc`: what the bytes were goes with them, before where they were goes.
    for copied in ← emu.memoryCopied.get do copied old start (min oldPages newPages)
    -- Of `MREMAP_DONTUNMAP`, where it was stays mapped without its pages, as Linux has it since 5.13: zeros, or of a file, the file.
    if keep then
      clearMapped emu old oldPages
      if let some mapping := mapping then
        poke emu old (kernel.inodeBytes mapping.inode offset (kernel.inodeExtent mapping.inode offset oldPages)) (known := mapping.shared)
    else unmap emu old oldPages
    note start
    pure (.returnValue start)
  catch _ => pure (errorOf Errno.enomem)

/-- `brk`: it grows by mapping zeros, and what it gives back is gone, so that it is zeros if it grows again. What is left of a page
stays as it was, as in Linux. -/
private def serveBreak (machine : Machine) (group wanted : Nat) : IO SyscallAction := do
  let kernel ← machine.kernel.get
  let process := kernel.process group
  if wanted < process.breakStart then
    pure (.returnValue process.breakEnd)
  else
    let mappedTo := pageUp process.breakEnd
    let needed := pageUp wanted
    -- Past where the memory of a process ends, or by more than the machine has, it stays where it is.
    if needed > userLimit machine.architecture || overcommitted (needed - mappedTo) then return .returnValue process.breakEnd
    -- Nor past what `RLIMIT_DATA` lets its data be, as `check_data_rlimit` has it.
    if wanted - process.breakStart > (kernel.limitOf group 2).1 then return .returnValue process.breakEnd
    if ← addressSpaceFull machine group (needed - mappedTo) then return .returnValue process.breakEnd
    try
      if needed > mappedTo then
        mapZeros machine.emu mappedTo (needed - mappedTo) ⟨true, true, false⟩
      else if needed < mappedTo then
        unmap machine.emu needed (mappedTo - needed)
      machine.kernel.set (kernel.setProcess group { process with breakEnd := wanted })
      pure (.returnValue wanted)
    catch _ => pure (.returnValue process.breakEnd)

private def base (machine : Machine) (group directory : Nat) : IO (Result String) := do
  pure ((← machine.kernel.get).baseOf group directory (atCwd directory))

private def stackTop (architecture : Architecture) : Nat := if architecture.bits == 32 then 0x7fff0000 else 0x7ffffffff000

/-- `MAX_RW_COUNT`, which is as much as one read or write asks for: what asks for more asks for that. -/
private def maxCount : Nat := 0x7ffff000

/-- `UIO_MAXIOV`, the most pieces of `readv` and `writev`. -/
private def maxVectors : Nat := 1024

/-- Whether a descriptor is one that a call of reading or writing goes on with as far as its buffer, as `ksys_read` and its kin have it:
open, for that, and of `pread` and `pwrite` one that may be read or written where it says. -/
private def ioReady (kernel : Kernel) (group : Nat) (call : Call) (fd : Nat) : Bool :=
  match kernel.openFileOf group fd with
  | .ok (_, file) =>
    let reading := call == .read || call == .pread
    let positioned := call == .pread || call == .pwrite
    let seekable := match kernel.inodes.get? file.inode with
      | some { content := .file _, .. } | some { content := .device _, .. } | some { content := .directory, .. } => true
      | _ => false
    (if reading then Kernel.reads file.flags else Kernel.writes file.flags) && (!positioned || seekable)
  | .error _ => false

/-- The arguments of a call, as `vfs_read` and `vfs_write` have them: a buffer that isn't all in the memory of a process, without its
tag if the thread has asked for tags to be taken (`untag` is nothing otherwise), is `EFAULT`,
and what asks for more than `MAX_RW_COUNT` asks for that; and as `import_iovec` has them, more pieces than `UIO_MAXIOV` is `EINVAL`. -/
private def checkedArguments (architecture : Architecture) (untag : Nat → Nat) (ready : Nat → Bool) (call : Call) (args : List Nat) :
    Except Nat (List Nat) :=
  match call, args with
  | .read, fd :: address :: count :: rest | .write, fd :: address :: count :: rest
  | .pread, fd :: address :: count :: rest | .pwrite, fd :: address :: count :: rest =>
    -- Of an address without its tag, as `access_ok` has it of a process that tags them, after the descriptor, which `ready` says is
    -- one that the call may go on with: what it is wrong of comes first.
    if ready fd && untag address + count > userLimit architecture then .error Errno.efault
    else .ok (fd :: address :: min count maxCount :: rest)
  | .readv, _ :: _ :: count :: _ | .writev, _ :: _ :: count :: _ | .preadv, _ :: _ :: count :: _
  | .pwritev, _ :: _ :: count :: _ | .preadv2, _ :: _ :: count :: _ | .pwritev2, _ :: _ :: count :: _ =>
    if count > maxVectors then .error Errno.einval else .ok args
  | _, _ => .ok args
private def stackSize : Nat := 8 * 1024 * 1024

/-- What makes a generated file: what the kernel was given for it, or else its own. -/
private def generatorOf (kernel : Kernel) (name : String) : Option Generator :=
  (kernel.generators.get? name).or (Proc.builtin name)

/-- The name of what makes the file of a path, if it is generated, and the path without links. -/
private def generatedAt (kernel : Kernel) (base path : String) : Option (String × String) :=
  match kernel.resolve base path with
  | .ok (normal, some number) =>
    match kernel.inodes.get? number with
    | some { content := .generated name, .. } => some (name, normal)
    | _ => none
  | _ => none

/-- The process that a path is about, if it is under `/proc/PID`, and otherwise the one that asks. -/
private def processOfPath (path : String) (group : Nat) : Nat :=
  match path.splitOn "/" with
  | "" :: "proc" :: number :: _ => number.toNat?.getD group
  | _ => group

/-- The thread of a path of `/proc/PID/task/TID`, if it is one. -/
private def threadOfPath (path : String) : Option Nat :=
  match path.splitOn "/" with
  | "" :: "proc" :: _ :: "task" :: number :: _ => number.toNat?
  | _ => none

/-- The name of a thread of a process, as `PR_GET_NAME` and its `comm` have it. -/
private def threadName (process : Process) (tid : Nat) : String :=
  (process.threadNames.lookup tid).getD process.name

/-- The processes that are running. -/
private def liveProcesses (emu : Emu) : IO (List Nat) := do
  pure (((← emu.taskTable.get).tasks.filter fun task => task.status.isNone && task.tid == task.group).map (·.tid))

/-- What `/proc/PID/maps` calls the file of a mapping of a process: its path as the process sees it, or what it was before it was
removed, or `/SYSV` and the key of a segment of System V, or else what is behind memory that is shared and anonymous, as Linux has it.
`paths` has the paths of the inodes that have one. -/
private def mappedName (kernel : Kernel) (group : Nat) (paths : Std.HashMap Nat String) (inode : Nat) : String :=
  match paths.get? inode with
  | some path => kernel.shownPath group path
  | none =>
    match kernel.ipc.segments.find? (·.inode == inode), kernel.inodes.get? inode with
    | some segment, _ =>
      let key := String.ofList (Nat.toDigits 16 (segment.perm.key % 2 ^ 32))
      s!"/SYSV{String.ofList (List.replicate (8 - key.length) '0')}{key} (deleted)"
    | none, some { details := { name, .. }, .. } => if name.isEmpty then "/dev/zero (deleted)" else name
    | none, none => "/dev/zero (deleted)"

/-- Whether a path is of `/proc`. -/
private def inProc (path : String) : Bool := path == "/proc" || path.startsWith "/proc/"

/-- A path that a process gives, as a path of the tree from `/`: one that isn't from `/` is from its working directory. -/
private def treePath (kernel : Kernel) (group : Nat) (path : String) : String :=
  let (base, relative) := kernel.pathIn group (kernel.cwdOf group) path
  if relative.startsWith "/" then relative else base ++ "/" ++ relative

/-- What a program loaded at `base` has of its file `inode`, as Linux maps it: of each segment, the pages that the file has, privately,
of which what a segment after it covers is that one's. -/
private def segmentMappings (program : Elf.Program) (base inode : Nat) : List FileMapping :=
  (program.segments.toArray.qsort fun left right => left.address < right.address).foldl (init := []) fun mappings segment =>
    let first := base + segment.address
    let start := pageDown first
    let stop := pageUp (first + segment.fileSize)
    if segment.fileSize == 0 || segment.memorySize == 0 then mappings
    else mappings.flatMap (·.without start stop) ++
      [{ start, size := stop - start, inode, offset := segment.offset - (first - start), shared := false, mayWrite := false }]

/-- What of the memory of a process its program and its interpreter are behind, as `loadProgram` put them, which `/proc/PID/maps`
shows as mappings of those files: where each went is in its auxiliary vector, the program by `AT_ENTRY` and the interpreter at
`AT_BASE`. -/
private def programMappings (kernel : Kernel) (group : Nat) (process : Process) : List FileMapping :=
  let loaded (path : String) : Option (Nat × Elf.Program) :=
    match kernel.resolve "/" path with
    | .ok (_, some inode) =>
      match kernel.inodes.get? inode with
      | some { content := .file data, .. } => (Elf.parse data).toOption.map (inode, ·)
      | _ => none
    | _ => none
  let auxiliary (type : Nat) : Option Nat :=
    let rec find : List Nat → Option Nat
      | key :: value :: rest => if key == type then some value else find rest
      | _ => none
    find process.auxiliary
  match loaded process.program, auxiliary 9 with
  | some (inode, program), some entry =>
    let interpreter := match program.interpreter.bind (loaded <| treePath kernel group ·), auxiliary 7 with
      | some (inode, interpreter), some base => segmentMappings interpreter base inode
      | _, _ => []
    segmentMappings program (entry - program.entry) inode ++ interpreter
  | _, _ => []

/-- What a generated file sees of a process. -/
private def viewOf (machine : Machine) (emu : Emu) (group : Nat) : IO ProcessView := do
  let kernel ← machine.kernel.get
  let process := kernel.process group
  let table ← emu.taskTable.get
  let ownSpace := table.spaceOf (← thread emu)
  let space := table.spaceOf group
  let regions ← if space == ownSpace then emu.regions.get
    else pure ((← emu.parkedRegions.get).getD space [])
  let architecture := machine.architecture
  let stackStart := stackTop architecture - stackSize
  -- Its mappings, with those of its program that nothing was mapped over, and the paths of their files, found in one pass.
  let mappings := programMappings kernel group process |>.flatMap (fun segment =>
    process.mappings.foldl (fun pieces mapping => pieces.flatMap (·.without mapping.start (mapping.start + mapping.size))) [segment])
  let mappings := mappings ++ process.mappings
  let inodes := mappings.map (·.inode)
  let paths := kernel.paths.fold (init := ({} : Std.HashMap Nat String)) fun found path number =>
    if inodes.contains number && path.startsWith "/" && !found.contains number then found.insert number path else found
  let mappings := mappings.map fun mapping => (mapping, mappedName kernel group paths mapping.inode)
  pure {
    pid := group
    parent := match table.find? group with
      | some task => task.parent
      | none => 0
    threads := (table.tasks.filter fun task => task.group == group && task.status.isNone).map (·.tid)
    command := process.command
    environment := process.environment
    program := process.program
    name := process.name
    auxiliary := process.auxiliary
    big := architecture.big
    cwd := kernel.shownPath group process.cwd.path
    mounts := kernel.mounts.map fun mount => (kernel.shownPath group mount.target, mount.fstype, mount.device, mount.flags)
    -- Each region, in pieces where what has a file behind it starts and ends.
    ranges := regions.flatMap fun region =>
      let stop := region.address + region.data.size
      let inside := mappings.filter (·.1.overlaps region.address stop)
      let bounds := (region.address :: (inside.flatMap fun (mapping, _) => [mapping.start, mapping.start + mapping.size]).filter
        (fun at_ => region.address < at_ && at_ < stop) ++ [stop]).mergeSort.eraseDups
      (bounds.zip bounds.tail).map fun (first, last) =>
        let writeOnly := process.guards.any fun guard =>
          guard.bits == Guard.writeOnly && guard.start ≤ first && first < guard.start + guard.size
        let range : MappedRange := { start := first, size := last - first, readable := region.protection.readable && !writeOnly
                                     writable := region.protection.writable, executable := region.protection.executable }
        match inside.find? (·.1.overlaps first (first + 1)) with
        | some (mapping, path) =>
          { range with shared := mapping.shared, offset := mapping.offset + (first - mapping.start), inode := mapping.inode, path }
        | none => range
    breakStart := process.breakStart
    umask := process.umask
    breakEnd := process.breakEnd
    stackStart
    tracer := ← do
      match ← machine.ptrace.tracerOf group with
      | some tid => pure ((table.find? tid).map (·.group) |>.getD tid)
      | none => pure 0
    -- Below the bytes of `AT_RANDOM`, as `mapStack` has it: the count of the arguments, their addresses and those of the environment,
    -- each list with its end, and the auxiliary vector with its own, aligned to 16.
    startStack :=
      let word := architecture.bits / 8
      let pairs := (List.range (process.auxiliary.length / 2)).map fun index =>
        (process.auxiliary.getD (2 * index) 0, process.auxiliary.getD (2 * index + 1) 0)
      match pairs.lookup 25 with
      | some random =>
        let cells := 3 + process.command.length + process.environment.length + process.auxiliary.length + 2
        (random - word * cells) / 16 * 16
      | none => 0
    credentials := process.credentials
    pgid := kernel.pgidOf group
    sid := kernel.sidOf group
    stack := kernel.limitOf group 3
    files := kernel.limitOf group 7
    descriptors := process.descriptors.toList.filterMap fun (fd, entry) =>
      -- Its flags as the guest has them, with `O_CLOEXEC` of the descriptor, as `/proc/PID/fdinfo` says them.
      (kernel.openFiles.get? entry.openFile).map fun file =>
        (fd, file.offset, architecture.guestFlags (file.flags ||| (if entry.closeOnExec then Kernel.oCloexec else 0)))
    bits := architecture.bits
    machine := architecture.name
    clock := kernel.clock
    uptime := kernel.clock - bootClock
    processes := ← liveProcesses emu }

/-- A number of `size` bytes of a structure, in the order of the guest. -/
private def numberAt (bytes : ByteArray) (offset size : Nat) (big : Bool) : Nat :=
  (List.range size).foldl (fun value index =>
    let at_ := if big then offset + size - 1 - index else offset + index
    value + bytes[at_]!.toNat * 256 ^ index) 0

/-- A call that has to wait for what happens to the inode `number`: it stops here and runs again when something changes, with its
registers as they were, as a read of a pipe does, having `written` bytes of a write already, or, of a signal, as `Timers.interrupted`
says. -/
private def waitOn (machine : Machine) (emu : Emu) (number : Nat) (written : Nat := 0) : IO SyscallAction :=
  machine.timers.waitUntil emu (pipeSpace + number) 0 none true written

/-- `SIGPIPE`, which is 13 on every architecture, to the thread that runs, of a write to what nothing reads any more. -/
private def sendBrokenPipe (machine : Machine) (emu : Emu) (group : Nat) : IO Unit := do
  let kernel ← machine.kernel.get
  machine.signals.send emu (some (← thread emu)) group ⟨13, 0, .sent group (kernel.process group).credentials.uid 0⟩

/-- A write of `count` bytes to the pipe `number` of a descriptor, which `bytesAt` gives from an offset in them, as Linux has it: of at
most `PIPE_BUF` bytes, all of them at once, and of more, as much as there is room for; while there is no room for that, `EAGAIN`, or,
if it may `wait`, a wait for a reader, after which it goes on with what is left until all of it is written. What it wrote before it
waited the site of its call has (`Timers.written`), which it gives if a signal ends the wait, or with `SIGPIPE` if the readers go.
Linux keeps a pipe in pages, so that what it has room for is a little less, at times, than here. -/
private def writePipe (machine : Machine) (emu : Emu) (group fd number count : Nat) (bytesAt : Nat → Nat → IO ByteArray) (wait : Bool) :
    IO SyscallAction := do
  let kernel ← machine.kernel.get
  if let some errno := kernel.writeError group fd count then return errorOf errno
  -- Of nothing, nothing, with or without a reader, as `pipe_write` has it.
  if count == 0 then return .returnValue 0
  let done ← if wait then machine.timers.written emu else pure 0
  let finished (value : Nat) : IO SyscallAction := do
    if wait then machine.timers.finish (← thread emu)
    pure (.returnValue value)
  let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
  if !kernel.pipeHeld number live false then
    if done == 0 then return errorOf Errno.epipe
    sendBrokenPipe machine emu group
    return ← finished done
  let room := kernel.pipeRoom number
  let piece := min room (count - done)
  if piece < count - done && (piece == 0 || count ≤ Kernel.pipeBuf) then
    return ← if wait then waitOn machine emu number done else pure (errorOf Errno.eagain)
  match ← (bytesAt done piece).toBaseIO with
  | .error _ => if done > 0 then finished done else pure (errorOf Errno.efault)
  | .ok bytes =>
    machine.kernel.modify (·.writeKnown group fd bytes)
    wakePipeReaders emu
    if done + piece == count || !wait then finished (done + piece) else waitOn machine emu number (done + piece)

/-- `writev` to the pipe `number` of a descriptor, of what its `count` pieces at `address` have together, as `writePipe` has it. -/
private def writeVectorPipe (machine : Machine) (emu : Emu) (group fd number address count : Nat) (wait : Bool) : IO SyscallAction := do
  let word := machine.architecture.bits / 8
  match ← (read emu address (2 * word * count)).toBaseIO with
  | .error _ => pure (errorOf Errno.efault)
  | .ok entries =>
    let field (offset : Nat) : Nat := numberAt entries offset word machine.architecture.big
    let pieces := (List.range count).map fun index => (field (2 * word * index), field (2 * word * index + word))
    -- A length below 0 is `EINVAL`, before anything is done, as `import_iovec` has it.
    if pieces.any (·.2 ≥ 2 ^ (8 * word - 1)) then return errorOf Errno.einval
    let total := min maxCount (pieces.foldl (· + ·.2) 0)
    -- Of the pieces, only what goes into the pipe, when it goes: as much as a guest says it has isn't made of the host at once.
    let bytesAt (at_ size : Nat) : IO ByteArray := do
      let mut out := ByteArray.empty
      let mut start := 0
      for (place, length) in pieces do
        let first := max at_ start
        let last := min (at_ + size) (start + length)
        if first < last then out := out ++ (← read emu (place + (first - start)) (last - first))
        start := start + length
        if start ≥ at_ + size then break
      pure out
    writePipe machine emu group fd number total bytesAt wait

/-- A write that finds that nothing reads what it writes to any more, a pipe or a socket of a stream, sends `SIGPIPE` to the thread that
made it, as `write`, `writev`, `pwritev2` at the offset of the file, `send`, `sendto`, `sendmsg`,
`sendfile`, `splice` and `tee` do that give `EPIPE`, unless a send says `MSG_NOSIGNAL`. The call gives `EPIPE` all the same, if the
signal doesn't end the process. -/
private def brokenPipe (machine : Machine) (emu : Emu) (group : Nat) (call : Call) (args : List Nat) (action : SyscallAction) :
    IO Unit := do
  let .returnValue value := action | return
  if value != 2 ^ 64 - Errno.epipe then return
  let arg (index : Nat) : Nat := args.getD index 0
  let quiet (flags : Nat) : Bool := flags &&& 0x4000 != 0
  let fd? := match call with
    | .write | .writev | .pwritev2 | .sendfile | .sendfile64 => some (arg 0)
    | .send | .sendto => if quiet (arg 3) then none else some (arg 0)
    | .sendmsg => if quiet (arg 2) then none else some (arg 0)
    | .splice => some (arg 2)
    | .tee => some (arg 1)
    | _ => none
  let some fd := fd? | return
  let kernel ← machine.kernel.get
  -- A socket of datagrams or of packets that can't send says so and no more.
  if let .ok (_, socket) := kernel.socketOf group fd then
    if socket.type != 1 then return
  sendBrokenPipe machine emu group

/-- A process that writes, or makes a file grow, past its `RLIMIT_FSIZE` is sent `SIGXFSZ` with the `EFBIG` it gets, as
`generic_write_check_limits` and `inode_newsize_ok` send it. -/
private def fileTooBig (machine : Machine) (emu : Emu) (group : Nat) (call : Call) (action : SyscallAction) : IO Unit := do
  let .returnValue value := action | return
  if value != 2 ^ 64 - Errno.efbig then return
  if ![Call.write, .pwrite, .writev, .pwritev, .pwritev2, .truncate, .truncate64, .ftruncate, .ftruncate64, .fallocate].contains call then
    return
  let kernel ← machine.kernel.get
  if (kernel.limitOf group 1).1 ≥ 2 ^ 63 then return
  let signal := match machine.architecture with | .mips .. => 31 | _ => 25
  machine.signals.send emu (some (← thread emu)) group ⟨signal, 0, .sent group (kernel.process group).credentials.uid 0⟩

/-- The name in a `struct sockaddr` of `size` bytes. Of `sockaddr_un`, a path, to its first zero, or a name of its own, which starts with
one, and of `sockaddr_in` and `sockaddr_in6`, an address of the Internet as a socket has it as its name. -/
private def socketName (emu : Emu) (big : Bool) (address size : Nat) : IO (Result String) := do
  if size < 3 || size > 128 then return .error Errno.einval
  match ← (read emu address size).toBaseIO with
  | .error _ => pure (.error Errno.efault)
  | .ok bytes =>
    let family := numberAt bytes 0 2 big
    -- The port and the address are in the order of the network.
    if family == 2 then
      if size < 16 then return .error Errno.einval
      return .ok ({ family, address := numberAt bytes 4 4 true, port := numberAt bytes 2 2 true } : Kernel.Endpoint).name
    if family == 10 then
      if size < 24 then return .error Errno.einval
      return .ok ({ family, address := numberAt bytes 8 16 true, port := numberAt bytes 2 2 true } : Kernel.Endpoint).name
    if family != 1 then return .error Errno.eafnosupport
    if size > 110 then return .error Errno.einval
    let path := bytes.extract 2 size
    let text := if path[0]! == 0 then path else path.extract 0 ((path.data.findIdx? (· == 0)).getD path.size)
    match String.fromUTF8? text with
    | some name => pure (.ok name)
    | none => pure (.error Errno.einval)

/-- A `struct sockaddr_in` or `sockaddr_in6`. -/
private def endpointBytes (big : Bool) (endpoint : Kernel.Endpoint) : ByteArray :=
  let head := Abi.field big 2 endpoint.family ++ Abi.field true 2 endpoint.port
  if endpoint.family == 2 then head ++ Abi.field true 4 endpoint.address ++ Abi.bytesOf 8 0
  else head ++ Abi.bytesOf 4 0 ++ Abi.field true 16 endpoint.address ++ Abi.bytesOf 4 0

/-- A `struct sockaddr` of a name of a socket of `family`. One of the Unix domain without a name is `AF_UNIX` alone, and one of the
Internet is at any address and port 0. -/
private def nameBytes (big : Bool) (family : Nat) (name : Option String) : ByteArray :=
  match name.bind Kernel.Endpoint.ofName?, name with
  | some endpoint, _ => endpointBytes big endpoint
  | none, some name =>
    let head := Abi.field big 2 1
    if Kernel.abstractName name then head ++ name.toUTF8 else head ++ name.toUTF8 ++ ByteArray.mk #[0]
  | none, none => if family == 1 then Abi.field big 2 1 else endpointBytes big { family, address := 0, port := 0 }

/-- Gives a name where the guest asked for one, as much of it as its length has room for, and how long it is. -/
private def giveName (emu : Emu) (big : Bool) (address lengthAddress : Nat) (bytes : ByteArray) : IO Bool := do
  if address == 0 || lengthAddress == 0 then return true
  match ← (read emu lengthAddress 4).toBaseIO with
  | .error _ => pure false
  | .ok length =>
    try
      writeGuest emu address (bytes.extract 0 (numberAt length 0 4 big))
      writeGuest emu lengthAddress (Abi.field big 4 bytes.size)
      pure true
    catch _ => pure false

/-- The calls of sockets, and `read` and `write` of one. -/
private def socketCall (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO SyscallAction := do
  let architecture := machine.architecture
  let wide := architecture.bits
  let wordSize := wide / 8
  let big := architecture.big
  let mips := match architecture with | .mips .. => true | _ => false
  let arg (index : Nat) : Nat := args.getD index 0
  let group := (← currentTask emu).group
  let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
  let kernel ← machine.kernel.get
  let alive (number : Nat) : Bool := kernel.socketAlive number live
  let cwd := kernel.cwdOf group
  -- MIPS has the numbers of streams and datagrams the other way round, and `SOL_SOCKET` and the options elsewhere.
  let typeOf (type : Nat) : Nat := if mips && (type == 1 || type == 2) then 3 - type else type
  let solSocket := if mips then 0xffff else 1
  let option (generic mipsValue : Nat) : Nat := if mips then mipsValue else generic
  -- `SO_RCVTIMEO` and `SO_SNDTIMEO`, as their old numbers, of `struct timeval` of words.
  let timeouts : Nat × Nat := match architecture with
    | .mips .. => (0x1006, 0x1005)
    | .powerpc .. => (18, 19)
    | _ => (20, 21)
  let peerCred := match architecture with
    | .mips .. => 18
    | .powerpc .. => 21
    | _ => 17
  -- `SO_PASSCRED`.
  let passCred := match architecture with
    | .mips .. => 17
    | .powerpc .. => 20
    | _ => 16
  let word (bytes : ByteArray) (offset : Nat) : Nat := numberAt bytes offset wordSize big
  let int (bytes : ByteArray) (offset : Nat) : Nat := numberAt bytes offset 4 big
  -- The address and length of each `struct iovec`.
  let vectorsAt (address count : Nat) : IO (List (Nat × Nat)) := do
    let bytes ← read emu address (2 * wordSize * count)
    pure ((List.range count).map fun index => (word bytes (2 * wordSize * index), word bytes (2 * wordSize * index + wordSize)))
  let gather (pieces : List (Nat × Nat)) : IO ByteArray :=
    pieces.foldlM (init := ByteArray.empty) fun out (address, size) => do pure (out ++ (← read emu address size))
  let scatter (pieces : List (Nat × Nat)) (data : ByteArray) : IO Unit := do
    let mut done := 0
    for (address, size) in pieces do
      if done ≥ data.size then break
      let piece := data.extract done (done + size)
      writeGuest emu address piece
      done := done + piece.size
  let target (address size : Nat) : IO (Result (Option String)) := do
    if address == 0 then return .ok none
    pure ((← socketName emu big address size).map some)
  let socket : Option Socket := (kernel.socketOf group (arg 0)).toOption.map (·.2)
  let family := (socket.map (·.family)).getD 1
  let sendFrom (fd : Nat) (pieces : List (Nat × Nat)) (rights : List Nat) (to : Option String) : IO SyscallAction := do
    match ← (gather pieces).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok data =>
      -- A socket of datagrams with `SO_PASSCRED` and no name gets one as it sends, as `unix_dgram_sendmsg` has it.
      let kernel := match kernel.socketOf group fd with
        | .ok (number, sending) =>
          if sending.family == 1 && sending.type == 2 && sending.passCredentials && sending.name.isNone then kernel.autobindUnix number alive
          else kernel
        | .error _ => kernel
      let sent : Result (Kernel × Nat) := do
        if family == 1 then
          let to ← match to with
            | some name => if (Kernel.Endpoint.ofName? name).isSome then .error Errno.eafnosupport else (kernel.socketNamed cwd name).map some
            | none => .ok none
          kernel.send group fd { data, rights } to alive
        else if !rights.isEmpty then .error Errno.einval
        -- A stream of the Internet goes where it is connected, whatever a send says.
        else if (socket.map (·.type)) == some 1 then kernel.send group fd { data } none alive
        else
          let endpoint ← match to with
            | some name => match Kernel.Endpoint.ofName? name with
              | some endpoint => .ok (some endpoint)
              | none => .error Errno.eafnosupport
            | none => .ok none
          kernel.sendDatagram group fd data endpoint alive
      match sent with
      | .error errno =>
        -- A socket of datagrams that finds its peer gone has none from then, as `unix_dgram_sendmsg` leaves it.
        if errno == Errno.econnrefused && family == 1 && to.isNone then machine.kernel.set (kernel.disconnectDead group fd alive)
        pure (errorOf errno)
      | .ok (next, count) =>
        machine.kernel.set next
        wakePipeReaders emu
        pure (.returnValue count)
  -- Who sent what was received, which a stream of the Internet doesn't say.
  let senderBytes (received : Kernel.Received) : ByteArray :=
    if received.sender.isNone || (family != 1 && (socket.map (·.type)) == some 1) then ByteArray.empty
    else nameBytes big family received.sender
  -- What is received, for the calls that take it, or that it has to wait.
  let receiveInto (fd : Nat) (pieces : List (Nat × Nat)) (flags : Nat) (finish : Kernel.Received → IO SyscallAction) :
      IO SyscallAction := do
    let total := pieces.foldl (fun total piece => total + piece.2) 0
    if let some next := kernel.tellReset group fd alive then
      machine.kernel.set next
      return errorOf Errno.econnreset
    let mayWait := flags &&& 0x40 == 0 && !kernel.nonblocking group fd
    match kernel.receive group fd total (flags &&& 2 != 0) alive (all := flags &&& 0x100 != 0 && mayWait) with
    | .error errno => pure (errorOf errno)
    | .ok (_, none) =>
      if !mayWait then pure (errorOf Errno.eagain)
      else
        match kernel.socketOf group fd with
        | .ok (number, socket) =>
          if socket.receiveTimeout == 0 then waitOn machine emu number
          else
            -- Of `SO_RCVTIMEO`: until then, from when the call began, after which `EAGAIN`, as Linux has it.
            let tid ← thread emu
            let now ← machine.timers.now
            let due ← machine.timers.deadlineOf tid (pure (now + socket.receiveTimeout))
            if due ≤ now then
              machine.timers.finish tid
              -- What `MSG_WAITALL` waited for more of is what there is by then, if anything is.
              match kernel.receive group fd total (flags &&& 2 != 0) alive with
              | .ok (next, some received) =>
                machine.kernel.set next
                wakePipeReaders emu
                match ← (scatter pieces received.data).toBaseIO with
                | .error _ => pure (errorOf Errno.efault)
                | .ok () => finish received
              | _ => pure (errorOf Errno.eagain)
            -- A signal ends it with `EINTR`, even of a handler of `SA_RESTART`, as `sock_intr_errno` has it of one with a time.
            else machine.timers.waitUntil emu (pipeSpace + number) 0 (some due) false
        | .error errno => pure (errorOf errno)
    | .ok (next, some received) =>
      machine.kernel.set next
      wakePipeReaders emu
      match ← (scatter pieces received.data).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok () => finish received
  -- Of the Unix domain, any of its types. Of the Internet, TCP as a stream and UDP as datagrams.
  let checkType (type protocol : Nat) (action : Nat → Nat → IO SyscallAction) : IO SyscallAction := do
    let kind := typeOf (type &&& 0xf)
    let domain := arg 0
    if ![1, 2, 10].contains domain then pure (errorOf Errno.eafnosupport)
    else if domain == 1 && ![1, 2, 5].contains kind then pure (errorOf Errno.esocktnosupport)
    else if domain == 1 && protocol > 1 then pure (errorOf Errno.eprotonosupport)
    else if domain != 1 && kind != 1 && kind != 2 then pure (errorOf Errno.esocktnosupport)
    else if domain != 1 && protocol != 0 && protocol != (if kind == 1 then 6 else 17) then pure (errorOf Errno.eprotonosupport)
    else action kind (architecture.openFlags (type - (type &&& 0xf)))
  match call with
  | .socket => checkType (arg 1) (arg 2) fun kind flags => do
    let (next, fd) := kernel.socket group kind flags (arg 0)
    machine.kernel.set next
    pure (.returnValue fd)
  | .socketpair =>
    if arg 0 != 1 && [2, 10].contains (arg 0) then pure (errorOf Errno.eopnotsupp) else
    checkType (arg 1) (arg 2) fun kind flags => do
    let (next, one, other) := kernel.socketPair group kind flags
    match ← (writeGuest emu (arg 3) (Abi.field big 4 one ++ Abi.field big 4 other)).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok () =>
      machine.kernel.set next
      pure (.returnValue 0)
  | .bind =>
    -- Of the Unix domain, a name of the size of its family alone asks for a name to be made, as `unix_bind` has it.
    let familyOnly ← if family == 1 && arg 2 % 2 ^ 32 == 2 then do
        pure ((← (read emu (arg 1) 2).toBaseIO).toOption.map fun bytes => numberAt bytes 0 2 big)
      else pure none
    if familyOnly == some 1 then
      return ← match kernel.socketOf group (arg 0) with
        | .error errno => pure (errorOf errno)
        | .ok (number, _) => do
          machine.kernel.set (kernel.autobindUnix number alive)
          pure (.returnValue 0)
    match ← socketName emu big (arg 1) (arg 2) with
    | .error errno => pure (errorOf errno)
    | .ok name =>
      match Kernel.Endpoint.ofName? name with
      | some endpoint => apply machine (·.bindInet group (arg 0) endpoint alive)
      | none => if family != 1 then pure (errorOf Errno.eafnosupport) else apply machine (·.bind group (arg 0) cwd name alive)
  | .listen =>
    -- Its backlog is unsigned, and no more than `somaxconn`.
    let backlog := min (arg 1 % 2 ^ 32) 4096
    if family == 1 then apply machine (·.listen group (arg 0) backlog) else apply machine (·.listenInet group (arg 0) alive backlog)
  | .connect =>
    match ← target (arg 1) (arg 2) with
    | .error errno => pure (errorOf errno)
    | .ok none => pure (errorOf Errno.einval)
    | .ok (some name) =>
      let action ← match Kernel.Endpoint.ofName? name with
        | some endpoint => apply machine (·.connectInet group (arg 0) endpoint alive)
        | none =>
          if family != 1 then pure (errorOf Errno.eafnosupport)
          else match kernel.socketNamed cwd name with
            | .error errno => pure (errorOf errno)
            | .ok to =>
              -- A listener that has as many waiting as it takes: `EAGAIN` of a socket that doesn't wait, and the others wait for one
              -- to be accepted, as `unix_stream_connect` has it.
              let waitsFor := (socket.map (·.type != 2)).getD false && (kernel.socketAt to).any (·.listening) && alive to &&
                kernel.backlogFull to
              if waitsFor then
                return ← if kernel.nonblocking group (arg 0) then pure (errorOf Errno.eagain) else waitOn machine emu to
              -- One with `SO_PASSCRED` and no name gets one, as `unix_stream_connect` and `unix_dgram_connect` have it.
              let named := match kernel.socketOf group (arg 0) with
                | .ok (number, connecting) =>
                  if connecting.passCredentials && connecting.name.isNone then kernel.autobindUnix number alive else kernel
                | .error _ => kernel
              machine.kernel.set named
              apply machine (·.connect group (arg 0) to alive)
      wakePipeReaders emu
      pure action
  | .accept | .accept4 =>
    -- Of the flags, only `SOCK_CLOEXEC` and `SOCK_NONBLOCK`, which is `O_NONBLOCK` of each, before the socket is looked at.
    let nonblocking := match architecture with | .mips .. => 0x80 | _ => 0x800
    if call == .accept4 && arg 3 % 2 ^ 32 &&& (2 ^ 32 - 1 - (0x80000 ||| nonblocking)) != 0 then return errorOf Errno.einval
    let flags := if call == .accept4 then architecture.openFlags (arg 3) else 0
    match kernel.accept group (arg 0) flags with
    | .error errno => pure (errorOf errno)
    | .ok (_, none) =>
      if kernel.nonblocking group (arg 0) then pure (errorOf Errno.eagain)
      else
        match kernel.socketOf group (arg 0) with
        | .ok (number, _) => waitOn machine emu number
        | .error errno => pure (errorOf errno)
    | .ok (next, some (fd, server)) =>
      machine.kernel.set next
      -- What waits to connect has room.
      wakePipeReaders emu
      let client := (next.socketAt server).bind (·.peer) |>.bind next.socketAt
      if ← giveName emu big (arg 1) (arg 2) (nameBytes big family (client.bind (·.name))) then pure (.returnValue fd)
      else pure (errorOf Errno.efault)
  | .getsockname =>
    match kernel.socketOf group (arg 0) with
    | .error errno => pure (errorOf errno)
    | .ok (_, socket) =>
      if ← giveName emu big (arg 1) (arg 2) (nameBytes big socket.family socket.name) then pure (.returnValue 0) else pure (errorOf Errno.efault)
  | .getpeername =>
    match kernel.peerName group (arg 0) with
    | .error errno => pure (errorOf errno)
    | .ok name => if ← giveName emu big (arg 1) (arg 2) (nameBytes big family name) then pure (.returnValue 0) else pure (errorOf Errno.efault)
  | .send | .write => sendFrom (arg 0) [(arg 1, arg 2)] [] none
  | .writev =>
    match ← (vectorsAt (arg 1) (arg 2)).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok pieces => sendFrom (arg 0) pieces [] none
  | .sendto =>
    match ← target (arg 4) (arg 5) with
    | .error errno => pure (errorOf errno)
    | .ok to => sendFrom (arg 0) [(arg 1, arg 2)] [] to
  | .sendmsg =>
    match ← (read emu (arg 1) (7 * wordSize)).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok header =>
      let some pieces ← (vectorsAt (word header (2 * wordSize)) (word header (3 * wordSize))).toBaseIO |>.map (·.toOption)
        | pure (errorOf Errno.efault)
      match ← target (word header 0) (int header wordSize) with
      | .error errno => pure (errorOf errno)
      | .ok to =>
        -- The descriptors that `SCM_RIGHTS` hands over.
        let control := word header (4 * wordSize)
        let controlSize := word header (5 * wordSize)
        let headerSize := wordSize + 8
        let some bytes ← (if control == 0 then pure ByteArray.empty else read emu control controlSize).toBaseIO |>.map (·.toOption)
          | pure (errorOf Errno.efault)
        let mut at_ := 0
        let mut fds : List Nat := []
        while at_ + headerSize ≤ bytes.size do
          let length := word bytes at_
          if length < headerSize then break
          if int bytes (at_ + wordSize) == solSocket && int bytes (at_ + wordSize + 4) == 1 then
            fds := fds ++ (List.range ((length - headerSize) / 4)).map fun index => int bytes (at_ + headerSize + 4 * index)
          at_ := at_ + (length + wordSize - 1) / wordSize * wordSize
        match kernel.rightsOf group fds with
        | .error errno => pure (errorOf errno)
        | .ok rights => sendFrom (arg 0) pieces rights to
  | .recv | .read => receiveInto (arg 0) [(arg 1, arg 2)] (if call == .recv then arg 3 else 0) fun received => pure (.returnValue received.data.size)
  | .readv =>
    match ← (vectorsAt (arg 1) (arg 2)).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok pieces => receiveInto (arg 0) pieces 0 fun received => pure (.returnValue received.data.size)
  | .recvfrom =>
    receiveInto (arg 0) [(arg 1, arg 2)] (arg 3) fun received => do
      if arg 4 != 0 && arg 5 != 0 then
        let given := senderBytes received
        unless ← giveName emu big (arg 4) (arg 5) given do return errorOf Errno.efault
      pure (.returnValue (if arg 3 &&& 0x20 != 0 then received.size else received.data.size))
  | .recvmsg =>
    match ← (read emu (arg 1) (7 * wordSize)).toBaseIO with
    | .error _ => pure (errorOf Errno.efault)
    | .ok header =>
      let some pieces ← (vectorsAt (word header (2 * wordSize)) (word header (3 * wordSize))).toBaseIO |>.map (·.toOption)
        | pure (errorOf Errno.efault)
      receiveInto (arg 0) pieces (arg 2) fun received => do
        let mut flags := if received.size > received.data.size then 0x20 else 0
        -- Who sent it.
        let nameAddress := word header 0
        let given := senderBytes received
        let nameLength := if nameAddress == 0 then 0 else min (int header wordSize) given.size
        if nameAddress != 0 then writeGuest emu nameAddress (given.extract 0 nameLength)
        writeGuest emu (arg 1 + wordSize) (Abi.field big 4 (if nameAddress == 0 then 0 else given.size))
        -- The descriptors that came, as many as there is room for, and the others are closed.
        let control := word header (4 * wordSize)
        let room := if control == 0 then 0 else word header (5 * wordSize)
        let headerSize := wordSize + 8
        let aligned (size : Nat) : Nat := (size + wordSize - 1) / wordSize * wordSize
        -- Who sent it, of a socket with `SO_PASSCRED`, as `SCM_CREDENTIALS`: a process, a user and a group, or of what was sent
        -- before either end asked, no process and nobody. It comes first, as `scm_recv` has it, if there is room for it.
        let asks := (socket.map (·.passCredentials)).getD false && family == 1
        let (pid, uid, gid) := received.credentials.getD (0, 65534, 65534)
        let credentials := if !asks then ByteArray.empty else
          Abi.field big wordSize (headerSize + 12) ++ Abi.field big 4 solSocket ++ Abi.field big 4 2 ++ Abi.field big 4 pid ++
            Abi.field big 4 uid ++ Abi.field big 4 gid
        let credentials := if credentials.size ≤ room then credentials else ByteArray.empty
        if asks && credentials.isEmpty then flags := flags ||| 8
        let before := aligned credentials.size
        let room := room - min room before
        let fit := if room < headerSize then 0 else min received.rights.length ((room - headerSize) / 4)
        if fit < received.rights.length then flags := flags ||| 8
        let (next, fds) := (← machine.kernel.get).receiveRights group (received.rights.take fit) (arg 2 &&& 0x40000000 != 0)
        machine.kernel.set next
        let used := before + (if fit == 0 then 0 else aligned (headerSize + 4 * fit))
        if !credentials.isEmpty then writeGuest emu control (credentials ++ Bap.zeroBytes (min room (before - credentials.size)))
        if fit > 0 then
          let message := Abi.field big wordSize (headerSize + 4 * fit) ++ Abi.field big 4 solSocket ++ Abi.field big 4 1 ++
            fds.foldl (fun out fd => out ++ Abi.field big 4 fd) ByteArray.empty
          writeGuest emu (control + before) message
        writeGuest emu (arg 1 + 5 * wordSize) (Abi.field big wordSize used)
        writeGuest emu (arg 1 + 6 * wordSize) (Abi.field big 4 flags)
        pure (.returnValue (if arg 2 &&& 0x20 != 0 then received.size else received.data.size))
  | .shutdown =>
    let action ← apply machine (·.shutdown group (arg 0) (arg 1))
    wakePipeReaders emu
    pure action
  | .setsockopt =>
    match kernel.socketOf group (arg 0) with
    | .error errno => pure (errorOf errno)
    | .ok (number, socket) =>
      -- `SO_RCVTIMEO` and `SO_SNDTIMEO`, of a `struct timeval` of words or, as the new ones, of 64 bits, which it keeps; the others
      -- that it can be given it takes, and they change nothing.
      let name := arg 2
      let receiving := name == timeouts.1 || name == 66
      let sending := name == timeouts.2 || name == 67
      -- `SO_PASSCRED`, of an `int`, which it keeps.
      if arg 1 == solSocket && name == passCred then
        if arg 4 % 2 ^ 32 < 4 then return errorOf Errno.einval
        return ← match ← (read emu (arg 3) 4).toBaseIO with
          | .error _ => pure (errorOf Errno.efault)
          | .ok bytes => do
            machine.kernel.set (kernel.setSocket number { socket with passCredentials := numberAt bytes 0 4 big != 0 })
            pure (.returnValue 0)
      if arg 1 != solSocket || !(receiving || sending) then return .returnValue 0
      let field := if name == 66 || name == 67 then 8 else wordSize
      if arg 4 < 2 * field then return errorOf Errno.einval
      match ← (read emu (arg 3) (2 * field)).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok bytes =>
        let seconds := numberAt bytes 0 field big
        let micros := numberAt bytes field field big
        -- `EDOM` of microseconds of a second or more; a time before 0 is as short as can be.
        if micros ≥ 1000000 then return errorOf 33
        let span := if seconds ≥ 2 ^ (8 * field - 1) then 1 else seconds * 1000000000 + micros * 1000
        machine.kernel.set (kernel.setSocket number
          (if receiving then { socket with receiveTimeout := span } else { socket with sendTimeout := span }))
        pure (.returnValue 0)
  | .getsockopt =>
    match kernel.socketOf group (arg 0) with
    | .error errno => pure (errorOf errno)
    | .ok (_, socket) =>
      -- The room for the value, which is no less than none.
      let room ← match ← (read emu (arg 4) 4).toBaseIO with
        | .ok bytes => pure (numberAt bytes 0 4 big)
        | .error _ => return errorOf Errno.efault
      if room ≥ 2 ^ 31 then return errorOf Errno.einval
      let name := arg 2
      let value : Option ByteArray :=
        -- What TCP and IP are asked of they have nothing to say of.
        if arg 1 == 6 || arg 1 == 0 || arg 1 == 41 then (if socket.family != 1 then some (Abi.field big 4 0) else none)
        else if arg 1 != solSocket then none
        else if name == option 3 0x1008 then some (Abi.field big 4 (typeOf socket.type))
        else if name == option 4 0x1007 then some (Abi.field big 4 0)
        else if name == option 7 0x1001 || name == option 8 0x1002 then some (Abi.field big 4 212992)
        else if name == option 13 0x80 then some (Bap.zeroBytes 8)
        -- `SO_RCVTIMEO` and `SO_SNDTIMEO`, of a `struct timeval` of words or, as the new ones, of 64 bits.
        else if name == timeouts.1 || name == timeouts.2 || name == 66 || name == 67 then
          let span := if name == timeouts.1 || name == 66 then socket.receiveTimeout else socket.sendTimeout
          let field := if name == 66 || name == 67 then 8 else wordSize
          some (Abi.field big field (span / 1000000000) ++ Abi.field big field (span % 1000000000 / 1000))
        else if name == option 30 0x1009 then some (Abi.field big 4 (if socket.listening then 1 else 0))
        else if name == option 38 0x1028 then
          some (Abi.field big 4 (if socket.family == 1 then 0 else if socket.type == 1 then 6 else 17))
        else if name == option 39 0x1029 then some (Abi.field big 4 socket.family)
        else if name == passCred then some (Abi.field big 4 (if socket.passCredentials then 1 else 0))
        else if name == peerCred then
          -- `struct ucred` of the other end: its process, with the user and the group that it acts as, and of none, no process and
          -- user and group -1.
          match (socket.peer.bind kernel.socketAt).map (·.owner) with
          | some owner =>
            let credentials := (kernel.process owner).credentials
            some (Abi.field big 4 owner ++ Abi.field big 4 credentials.euid ++ Abi.field big 4 credentials.egid)
          | none => some (Abi.field big 4 0 ++ Abi.field big 4 (2 ^ 32 - 1) ++ Abi.field big 4 (2 ^ 32 - 1))
        -- The others that it can be asked, such as `SO_REUSEADDR` and `SO_KEEPALIVE`, are off.
        else some (Abi.field big 4 0)
      -- As much of it as there is room for, and how much that is.
      match value with
      | none => pure (errorOf Errno.enoprotoopt)
      | some bytes =>
        let given := bytes.extract 0 room
        try
          writeGuest emu (arg 3) given
          writeGuest emu (arg 4) (Abi.field big 4 given.size)
          pure (.returnValue 0)
        catch _ => pure (errorOf Errno.efault)
  | _ => pure (errorOf Errno.enosys)

/-- Whether there is a clock of an id, to read (`clock_gettime`) or to say the resolution of (`clock_getres`): those that Linux numbers
from 0 to 11 but `CLOCK_SGI_CYCLE`, and below 0 a clock of the CPU time of a process or of a thread of the process that asks, by its id
or 0 for that one. A process is any of its threads to read, and its leader otherwise. What else is below 0 is a clock of a descriptor,
such as of PTP, of which there are none. -/
private def clockExists (emu : Emu) (clock : Nat) (reading : Bool) : IO Bool := do
  let clock := clock % 2 ^ 32
  if clock < 2 ^ 31 then return clock ≤ 11 && clock != 10
  -- `~id << 3`, then 4 of a thread, and which of three clocks it is.
  if clock % 4 == 3 then return false
  let id := (2 ^ 32 - 1 - clock) / 8
  if id == 0 then return true
  let group := (← currentTask emu).group
  pure <| match (← emu.taskTable.get).find? id with
    | none => false
    | some task =>
      if clock &&& 4 != 0 then task.group == group && task.status.isNone
      else if reading then task.status.isNone || task.tid == task.group
      else task.tid == task.group

/-- What the calls of `Poller` need of a machine. -/
private def pollerOf (machine : Machine) : Poller :=
  let emu := machine.emu
  { architecture := machine.architecture, kernel := machine.kernel, timers := machine.timers, signals := machine.signals
    live := do pure (((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups)
    wake := wakePipeReaders, completed := Ring.completed machine.rings machine.architecture.big }

/-- What AIO and io_uring need of a machine, of the process `group`, whose entries do what `call` does. What an io_uring writes to a
pipe doesn't wait: it is what there is room for; and a write that finds that nothing reads it any more sends `SIGPIPE`, as `write` does,
where a send doesn't, as io_uring sends with `MSG_NOSIGNAL`. -/
private def ringsOf (machine : Machine) (poller : Poller) (group : Nat) (call : Call → List Nat → IO SyscallAction) : Ring.Rings :=
  let emu := machine.emu
  let perform (operation : Call) (args : List Nat) : IO SyscallAction := do
    let fd := args.getD 0 0
    let action ← match operation, (← machine.kernel.get).pipeOf group fd with
      | .write, some number => writePipe machine emu group fd number (args.getD 2 0) (fun at_ size => read emu (args.getD 1 0 + at_) size) false
      | .writev, some number => writeVectorPipe machine emu group fd number (args.getD 1 0) (args.getD 2 0) false
      | _, _ => call operation args
    if operation == .write || operation == .writev then brokenPipe machine emu group operation args action
    pure action
  { poller, state := machine.rings, perform }

/-- The system calls of files, memory that files are mapped into, time and what a process asks of itself. -/
private partial def kernelCall (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO SyscallAction := do
    -- The ranges that these change may have a tag, as a program may give what it got from an allocator that tags them.
    let args := match call, args with
      | .munmap, address :: rest | .mprotect, address :: rest | .madvise, address :: rest => emu.config.untag address :: rest
      | _, _ => args
    let machine : Machine := { machine with emu }
    let architecture := machine.architecture
    let args ← match checkedArguments architecture (if ← takesTaggedAddresses emu then emu.config.untag else id) (ioReady (← machine.kernel.get) (← currentTask emu).group call) call args with
      | .ok args => pure args
      | .error errno => return errorOf errno
    let wide := architecture.bits
    let big := architecture.big
    let mips := match architecture with | .mips .. => true | _ => false
    let wordSize := wide / 8
    let cell := Abi.field big
    -- A number that doesn't fit a word on 32 bits, from two arguments in the order of the guest.
    let pair (index : Nat) : Nat :=
      let (low, high) := if big then (args.getD (index + 1) 0, args.getD index 0) else (args.getD index 0, args.getD (index + 1) 0)
      high * 2 ^ 32 + low
    let offset64 (index : Nat) : Nat := if wide == 64 then args.getD index 0 else pair architecture.pairBase
    let arg (index : Nat) : Nat := args.getD index 0
    -- The offset of `preadv` and `pwritev` and of the second ones, which on 32 bits is in two words, the low one first on each.
    let vectorOffset : Nat := if wide == 64 then arg 3 else arg 4 * 2 ^ 32 + arg 3
    -- An `off_t` of a word, as the 64 bits that the kernel has it in, which on 32 bits it is the sign of.
    let offsetWord (index : Nat) : Nat :=
      let value := arg index % 2 ^ wide
      if value ≥ 2 ^ (wide - 1) then value + 2 ^ 64 - 2 ^ wide else value
    let group := (← currentTask emu).group
    let kernel ← machine.kernel.get
    let cwd := kernel.cwdOf group
    let poller := pollerOf machine
    -- `path` from an address, in the directory that the call says.
    -- The path is read first, as `getname` is, and the directory is looked at only for a path that isn't absolute.
    let at_ (directory address : Nat) (action : String → String → IO SyscallAction) : IO SyscallAction := do
      match ← (readString emu address).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok path =>
        -- No name is none, rather than where the call is from; within the root of the process.
        if path.isEmpty then return errorOf Errno.enoent
        match if path.startsWith "/" then .ok cwd else kernel.baseOf group directory (atCwd directory) with
        | .error errno => pure (errorOf errno)
        | .ok from_ =>
          let (from_, path) := kernel.pathIn group from_ path
          action from_ path
    let here := 2 ^ 64 - 100
    let openAt (directory address flags mode : Nat) : IO SyscallAction := do
      -- `O_DIRECTORY` with `O_CREAT`, which `O_TMPFILE` has the first of, is `EINVAL` before the path is looked at, as
      -- `build_open_flags` has it.
      let both := Kernel.oDirectory ||| Kernel.oCreat
      if architecture.openFlags flags &&& both == both then return errorOf Errno.einval
      at_ directory address fun from_ path => do
        let flags := architecture.openFlags flags
        if flags &&& 0x400000 != 0 then return ← applyNat machine (·.openTmpfile group from_ path flags mode)
        -- What makes a pseudo-terminal, and the controlling terminal.
        if let some action ← Tty.openDevice poller emu (Path.ofParts (Path.parts from_ path)) flags then return action
        let current ← machine.kernel.get
        -- A FIFO, or a pipe by its name in `/proc`, as `fifo_open` has it: to read, it is open once something has it open to write,
        -- and to write, once something has it open to read, each of which waits for the other unless it says not to, `O_NONBLOCK`,
        -- of which one to write that nothing reads is `ENXIO`. What waits has it open already, so that the other finds it, and its
        -- descriptor is what its site has, which a signal that ends the wait gives it too. One to read goes on too when there is
        -- something to read, as what wrote it had it open, whether it still has.
        let both := Kernel.oCreat ||| Kernel.oExcl
        let fifo : Option Nat := if flags &&& (Kernel.oPath ||| Kernel.oDirectory) != 0 || flags &&& both == both then none else
          match current.resolve from_ path (follow := flags &&& Kernel.oNofollow == 0) with
          | .ok (_, some number) => if current.inodes.get? number matches some { content := .pipe .., .. } then some number else none
          | _ => none
        if let some number := fifo then
          let access := flags &&& 3
          if access == 0 || access == 1 then
            let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
            let partner (kernel : Kernel) : Bool :=
              if access == 0 then kernel.pipeHeld number live true || kernel.pipeWaiting number > 0 else kernel.pipeHeld number live false
            let nonblocking := flags &&& Kernel.oNonblock != 0
            if ← machine.timers.again emu then
              let fd ← machine.timers.written emu
              if partner current then
                machine.timers.finish (← thread emu)
                return .returnValue fd
              return ← waitOn machine emu number fd
            if access == 1 && nonblocking && !partner current then return errorOf Errno.enxio
            let action ← applyNat machine (·.openPath group from_ path flags mode)
            let .returnValue fd := action | return action
            if fd ≥ 2 ^ 63 then return action
            wakePipeReaders emu
            if nonblocking || partner (← machine.kernel.get) then return action
            return ← waitOn machine emu number fd
        match generatedAt current from_ path with
        | some (name, normal) =>
          if flags &&& 3 != 0 then pure (errorOf Errno.eacces)
          -- It is a file, as far as `O_DIRECTORY` goes.
          else if flags &&& Kernel.oDirectory != 0 then pure (errorOf Errno.enotdir)
          else
            match generatorOf current name with
            | none => pure (errorOf Errno.eio)
            | some generate =>
              let view ← viewOf machine emu (processOfPath normal group)
              let view := match threadOfPath normal with
                | some tid => { view with name := threadName (current.process view.pid) tid }
                | none => view
              let bytes := generate view
              applyNat machine fun kernel => .ok (kernel.openBytes group bytes flags)
        | none =>
          let action ← applyNat machine (·.openPath group from_ path flags mode)
          -- A slave of a pseudo-terminal, which may be locked, or be what its process takes as its controlling terminal.
          match action with
          | .returnValue fd => if fd < 2 ^ 31 then pure ((← Tty.opened poller emu fd flags).getD action) else pure action
          | other => pure other
    -- Of the flags of `faccessat2`, `AT_SYMLINK_NOFOLLOW`, `AT_EACCESS` and `AT_EMPTY_PATH` are all there are, and of a mode,
    -- `R_OK`, `W_OK` and `X_OK`.
    let accessAt (directory address mode flags : Nat) : IO SyscallAction :=
      if flags % 2 ^ 32 ||| 0x1300 != 0x1300 || mode % 2 ^ 32 > 7 then pure (errorOf Errno.einval)
      else do
        -- `AT_EMPTY_PATH` of no path: of what the descriptor is open on, or of `AT_FDCWD` the working directory.
        if flags &&& 0x1000 != 0 then
          if let .ok "" ← (readString emu address).toBaseIO then
            if atCwd directory then
              return match kernel.accessPath group cwd "." (mode % 8) true (flags &&& 0x200 != 0) with
                | .error errno => errorOf errno
                | .ok _ => .returnValue 0
            return match kernel.objectOf group (directory % 2 ^ 32) with
              | .error errno => errorOf errno
              | .ok (_, _, inode) =>
                if Kernel.permits inode (kernel.process group).credentials (flags &&& 0x200 == 0) (mode % 8) then .returnValue 0
                else errorOf Errno.eacces
        at_ directory address fun from_ path =>
          pure (match kernel.accessPath group from_ path (mode % 8) (flags &&& 0x100 == 0) (flags &&& 0x200 != 0) with
            | .error errno => errorOf errno
            | .ok _ => .returnValue 0)
    let liveGroups : IO (List Nat) := do
      pure (((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups)
    -- What is to read of a pipe, if the call has to wait for it: then it stops here and runs again when something changes, with its
    -- registers as they were, and otherwise it goes on.
    let waitForPipe (fd : Nat) : IO (Option SyscallAction) := do
      let current ← machine.kernel.get
      match current.pipeOf group fd with
      | none => pure none
      | some number =>
        -- The end that is written has nothing to read, and `read` says `EBADF` of it.
        let writeOnly := match current.openFileOf group fd with
          | .ok (_, file) => file.flags &&& 3 == 1
          | .error _ => false
        if writeOnly || current.pipeWaiting number > 0 || !current.pipeHeld number (← liveGroups) true then pure none
        else if current.nonblocking group fd then pure (some (errorOf (Errno.eagain)))
        else
          pure (some (← waitOn machine emu number))
    -- What a device that gives all it is asked for gives, and `getrandom`, is written a piece at a time, as `read_zero` writes it: up
    -- to where the memory ends, with what was written by then, or `EFAULT` of none, and without the rest made first. Each piece is
    -- what `piece` gives from where it has got to, of at most a size, and what it gives with it is kept once the piece is written.
    let inPieces {σ : Type} (address count : Nat) (piece : Nat → Nat → IO (Option (ByteArray × σ))) (keep : σ → IO Unit) :
        IO SyscallAction := do
      let mut done := 0
      while done < count do
        -- Of a page at most, which is what is mapped or not.
        let some (bytes, kept) ← piece done (min (4096 - (address + done) % 4096) (count - done)) | break
        if bytes.isEmpty then break
        try writeGuest emu (address + done) bytes catch _ => break
        keep kept
        done := done + bytes.size
      pure (if done == 0 && count > 0 then errorOf Errno.efault else .returnValue done)
    let readInto (fd address count : Nat) : IO SyscallAction := do
      let kernel ← machine.kernel.get
      if kernel.givesAll group fd then
        return ← inPieces address count
          (fun _ size => do pure (((← machine.kernel.get).read group fd size).toOption.map fun (next, bytes) => (bytes, next)))
          machine.kernel.set
      match kernel.read group fd count with
      | .error errno => pure (errorOf errno)
      | .ok (next, bytes) =>
        -- What is read is what was copied: of a pipe, all of it or nothing, as `pipe_read` has it; of a file, what fits where the memory
        -- ends, a page at a time, as `copy_to_user` gives up there.
        let copied ← (writeGuest emu address bytes *> pure bytes.size).catchExceptions fun _ => pure 0
        if copied < bytes.size && (kernel.pipeOf group fd).isSome then return errorOf Errno.efault
        let copied ← if copied == bytes.size then pure copied else do
          let mut done := 0
          while done < bytes.size do
            let size := min (4096 - (address + done) % 4096) (bytes.size - done)
            try writeGuest emu (address + done) (bytes.extract done (done + size)) catch _ => break
            done := done + size
          pure done
        if copied == 0 && bytes.size > 0 then return errorOf Errno.efault
        let next := if copied == bytes.size then next else
          match kernel.read group fd copied with
          | .ok (next, _) => next
          | .error _ => kernel
        machine.kernel.set next
        -- A writer that waits for room has some.
        if copied > 0 && (kernel.pipeOf group fd).isSome then wakePipeReaders emu
        pure (.returnValue copied)
    let writeOut (fd address count : Nat) : IO SyscallAction := do
      let current ← machine.kernel.get
      if let some number := current.pipeOf group fd then
        return ← writePipe machine emu group fd number count (fun at_ size => read emu (address + at_) size) !(current.nonblocking group fd)
      let bytes ← readPrefix emu address count
      if bytes.isEmpty && count > 0 then return errorOf Errno.efault
      applyNat machine (·.write group fd bytes)
    let statAt (directory address out : Nat) (follow : Bool) : IO SyscallAction :=
      at_ directory address fun from_ path =>
        match kernel.statPath from_ path follow (some (kernel.process group).credentials) with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu out (architecture.stat value)
    let clock (out scale : Nat) : IO SyscallAction := do
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returningIf emu out (Abi.time now scale big wordSize)
    -- Anonymous and private is for `serveTaskCalls`, once what it takes the place of isn't mapped.
    let rings := ringsOf machine poller group (kernelCall machine emu)
    let mapMemory (offset : Nat) : IO SyscallAction := do
      -- Neither shared nor private, as `do_mmap` has `MAP_TYPE`, is `EINVAL`, and so is both of no file, `MAP_SHARED_VALIDATE`.
      if arg 3 &&& 3 == 0 || (arg 3 &&& 3 == 3 && arg 3 &&& architecture.mapAnonymous != 0) then return errorOf Errno.einval
      -- More than `RLIMIT_AS` lets it have, but for what `MAP_FIXED` takes the place of.
      let pages := pageUp (arg 1)
      -- More than a process can have, as `do_mmap` has `TASK_SIZE`, and at an address, what would end past it.
      if pages > userLimit architecture || (arg 3 &&& 0x100010 != 0 && arg 0 > userLimit architecture - pages) then
        return errorOf Errno.enomem
      -- What is the process's own to write, or shared without a file, is counted, unless it says not to: `MAP_NORESERVE`, which
      -- MIPS and PowerPC number apart.
      let reserved := arg 3 &&& (if mips then 0x400 else if architecture matches .powerpc .. then 0x40 else 0x4000) == 0
      let counted := if mapsShared (arg 3) then arg 3 &&& architecture.mapAnonymous != 0 else arg 2 &&& 2 != 0
      if reserved && counted && overcommitted pages then return errorOf Errno.enomem
      let regions ← emu.regions.get
      let replaced := if arg 3 &&& 0x10 == 0 then 0 else
        regions.foldl (init := 0) fun total region =>
          total + (min (arg 0 + pages) (region.address + region.data.size) - max (arg 0) region.address)
      if ← addressSpaceFull machine group (pages - replaced) then return errorOf Errno.enomem
      -- The rings of an io_uring.
      if arg 3 &&& architecture.mapAnonymous == 0 then
        if let some action ← Ring.map rings emu group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) offset then return action
      let action ← if arg 3 &&& architecture.mapAnonymous == 0 then
        serveFileMap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) offset
      else if mapsShared (arg 3) then
        serveSharedMemory machine group (arg 0) (arg 1) (arg 2) (arg 3)
      else if arg 1 == 0 then pure (errorOf Errno.einval)
      else
        -- What is anonymous and private, as `serveTaskCalls` has it, here for what it says of where it is.
        match ← mmapPlace emu (arg 0) pages (arg 3) with
        | .error errno => pure (errorOf errno)
        | .ok (start, fixed) =>
          try
            let start ← placeZeros emu start fixed pages (arg 2)
            machine.kernel.modify (·.dropMappings group start (start + pages))
            -- A mapping that grows down, which a fault below it goes by.
            if arg 3 &&& architecture.mapGrowsDown != 0 then
              machine.kernel.modify (noted · group start (start + pages) Guard.growsDown true)
            pure (.returnValue start)
          catch _ => pure (errorOf Errno.enomem)
      -- What was asked for to be written and not read says so, though it can be read.
      if let .returnValue start := action then
        if start < 2 ^ 64 - 4096 then
          machine.kernel.modify (noted · group start (start + pages) Guard.writeOnly (arg 2 &&& 3 == 2))
      pure action
    let vectors (fd address count : Nat) (action : Nat → Nat → Nat → IO SyscallAction) : IO SyscallAction := do
      let mut total := 0
      -- All of the array first, as `import_iovec` has it: one that isn't all there is EFAULT before anything is done.
      let entries ← match ← (read emu address (2 * wordSize * count)).toBaseIO with
        | .ok entries => pure entries
        | .error _ => return errorOf Errno.efault
      -- A length below 0 is `EINVAL`, before anything is done.
      if (List.range count).any fun index => numberAt entries (2 * wordSize * index + wordSize) wordSize big ≥ 2 ^ (wide - 1) then
        return errorOf Errno.einval
      -- And one that ends past the memory of a process `EFAULT`, as `access_ok` has it.
      if (List.range count).any fun index =>
          emu.config.untag (numberAt entries (2 * wordSize * index) wordSize big) +
            numberAt entries (2 * wordSize * index + wordSize) wordSize big > userLimit architecture then
        return errorOf Errno.efault
      -- Of all of them, no more than `MAX_RW_COUNT`.
      let mut asked := 0
      for index in List.range count do
        let field (offset : Nat) : Nat := numberAt entries (2 * wordSize * index + offset) wordSize big
        let length := min (field wordSize) (maxCount - asked)
        asked := asked + length
        match ← action fd (field 0) length with
        | .returnValue value =>
          if value ≥ 2 ^ 63 then
            return if total > 0 then .returnValue total else .returnValue value
          total := total + value
          if value < length then return .returnValue total
        | other => return other
      pure (.returnValue total)
    -- `preadv` and `pwritev`: `pread` and `pwrite` of each piece in turn, from where the one before ended, as `vectors` has them.
    -- What the descriptor is open on is checked first, even of no pieces.
    let atOffset (fd address count offset : Nat) (writing : Bool) (append : Bool := true) : IO SyscallAction := do
      let current ← machine.kernel.get
      let checked := if writing then (current.writeTo group fd .empty offset).map (·.2) else (current.readFrom group fd 0 offset).map (·.size)
      if let .error errno := checked then return errorOf errno
      let done ← IO.mkRef 0
      vectors fd address count fun fd base size => do
        let at__ := offset + (← done.get)
        let action ← if writing then do
            let bytes ← readPrefix emu base size
            if bytes.isEmpty && size > 0 then pure (errorOf Errno.efault)
            else applyNat machine (·.writeTo group fd bytes at__ append)
          else if current.givesAll group fd then
            inPieces base size (fun done piece => do pure ((current.readFrom group fd piece (at__ + done)).toOption.map ((·, ()))))
              fun _ => pure ()
          else
            match (← machine.kernel.get).readFrom group fd size at__ with
            | .error errno => pure (errorOf errno)
            | .ok bytes => returningPrefix emu base bytes
        if let .returnValue value := action then
          if value < 2 ^ 63 then done.modify (· + value)
        pure action
    -- A path in the directory of the second, from another call of `at_`.
    let inDirectory (directory address : Nat) (action : String → IO SyscallAction) : IO SyscallAction :=
      at_ directory address fun from_ path => action (if path.startsWith "/" then path else from_ ++ "/" ++ path)
    -- Of what `read` and `write` serve themselves: terminals, and the objects of `eventfd`, `timerfd`, `signalfd` and `inotify`.
    let isObject (fd : Nat) : Bool := match kernel.objectOf group fd with
      | .ok (_, _, { content := .eventfd .., .. }) | .ok (_, _, { content := .timerfd .., .. }) | .ok (_, _, { content := .signalfd _, .. })
      | .ok (_, _, { content := .ptyMaster _, .. }) | .ok (_, _, { content := .ptySlave _, .. }) | .ok (_, _, { content := .inotify .., .. }) => true
      | _ => false
    let number (address size : Nat) : IO Nat := do pure (numberAt (← read emu address size) 0 size big)
    -- `struct statfs` of the file system that a path of the tree is on: `/proc` and `/sys` are their own, which hold nothing, and
    -- the others are of memory.
    let statfsOf (path : Option String) : ByteArray :=
      let within (root : String) : Bool := path.any fun path => path == root || path.startsWith (root ++ "/")
      if within "/proc" then Abi.statfs (architecture.bits == 64) big mips 0x9fa0 0
      else if within "/sys" then Abi.statfs (architecture.bits == 64) big mips 0x62656572 0
      else Abi.statfs (architecture.bits == 64) big mips
    if [Call.read, .write, .readv, .writev].contains call && kernel.isSocket group (arg 0) then
      return ← socketCall machine emu call args
    match call with
    | .read =>
      match ← Notify.serve machine.notifier poller emu call args with
      | some action => pure action
      | none =>
      match ← Tty.serve poller emu call args with
      | some action => pure action
      | none =>
      match ← poller.serve emu call args with
      | some action => pure action
      | none =>
      -- Of nothing, nothing, at once, as `pipe_read` has it.
      match ← (if arg 2 == 0 then pure none else waitForPipe (arg 0)) with
      | some action => pure action
      | none => readInto (arg 0) (arg 1) (arg 2)
    | .write =>
      match ← Tty.serve poller emu call args with
      | some action => pure action
      | none =>
      match ← poller.serve emu call args with
      | some action => pure action
      | none => writeOut (arg 0) (arg 1) (arg 2)
    | .shmget | .shmat | .shmdt | .shmctl | .semget | .semop | .semtimedop | .semtimedop64 | .semctl | .msgget | .msgsnd | .msgrcv
    | .msgctl | .ipc =>
      pure ((← SysV.serve poller emu call args).getD (errorOf Errno.enosys))
    | .ioSetup | .ioDestroy | .ioSubmit | .ioCancel | .ioGetevents | .ioPgetevents | .ioPgetevents64 | .ioUringSetup | .ioUringEnter
    | .ioUringRegister =>
      pure ((← Ring.serve rings emu call args).getD (errorOf Errno.enosys))
    | .mqOpen | .mqUnlink | .mqTimedsend | .mqTimedsend64 | .mqTimedreceive | .mqTimedreceive64 | .mqNotify | .mqGetsetattr =>
      pure ((← Mqueue.serve poller emu call args).getD (errorOf Errno.enosys))
    | .inotifyInit | .inotifyInit1 | .inotifyAddWatch | .inotifyRmWatch =>
      pure ((← Notify.serve machine.notifier poller emu call args).getD (errorOf Errno.enosys))
    | .poll | .ppoll | .ppoll64 | .select | .pselect6 | .pselect664 | .epollCreate | .epollCreate1 | .epollCtl | .epollWait
    | .epollPwait | .epollPwait2 | .eventfd | .eventfd2 | .timerfdCreate | .timerfdSettime | .timerfdSettime64 | .timerfdGettime
    | .timerfdGettime64 | .signalfd | .signalfd4 =>
      pure ((← poller.serve emu call args).getD (errorOf Errno.enosys))
    | .open_ => openAt here (arg 0) (arg 1) (arg 2)
    | .openat => openAt (arg 0) (arg 1) (arg 2) (arg 3)
    | .close =>
      let action ← apply machine (·.close group (arg 0))
      wakePipeReaders emu
      Tty.hangUp poller emu
      pure action
    | .pipe | .pipe2 =>
      let flags := if call == .pipe2 then architecture.openFlags (arg 1 % 2 ^ 32) else 0
      -- Of its flags, `O_CLOEXEC`, `O_NONBLOCK` and `O_DIRECT`, and `O_NOTIFICATION_PIPE`, which is `O_EXCL`, of a queue of
      -- notifications of the kernel, of which there are none here: `ENOPKG`, as of a kernel made without them. Another is `EINVAL`.
      if flags - (flags &&& (Kernel.oCloexec ||| Kernel.oNonblock ||| Kernel.oDirect ||| Kernel.oExcl)) != 0 then return errorOf Errno.einval
      if flags &&& Kernel.oExcl != 0 then return errorOf 65
      -- Where the descriptors go is there before they are made, as `do_pipe2` has it: no descriptor is left of `EFAULT`.
      if !(mips && call == .pipe) then
        let fits ← (do writeGuest emu (arg 0) (← read emu (arg 0) 8); pure true).catchExceptions fun _ => pure false
        if !fits then return errorOf Errno.efault
      let (next, readFd, writeFd) := (← machine.kernel.get).pipe group flags
      machine.kernel.set next
      -- MIPS gives them in registers, for what is called the same.
      if mips && call == .pipe then
        setReg emu ⟨"R3", .imm wide, 0, false⟩ (bits wide writeFd)
        pure (.returnValue readFd)
      else returning emu (arg 0) (cell 4 readFd ++ cell 4 writeFd)
    | .stat => statAt here (arg 0) (arg 1) true
    | .lstat => statAt here (arg 0) (arg 1) false
    | .fstat =>
      match kernel.statDescriptor group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok value => returning emu (arg 1) (architecture.stat value)
    | .fstatat =>
      -- AT_EMPTY_PATH says that the descriptor is what it is about, which of AT_FDCWD is the working directory.
      let path ← (readString emu (arg 1)).toBaseIO
      match path with
      | .ok "" =>
        if arg 3 &&& 0x1000 != 0 then
          match (if atCwd (arg 0) then kernel.statPath cwd "." (searching := some (kernel.process group).credentials) else kernel.statDescriptor group (arg 0)) with
          | .error errno => pure (errorOf errno)
          | .ok value => returning emu (arg 2) (architecture.stat value)
        else pure (errorOf Errno.enoent)
      -- Of its flags, `AT_SYMLINK_NOFOLLOW`, `AT_NO_AUTOMOUNT`, `AT_EMPTY_PATH` and those of how fresh, as `vfs_statx` has it.
      | .ok _ =>
        if arg 3 % 2 ^ 32 &&& (2 ^ 32 - 1 - 0x7900) != 0 then pure (errorOf Errno.einval)
        else statAt (arg 0) (arg 1) (arg 2) (arg 3 &&& 0x100 == 0)
      | _ => statAt (arg 0) (arg 1) (arg 2) (arg 3 &&& 0x100 == 0)
    | .statfs | .statfs64 =>
      at_ here (arg 0) fun from_ path =>
        match kernel.statPath from_ path (searching := some (kernel.process group).credentials) with
        | .error errno => pure (errorOf errno)
        | .ok _ =>
          let bytes := statfsOf ((kernel.resolve from_ path).toOption.map (·.1))
          if call == .statfs then returning emu (arg 1) bytes else returning emu (arg 2) (bytes.extract 0 (arg 1))
    | .fstatfs | .fstatfs64 =>
      match kernel.statDescriptor group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok value =>
        let bytes := statfsOf (kernel.pathOfInode value.inode)
        if call == .fstatfs then returning emu (arg 1) bytes else returning emu (arg 2) (bytes.extract 0 (arg 1))
    | .execve | .execveat => pure (errorOf Errno.enosys)
    | .sysinfo => returning emu (arg 0) (Abi.sysinfo (architecture.bits == 64) big (kernel.clock / 1000000000 - 1700000000) 1)
    | .statx =>
      let path ← (readString emu (arg 1)).toBaseIO
      let finish (result : Result Kernel.Stat) : IO SyscallAction :=
        match result with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu (arg 4) (Abi.statx value big)
      match path with
      | .ok "" =>
        if arg 2 &&& 0x1000 != 0 then finish (if atCwd (arg 0) then kernel.statPath cwd "." (searching := some (kernel.process group).credentials) else kernel.statDescriptor group (arg 0))
        else pure (errorOf Errno.enoent)
      -- A mask with what is reserved, both ways of how fresh at once, or a flag that there isn't: `EINVAL`, as `do_statx` has it.
      | .ok _ =>
        let given := arg 2 % 2 ^ 32
        if arg 3 &&& 0x80000000 != 0 || given &&& 0x6000 == 0x6000 || given &&& (2 ^ 32 - 1 - 0x7900) != 0 then pure (errorOf Errno.einval)
        else at_ (arg 0) (arg 1) fun from_ text => finish (kernel.statPath from_ text (arg 2 &&& 0x100 == 0) (some (kernel.process group).credentials))
      | _ =>
        at_ (arg 0) (arg 1) fun from_ text => finish (kernel.statPath from_ text (arg 2 &&& 0x100 == 0) (some (kernel.process group).credentials))
    | .lseek =>
      let (negative, distance) := signed wide (arg 1)
      applyNat machine (·.seek group (arg 0) negative distance (arg 2))
    | .llseek =>
      -- Linux ORs the halves of 64 bits: of a 64-bit target, the low one is all of the offset and the high one the offset
      -- shifted, as musl passes them.
      let (negative, distance) := signed 64 ((arg 1 * 2 ^ 32 ||| arg 2) % 2 ^ 64)
      match (← machine.kernel.get).seek group (arg 0) negative distance (arg 4) with
      | .error errno => pure (errorOf errno)
      | .ok (next, position) =>
        machine.kernel.set next
        returning emu (arg 3) (cell 8 position)
    | .pread =>
      if kernel.givesAll group (arg 0) then
        return ← inPieces (arg 1) (arg 2)
          (fun done size => do pure ((kernel.readFrom group (arg 0) size (offset64 3 + done)).toOption.map ((·, ()))))
          fun _ => pure ()
      match kernel.readFrom group (arg 0) (arg 2) (offset64 3) with
      | .error errno => pure (errorOf errno)
      | .ok bytes => returningPrefix emu (arg 1) bytes
    | .pwrite =>
      let bytes ← readPrefix emu (arg 1) (arg 2)
      if bytes.isEmpty && arg 2 > 0 then return errorOf Errno.efault
      applyNat machine (·.writeTo group (arg 0) bytes (offset64 3))
    | .readv =>
      -- What a terminal or another object of the kernel has is a read into the first buffer that has room, which may well be short.
      if isObject (arg 0) then
        let pieces ← (List.range (arg 2)).mapM fun index => do
          pure (← number (arg 1 + 2 * wordSize * index) wordSize, ← number (arg 1 + 2 * wordSize * index + wordSize) wordSize)
        match pieces.find? (·.2 > 0) with
        | some (address, size) => kernelCall machine emu .read [arg 0, address, size]
        | none => pure (.returnValue 0)
      else
      match ← waitForPipe (arg 0) with
      | some action => pure action
      | none => vectors (arg 0) (arg 1) (arg 2) readInto
    | .writev =>
      if isObject (arg 0) then vectors (arg 0) (arg 1) (arg 2) fun fd address count => kernelCall machine emu .write [fd, address, count]
      else match kernel.pipeOf group (arg 0) with
        | some number => writeVectorPipe machine emu group (arg 0) number (arg 1) (arg 2) !(kernel.nonblocking group (arg 0))
        | none => vectors (arg 0) (arg 1) (arg 2) writeOut
    | .preadv | .pwritev => atOffset (arg 0) (arg 1) (arg 2) vectorOffset (call == .pwritev)
    | .preadv2 | .pwritev2 =>
      -- Of the flags, `RWF_HIPRI`, `RWF_DSYNC` and `RWF_SYNC` are of a disk, which there is none of, `RWF_NOWAIT` of what would wait
      -- for one, and `RWF_APPEND` writes at the end, as of `O_APPEND`, wherever it is asked to, and `RWF_NOAPPEND` where it is asked
      -- to, whatever the file was opened for; both are `EINVAL`. The others aren't here.
      let flags := arg 5 % 2 ^ 32
      let appending := call == .pwritev2 && flags &&& 0x10 != 0
      let noAppend := call == .pwritev2 && flags &&& 0x20 != 0
      if flags > 0x3f then pure (errorOf Errno.eopnotsupp)
      else if appending && noAppend then pure (errorOf Errno.einval)
      else if appending then
        match kernel.statDescriptor group (arg 0) with
        | .error errno => pure (errorOf errno)
        | .ok status =>
          -- Of the file's own offset, which goes to the end with what is written.
          if vectorOffset == 2 ^ 64 - 1 then
            match kernel.seek group (arg 0) false status.size 0 with
            | .error errno => pure (errorOf errno)
            | .ok (next, _) =>
              machine.kernel.set next
              kernelCall machine emu .writev (args.take 3)
          else atOffset (arg 0) (arg 1) (arg 2) status.size true
      -- An offset of -1 is that of the file.
      else if vectorOffset == 2 ^ 64 - 1 then kernelCall machine emu (if call == .preadv2 then .readv else .writev) (args.take 3)
      else atOffset (arg 0) (arg 1) (arg 2) vectorOffset (call == .pwritev2) !noAppend
    | .access => accessAt here (arg 0) (arg 1) 0
    | .faccessat => accessAt (arg 0) (arg 1) (arg 2) 0
    | .faccessat2 => accessAt (arg 0) (arg 1) (arg 2) (arg 3)
    | .dup => applyNat machine (·.dup group (arg 0))
    | .dup2 =>
      let action ← applyNat machine (·.dupTo group (arg 0) (arg 1))
      wakePipeReaders emu
      pure action
    | .dup3 => applyNat machine (·.dupTo group (arg 0) (arg 1) (arg 2 &&& Kernel.oCloexec != 0))
    | .fcntl =>
      match arg 1 with
      | 0 => applyNat machine (·.dup group (arg 0) (arg 2))
      | 1030 => applyNat machine (·.dup group (arg 0) (arg 2) true)
      | 1 =>
        pure (match kernel.getCloseOnExec group (arg 0) with
          | .error errno => errorOf errno
          | .ok value => .returnValue (if value then 1 else 0))
      | 2 => apply machine (·.setCloseOnExec group (arg 0) (arg 2 &&& 1 != 0))
      | 3 =>
        pure (match kernel.getFlags group (arg 0) with
          | .error errno => errorOf errno
          | .ok value => .returnValue (architecture.guestFlags value))
      | 4 => apply machine (·.setFlags group (arg 0) (architecture.openFlags (arg 2)))
      | 1031 => applyNat machine (·.setPipeSize group (arg 0) (arg 2) ((kernel.process group).credentials.capable Capability.sysResource))
      | 1032 =>
        pure (match kernel.pipeSize group (arg 0) with
          | .error errno => errorOf errno
          | .ok value => .returnValue value)
      | 1033 => apply machine (·.addSeals group (arg 0) (arg 2))
      | 1034 =>
        pure (match kernel.seals group (arg 0) with
          | .error errno => errorOf errno
          | .ok value => .returnValue value)
      | _ => pure ((← Files.serveLock poller emu args).getD (errorOf Errno.einval))
    | .ioctl =>
      match ← Notify.serve machine.notifier poller emu call args with
      | some action => pure action
      | none =>
      -- No descriptor is a terminal but those of a pseudo-terminal.
      match ← Tty.serve poller emu call args with
      | some action => pure action
      | none =>
      match kernel.openFileOf group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok (_, file) =>
      -- What any descriptor takes, as `do_vfs_ioctl` has it, and what is waiting to be read of a file, a pipe or a socket, as `file_ioctl`,
      -- `pipe_ioctl` and the sockets have it: FIONREAD, FIONBIO, FIOCLEX, FIONCLEX and FIOASYNC, by the numbers of each target.
      let (fionread, fionbio, fioclex, fionclex, fioasync) : Nat × Nat × Nat × Nat × Nat := match architecture with
        | .mips .. => (0x467f, 0x667e, 0x6601, 0x6602, 0x667d)
        | .powerpc .. => (0x4004667f, 0x8004667e, 0x20006601, 0x20006602, 0x8004667d)
        | _ => (0x541b, 0x5421, 0x5451, 0x5450, 0x5452)
      let request := arg 1 % 2 ^ 32
      let content : Option Content := (kernel.inodes.get? file.inode).map (·.content)
      if request == fionread then
        let waiting : Option Nat := match content with
          | some (.file data) => some (data.size - min data.size file.offset)
          | some (.pipe ..) => some (kernel.pipeWaiting file.inode)
          | some (.socket socket) => some (socket.incoming.foldl (· + ·.data.size) 0)
          | _ => none
        match waiting with
        | some waiting => returning emu (arg 2) (cell 4 waiting)
        | none => pure (errorOf Errno.enotty)
      else if request == fionbio then
        match ← (read emu (arg 2) 4).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok bytes =>
          let on := numberAt bytes 0 4 big != 0
          let flags := (if on then Kernel.oNonblock else 0) ||| (file.flags &&& Kernel.oAppend)
          apply machine (·.setFlags group (arg 0) flags)
      else if request == fioclex || request == fionclex then apply machine (·.setCloseOnExec group (arg 0) (request == fioclex))
      else if request == fioasync then pure (.returnValue 0)
      else pure (errorOf Errno.enotty)
    | .getdents =>
      -- What a directory has takes going through all paths, and a program may read it a little at a time.
      let found : Result (Nat × Array (Nat × Nat × String)) ← match kernel.openFileOf group (arg 0) with
        | .error errno => pure (.error errno)
        | .ok (id, file) =>
          let cached ← machine.listing.get
          match cached with
          | some (paths, number, all, _) =>
            if number == file.inode && sameObject paths kernel.paths then pure (.ok (id, all)) else pure (.error 0)
          | none => pure (.error 0)
      let found ← match found with
        | .error 0 =>
          match kernel.directoryListing group (arg 0), kernel.openFileOf group (arg 0) with
          | .ok all, .ok (id, file) =>
            machine.listing.set (some (kernel.paths, file.inode, all, (kernel.pathOfInode file.inode).any inProc))
            pure (.ok (id, all))
          | .error errno, _ | _, .error errno => pure (.error errno)
        | other => pure other
      match found, kernel.openFileOf group (arg 0) with
      | .error errno, _ | _, .error errno => pure (errorOf errno)
      | .ok (id, all), .ok (_, file) =>
        let first := kernel.readsFrom id all file.offset
        -- No entry is shorter than what its header takes.
        let entries := (all.extract first (first + arg 2 / 24 + 1)).toList
        let (bytes, count) := Abi.dirents entries first (arg 2) big
        if count == 0 && !entries.isEmpty then
          pure (errorOf Errno.einval)
        else
          machine.kernel.set (kernel.advance id first count all)
          returning emu (arg 1) bytes bytes.size
    | .getcwd =>
      -- A directory that was removed has no path, and one that isn't under the root of the process is said to be so, as `d_path`
      -- has it.
      match kernel.pathOf (kernel.process group).cwd with
      | none => pure (errorOf Errno.enoent)
      | some path =>
        let (shown, within) := kernel.shownWithin group path
        let text := Path.toBytes ((if within then "" else "(unreachable)") ++ shown ++ "\x00")
        if text.size > arg 1 then pure (errorOf Errno.erange)
        else returning emu (arg 0) text text.size
    | .chdir => at_ here (arg 0) fun _ path => apply machine (·.chdir group path)
    | .fchdir => apply machine (·.fchdir group (arg 0))
    | .mkdir => at_ here (arg 0) fun from_ path => apply machine (·.mkdir group from_ path (arg 1))
    | .mkdirat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.mkdir group from_ path (arg 2))
    | .rmdir => at_ here (arg 0) fun from_ path => apply machine (·.remove group from_ path true)
    | .unlink => at_ here (arg 0) fun from_ path => apply machine (·.remove group from_ path false)
    -- Of its flags, `AT_REMOVEDIR` is all there is.
    | .unlinkat =>
      if arg 2 % 2 ^ 32 &&& (2 ^ 32 - 1 - 0x200) != 0 then pure (errorOf Errno.einval)
      else at_ (arg 0) (arg 1) fun from_ path => apply machine (·.remove group from_ path (arg 2 &&& 0x200 != 0))
    | .mknod => at_ here (arg 0) fun from_ path => apply machine (·.mknod group from_ path (arg 1 % 2 ^ 32) (arg 2 % 2 ^ 32))
    | .mknodat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.mknod group from_ path (arg 2 % 2 ^ 32) (arg 3 % 2 ^ 32))
    | .closeRange =>
      let action ← apply machine (·.closeRange group (arg 0) (arg 1) (arg 2 % 2 ^ 32))
      wakePipeReaders emu
      Tty.hangUp poller emu
      pure action
    | .rename =>
      inDirectory here (arg 0) fun source => inDirectory here (arg 1) fun target =>
        apply machine (·.rename group "/" source target)
    | .renameat =>
      inDirectory (arg 0) (arg 1) fun source => inDirectory (arg 2) (arg 3) fun target =>
        apply machine (·.rename group "/" source target)
    | .mount =>
      at_ here (arg 1) fun from_ target => do
        let text (address : Nat) : IO String := do if address == 0 then pure "" else readString emu address
        let source ← text (arg 0)
        let fstype ← text (arg 2)
        -- What a bind or a move mounts is a path, within the root of the process.
        let source := if arg 3 &&& (4096 ||| 8192) != 0 then
            let (base, path) := kernel.pathIn group cwd source
            Path.ofParts (Path.parts base path)
          else source
        apply machine (·.mount group from_ source target fstype (arg 3))
    | .umount2 => at_ here (arg 0) fun from_ target => apply machine (·.unmount group from_ target (arg 1))
    | .chroot => at_ here (arg 0) fun from_ path => apply machine (·.chroot group from_ path)
    | .pivotRoot =>
      at_ here (arg 0) fun from_ newRoot => at_ here (arg 1) fun base putOld =>
        apply machine fun kernel =>
          if from_ != base then .error Errno.einval
          else kernel.pivotRoot group from_ newRoot putOld
    | .link | .linkat | .renameat2 | .utimensat | .utimensat64 | .utimes | .utime | .futimesat | .chown | .lchown | .fchown
    | .fchownat | .setxattr | .lsetxattr | .fsetxattr | .getxattr | .lgetxattr | .fgetxattr | .listxattr | .llistxattr
    | .flistxattr | .removexattr | .lremovexattr | .fremovexattr | .flock | .memfdCreate | .sendfile | .sendfile64 | .splice | .tee
    | .copyFileRange =>
      pure ((← Files.serve poller emu call args).getD (errorOf Errno.enosys))
    | .symlink | .symlinkat =>
      let (directory, address) := if call == .symlink then (here, arg 1) else (arg 1, arg 2)
      at_ directory address fun from_ path => do
        match ← (readString emu (arg 0)).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok target => apply machine (·.symlink group from_ target path)
    | .readlink | .readlinkat =>
      let (directory, address, out, room) := if call == .readlink then (here, arg 0, arg 1, arg 2) else (arg 0, arg 1, arg 2, arg 3)
      -- Its room is an `int`: none, or less, is `EINVAL`, before the path is looked at.
      if room % 2 ^ 32 == 0 || room % 2 ^ 32 ≥ 2 ^ 31 then pure (errorOf Errno.einval) else
      -- Of no path, `readlinkat` is of what the descriptor is open on, a link that `O_PATH` with `O_NOFOLLOW` opened: of anything
      -- else, `ENOENT`, as of the working directory.
      let empty ← if call == .readlinkat then do pure ((← (readString emu address).toBaseIO).toOption == some "") else pure false
      if empty && !atCwd directory then
        match kernel.objectOf group (directory % 2 ^ 32) with
        | .error errno => pure (errorOf errno)
        | .ok (_, _, { content := .symlink target, .. }) =>
          let bytes := (Path.toBytes target).extract 0 room
          returning emu out bytes bytes.size
        | .ok _ => pure (errorOf Errno.enoent)
      else
      at_ directory address fun from_ path =>
        match kernel.readlink from_ path (some (kernel.process group).credentials) with
        | .error errno => pure (errorOf errno)
        | .ok target =>
          let bytes := Path.toBytes target
          let bytes := bytes.extract 0 room
          returning emu out bytes bytes.size
    | .chmod => at_ here (arg 0) fun from_ path => apply machine (·.chmod group from_ path (arg 1))
    | .fchmod => apply machine (·.fchmod group (arg 0) (arg 1))
    | .fchmodat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.chmod group from_ path (arg 2))
    | .truncate => at_ here (arg 0) fun from_ path => apply machine (·.truncatePath group from_ path (offsetWord 1))
    | .ftruncate => apply machine (·.truncateDescriptor group (arg 0) (offsetWord 1))
    | .truncate64 => at_ here (arg 0) fun from_ path => apply machine (·.truncatePath group from_ path (pair (architecture.pairBase - 2)))
    | .ftruncate64 => apply machine (·.truncateDescriptor group (arg 0) (pair (architecture.pairBase - 2)))
    | .fsync | .fdatasync =>
      match kernel.syncDescriptor group (arg 0) with
      | .ok () => pure (.returnValue 0)
      | .error errno => pure (errorOf errno)
    -- Of `syncfs` there is no disk to write to, whatever a descriptor is open on.
    | .syncfs => pure (match kernel.openFileOf group (arg 0) with
      | .ok _ => .returnValue 0
      | .error errno => errorOf errno)
    -- Nor of `sync`.
    | .sync => pure (.returnValue 0)
    | .fallocate =>
      let (offset, size) := if wide == 64 then (arg 2, arg 3) else (pair 2, pair 4)
      apply machine (·.allocate group (arg 0) (arg 1 % 2 ^ 32) offset size)
    -- What `posix_fadvise` says is to come has nothing to change, as all of a file is in memory, but what it is given is checked: the
    -- length, which of `fadvise64` on 32 bits is a word, and the advice, after the offset where the pairs start.
    | .fadvise64 | .fadvise6464 | .armFadvise6464 =>
      let base := architecture.pairBase - 2
      let (length, advice) := match call with
        | .armFadvise6464 => (pair 4, arg 1)
        | .fadvise6464 => (pair (base + 2), arg (base + 4))
        | _ => if wide == 64 then (arg 2, arg 3) else (arg (base + 2), arg (base + 3))
      pure (match kernel.objectOf group (arg 0) with
        | .error errno => errorOf errno
        | .ok (_, _, { content := .pipe .., .. }) => errorOf Errno.espipe
        | .ok _ => if negativeOffset length || advice % 2 ^ 32 > 5 then errorOf Errno.einval else .returnValue 0)
    | .umask =>
      let process := kernel.process group
      machine.kernel.set (kernel.setProcess group { process with umask := arg 0 &&& 0o777 })
      pure (.returnValue process.umask)
    | .mmap => mapMemory (arg 5)
    | .mmap2 => mapMemory (arg 5 * 4096)
    | .munmap =>
      if arg 0 % 4096 != 0 || arg 1 == 0 then pure (errorOf Errno.einval)
      -- Past where the memory of a process ends, as `__vm_munmap` has `TASK_SIZE`.
      else if arg 0 > userLimit architecture || arg 1 > userLimit architecture - arg 0 then pure (errorOf Errno.einval)
      else
        machine.kernel.modify (·.dropMappings group (arg 0) (arg 0 + pageUp (arg 1)))
        pure .default
    | .mprotect =>
      -- `PROT_GROWSDOWN` is of all of a mapping that grows down from where it starts, as `do_mprotect_pkey` has it, and of
      -- another, `EINVAL`, as `PROT_GROWSUP` is of any here, where nothing grows up; of where nothing is mapped, `ENOMEM`.
      let grows := arg 2 &&& 0x03000000
      let (lower, bits) ← if grows == 0 || grows == 0x03000000 || arg 0 % 4096 != 0 || arg 1 == 0 then pure (arg 0, arg 2) else
        match lookupRegion (← emu.regions.get) (arg 0) with
        | none => return errorOf Errno.enomem
        | some _ =>
          match (kernel.process group).guards.find? fun guard =>
              guard.bits == Guard.growsDown && guard.start ≤ arg 0 && arg 0 < guard.start + guard.size with
          | some guard => if grows == 0x01000000 then pure (guard.start, arg 2 - grows) else return errorOf Errno.einval
          | none => return errorOf Errno.einval
      let upper := arg 0 + pageUp (arg 1)
      if bits &&& 2 != 0 && (kernel.process group).mappings.any (fun mapping => mapping.shared && !mapping.mayWrite && mapping.overlaps lower upper) then
        pure (errorOf Errno.eacces)
      else do
        -- What `settleMappings` keeps with another protection has the one that this gives it, which it then keeps anew.
        let process := kernel.process group
        let (kept, guards) := process.guards.partition fun guard => guard.isPastEnd || guard.isSibling
        if !kept.isEmpty then
          machine.kernel.set (kernel.setProcess group { process with guards := guards ++ kept.flatMap (·.without lower upper) })
        match ← protectRange emu lower (upper - lower) bits with
        | .ok _ =>
          machine.kernel.modify (noted · group lower upper Guard.writeOnly (bits &&& 3 == 2))
          pure (.returnValue 0)
        | .error errno => pure (errorOf errno)
    | .madvise =>
      -- The advice that there is, of a range that is mapped.
      let advice := arg 2
      if arg 0 % 4096 != 0 || !(advice ≤ 4 || (8 ≤ advice && advice ≤ 25) || (100 ≤ advice && advice ≤ 103)) then
        pure (errorOf Errno.einval)
      -- What ends past the last address there is, where it would be before where it starts.
      else if arg 0 + pageUp (arg 1) > 2 ^ architecture.bits then pure (errorOf Errno.einval)
      else if !coversRange (← emu.regions.get) (arg 0) (arg 0 + pageUp (arg 1)) then
        -- What is mapped of it is advised all the same, as `madvise_walk_vmas` has it, and what isn't is `ENOMEM` after: each piece
        -- that is mapped, as the range may be of more than there is.
        if advice == 4 then
          let upper := arg 0 + pageUp (arg 1)
          for region in ← emu.regions.get do
            let first := max (arg 0) region.address
            let stop := min upper (region.address + region.data.size)
            if first < stop then zapPages machine group first (stop - first)
        pure (errorOf Errno.enomem)
      else if advice == 9 || advice == 102 || advice == 103 then serveRemoval machine group (arg 0) (arg 0 + pageUp (arg 1)) advice
      -- `MADV_DONTFORK`, `MADV_DOFORK`, `MADV_WIPEONFORK` and `MADV_KEEPONFORK`, which a child of `fork` goes by. Only what is private
      -- and anonymous can be wiped.
      else if advice == 18 && (kernel.process group).mappings.any (·.overlaps (arg 0) (arg 0 + pageUp (arg 1))) then
        pure (errorOf Errno.einval)
      else if advice ∈ [10, 11, 18, 19] then
        machine.kernel.set (kernel.adviseFork group (arg 0) (arg 0 + pageUp (arg 1)) (advice ≥ 18) (advice % 2 == 0))
        pure (.returnValue 0)
      else serveAdvice machine group (arg 0) (arg 1) advice
    | .msync =>
      -- `MS_ASYNC`, `MS_INVALIDATE` and `MS_SYNC`, but not the first and the last. What a shared mapping wrote is in its file already.
      if arg 0 % 4096 != 0 || arg 2 ≥ 8 || arg 2 &&& 5 == 5 then pure (errorOf Errno.einval)
      else if !coversRange (← emu.regions.get) (arg 0) (arg 0 + pageUp (arg 1)) then pure (errorOf Errno.enomem)
      else pure (.returnValue 0)
    | .mlock | .munlock | .mlock2 =>
      -- Of the pages of the range, which are all in memory as they are.
      let lower := arg 0 - arg 0 % 4096
      if call == .mlock2 && arg 2 > 1 then pure (errorOf Errno.einval)
      else if !coversRange (← emu.regions.get) lower (pageUp (arg 0 + arg 1)) then pure (errorOf Errno.enomem)
      else pure (.returnValue 0)
    | .mlockall =>
      -- `MCL_CURRENT` or `MCL_FUTURE`, and `MCL_ONFAULT` with one of them.
      if arg 0 &&& 3 == 0 || arg 0 ≥ 8 then pure (errorOf Errno.einval) else pure (.returnValue 0)
    | .munlockall => pure (.returnValue 0)
    | .mincore =>
      if arg 0 % 4096 != 0 then pure (errorOf Errno.einval)
      else if !coversRange (← emu.regions.get) (arg 0) (arg 0 + pageUp (arg 1)) then pure (errorOf Errno.enomem)
      else returning emu (arg 2) (ByteArray.mk (Array.replicate (pageUp (arg 1) / 4096) 1))
    | .membarrier =>
      -- What it can do, and what a process has to register for first: the expedited private ones, of a core too, and of rseq.
      let process := kernel.process group
      let command := arg 0
      let known := 0x1ff
      if arg 1 != 0 || (command != 0 && (command &&& (command - 1) != 0 || command &&& known == 0)) then pure (errorOf Errno.einval)
      else if command == 0 then pure (.returnValue known)
      else if command ∈ [16, 64, 256] then
        machine.kernel.set (kernel.setProcess group { process with barriers := process.barriers ||| command })
        pure (.returnValue 0)
      else if command ∈ [8, 32, 128] && process.barriers &&& (2 * command) == 0 then pure (errorOf Errno.eperm)
      else pure (.returnValue 0)
    | .mremap =>
      releaseMappings machine emu group (arg 0) (arg 0 + pageUp (arg 1))
      serveRemap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4)
    | .brk => serveBreak machine group (arg 0)
    | .gettimeofday => clock (arg 0) 1000
    | .time =>
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returningIf emu (arg 0) (cell wordSize (now / 1000000000)) (now / 1000000000)
    | .clockGettime | .clockGetres | .clockGettime64 | .clockGetres64 =>
      let reading := call == .clockGettime || call == .clockGettime64
      let size := if call == .clockGettime || call == .clockGetres then wordSize else 8
      if !(← clockExists emu (arg 0) reading) then pure (errorOf Errno.einval)
      else if !reading then returningIf emu (arg 1) (Abi.time 1 1 big size)
      else
        let (next, now) := (← machine.kernel.get).tick
        machine.kernel.set next
        returning emu (arg 1) (Abi.time now 1 big size)
    | .setThreadArea =>
      if architecture == .arm then
        setReg emu ⟨"TPIDRURO", .imm 32, 0, false⟩ (bits 32 (arg 0))
        pure (.returnValue 0)
      else if architecture == .i686 then
        -- A `struct user_desc`: it says which entry it wants, or that any will do, and gets one, whose base is at 4.
        match ← (read emu (arg 0) 8).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok entry =>
          let base := (List.range 4).foldl (fun value index => value + entry[4 + index]!.toNat * 256 ^ index) 0
          setReg emu ⟨"GS_BASE", .imm 32, 0, false⟩ (bits 32 base)
          if entry[0]! == 0xff then writeGuest emu (arg 0) (Abi.bytesOf 4 12)
          pure (.returnValue 0)
      else
        setReg emu ⟨"USERLOCAL", .imm wide, 0, false⟩ (bits wide (arg 0))
        pure (.returnValue 0)
    | .uname => returning emu (arg 0) (Abi.utsname "bap" architecture.name)
    | .getrlimit | .prlimit | .getpgid | .setpgid | .getpgrp | .setsid | .getsid | .getuid | .geteuid | .getgid | .getegid | .setuid
    | .setgid | .setreuid | .setregid | .setresuid | .setresgid | .getresuid | .getresgid | .setfsuid | .setfsgid | .getgroups
    | .setgroups | .capget | .capset | .setrlimit | .getrusage | .times | .getpriority | .setpriority | .schedSetaffinity
    | .schedGetparam | .schedSetparam | .schedGetscheduler | .schedSetscheduler | .schedGetPriorityMax | .schedGetPriorityMin
    | .schedRrGetInterval | .schedRrGetInterval64 =>
      let identity : Identity := { architecture, kernel := machine.kernel }
      pure ((← identity.serve emu call args).getD (errorOf Errno.enosys))
    | .getrandom =>
      -- Of its flags, `GRND_NONBLOCK`, `GRND_RANDOM` and `GRND_INSECURE`, of which the last two aren't both.
      if arg 2 % 2 ^ 32 > 7 || arg 2 &&& 6 == 6 then return errorOf Errno.einval
      -- A fixed sequence, as a run is the same each time, of which each call has what comes after what the last one had.
      inPieces (arg 0) (min (arg 1) maxCount)
        (fun _ size => do
          let given := (← machine.kernel.get).randomGiven
          pure (some (Kernel.randomBytes given size, given + size)))
        fun given => machine.kernel.modify fun kernel => { kernel with randomGiven := given }
    | .sigaltstack => returningIf emu (arg 1) (ByteArray.mk (Array.replicate (3 * wordSize) 0))
    | .schedGetaffinity =>
      -- Of a mask that has room for the processors that there are, one, and that is of whole words, as `sched_getaffinity` has it,
      -- `EINVAL` otherwise; of a thread that there is.
      let target := arg 0 % 2 ^ 32
      if arg 1 == 0 || arg 1 % wordSize != 0 then pure (errorOf Errno.einval)
      else if target != 0 && !(← emu.taskTable.get).tasks.any (fun task => task.tid == target && task.status.isNone) then pure (errorOf 3)
      else returning emu (arg 2) (cell wordSize 1) wordSize
    | .succeeds => pure (.returnValue 0)
    -- Served by `Bap.Linux.Seccomp` before it comes here.
    | .seccomp => pure (errorOf Errno.enosys)
    | .nanosleep | .clockNanosleep | .clockNanosleep64 | .setitimer | .getitimer | .alarm | .timerCreate | .timerSettime
    | .timerSettime64 | .timerGettime | .timerGettime64 | .timerGetoverrun | .timerDelete =>
      pure ((← machine.timers.serve emu call args).getD (errorOf Errno.enosys))
    | .prctl =>
      -- What a program asks of tagged addresses, on AArch64, `PR_SET_TAGGED_ADDR_CTRL` and `PR_GET_TAGGED_ADDR_CTRL`: whether the
      -- kernel takes them from the thread, `PR_TAGGED_ADDR_ENABLE`, which is all there is to ask without MTE, and which a thread
      -- starts without (`set_tagged_addr_ctrl`, `Emu.taggedAddresses`).
      if architecture == .aarch64 && arg 0 == 55 then
        if arg 1 ≤ 1 && arg 2 == 0 && arg 3 == 0 && arg 4 == 0 then
          setReg emu taggedAddresses (bits 1 (arg 1))
          pure (.returnValue 0)
        else pure (errorOf Errno.einval)
      else if architecture == .aarch64 && arg 0 == 56 then
        if arg 1 == 0 && arg 2 == 0 && arg 3 == 0 && arg 4 == 0 then
          pure (.returnValue (if ← takesTaggedAddresses emu then 1 else 0))
        else pure (errorOf Errno.einval)
      -- `PR_SET_NAME` and `PR_GET_NAME`, of the name of the thread that calls, which is given and taken with the zero that ends it: of
      -- the first, the name of the process.
      else if arg 0 == 15 then
        match ← (readString emu (arg 1)).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok name =>
          let tid ← thread emu
          let process := kernel.process group
          let process := if tid == group then { process with name := commOf name }
            else { process with threadNames := (tid, commOf name) :: process.threadNames.filter (·.1 != tid) }
          machine.kernel.set (kernel.setProcess group process)
          pure (.returnValue 0)
      else if arg 0 == 16 then
        let name := (threadName (kernel.process group) (← thread emu)).toUTF8
        returning emu (arg 1) (name ++ Bap.zeroBytes (commLength + 1 - name.size)) 0
      else
        let tid ← thread emu
        let notes ← machine.notes.get
        let process := kernel.process group
        match arg 0 with
        -- `PR_SET_PDEATHSIG` and `PR_GET_PDEATHSIG`: the signal that the thread is sent when its parent ends, or 0 for none.
        | 1 =>
          if arg 1 > (if mips then 128 else 64) then pure (errorOf Errno.einval)
          else
            machine.notes.set { notes with
              deathSignals := if arg 1 == 0 then notes.deathSignals.erase tid else notes.deathSignals.insert tid (arg 1) }
            pure (.returnValue 0)
        | 2 => returning emu (arg 1) (cell 4 (notes.deathSignals.getD tid 0))
        -- `PR_GET_DUMPABLE` and `PR_SET_DUMPABLE`, which may be 0 or 1.
        | 3 => pure (.returnValue (notes.dumpable.getD group 1))
        | 4 =>
          if arg 1 > 1 then pure (errorOf Errno.einval)
          else
            machine.notes.set { notes with dumpable := if arg 1 == 1 then notes.dumpable.erase group else notes.dumpable.insert group (arg 1) }
            pure (.returnValue 0)
        -- `PR_CAPBSET_READ` and `PR_CAPBSET_DROP`, of a capability that there is, the latter with `CAP_SETPCAP`.
        | 23 =>
          if arg 1 > 40 then pure (errorOf Errno.einval)
          else pure (.returnValue (if process.credentials.bounding.testBit (arg 1) then 1 else 0))
        | 24 =>
          if !process.credentials.capable Capability.setpcap then pure (errorOf Errno.eperm)
          else if arg 1 > 40 then pure (errorOf Errno.einval)
          else
            let bounding := process.credentials.bounding
            let bounding := if bounding.testBit (arg 1) then bounding - 2 ^ arg 1 else bounding
            machine.kernel.set (kernel.setProcess group { process with credentials := { process.credentials with bounding } })
            pure (.returnValue 0)
        -- `PR_SET_CHILD_SUBREAPER` and `PR_GET_CHILD_SUBREAPER`: whether it takes in the children of its descendants that end.
        | 36 =>
          machine.notes.set { notes with
            subreapers := if arg 1 != 0 then (if notes.subreapers.contains group then notes.subreapers else group :: notes.subreapers)
              else notes.subreapers.erase group }
          pure (.returnValue 0)
        | 37 => returning emu (arg 1) (cell 4 (if notes.subreapers.contains group then 1 else 0))
        -- An option that there isn't, as `prctl` has it of those that it doesn't know.
        | _ => pure (errorOf Errno.einval)
    | .socket | .socketpair | .bind | .listen | .accept | .accept4 | .connect | .getsockname | .getpeername | .sendto | .recvfrom
    | .send | .recv | .setsockopt | .getsockopt | .shutdown | .sendmsg | .recvmsg => socketCall machine emu call args

/-- The paths that a call is given, by the index of each, and whether the argument before it is a directory that it is from. -/
private def pathArguments : Call → List (Nat × Bool)
  | .open_ | .stat | .lstat | .access | .readlink | .chdir | .truncate | .truncate64 | .statfs | .statfs64 | .execve | .mkdir | .rmdir
  | .unlink | .chmod | .chown | .lchown | .utimes | .utime | .setxattr | .lsetxattr | .getxattr | .lgetxattr | .listxattr
  | .llistxattr | .removexattr | .lremovexattr | .chroot | .umount2 => [(0, false)]
  | .openat | .fstatat | .statx | .faccessat | .faccessat2 | .readlinkat | .mkdirat | .unlinkat | .fchmodat | .fchownat | .utimensat
  | .utimensat64 | .futimesat | .execveat => [(1, true)]
  | .mknod => [(0, false)]
  | .mknodat => [(1, true)]
  | .rename | .link => [(0, false), (1, false)]
  | .renameat | .renameat2 | .linkat => [(1, true), (3, true)]
  | .symlink | .inotifyAddWatch | .mount => [(1, false)]
  | .symlinkat => [(2, true)]
  | _ => []

/-- What a path of the tree is under a directory of the host that the machine sees: each part of it that the kernel hasn't and the
host has comes in, once, as a directory, as a file with what it holds, or as a link to what is in the same directory of the host; a
link to anything else of the host isn't there, so that nothing of the host but what is in the directory comes in. A directory at the
end comes in with its entries, each of which is a directory that is empty until it is looked in, a file or a link. -/
private partial def fromHost (machine : Machine) (path : String) (links : Nat := 8) : IO Unit := do
  let within (path prefix_ : String) : Bool := prefix_ == "/" || path == prefix_ || path.startsWith (prefix_ ++ "/")
  let some (hostRoot, guestRoot) := (← machine.hostMounts.get).reverse.find? (within path ·.2) | return
  let child (parent name : String) : String := if parent == "/" then "/" ++ name else parent ++ "/" ++ name
  -- One path, and whether it is a directory to go on into.
  let bring (guest host : String) : IO Bool := do
    let isDirectory : IO Bool := do
      let kernel ← machine.kernel.get
      pure ((kernel.paths.get? guest).bind kernel.inodes.get? |>.any (·.content matches .directory))
    if (← machine.kernel.get).hostSeen.contains guest || (← machine.kernel.get).paths.contains guest then return ← isDirectory
    machine.kernel.modify fun kernel => { kernel with hostSeen := kernel.hostSeen.insert guest }
    let real ← (IO.FS.realPath host).toBaseIO
    match real with
    | .error _ => return false
    | .ok real =>
      let realText := real.toString
      if !within realText hostRoot then return false
      if (← (System.FilePath.mk host).symlinkMetadata.toBaseIO).toOption.any (·.type == .symlink) then
        machine.kernel.modify (·.addSymlink guest (if realText == hostRoot then guestRoot
          else child guestRoot (realText.drop (hostRoot.length + if hostRoot == "/" then 0 else 1)).toString))
        return false
      match ← real.metadata.toBaseIO with
      | .ok { type := .dir, .. } =>
        machine.kernel.modify (·.addDirectories guest)
        pure true
      | .ok { type := .file, .. } =>
        if let .ok data ← (IO.FS.readBinFile real).toBaseIO then machine.kernel.modify (·.addFile guest data)
        pure false
      | _ => pure false
  let parts := (Path.parts "/" path).drop (Path.parts "/" guestRoot).length
  let mut guest := guestRoot
  let mut host := hostRoot
  for (part, index) in parts.zipIdx do
    guest := child guest part
    host := child host part
    if !(← bring guest host) then
      -- A link goes on where it leads, with the rest of the path, as resolving it will.
      let kernel ← machine.kernel.get
      if let some { content := .symlink target, .. } := (kernel.paths.get? guest).bind kernel.inodes.get? then
        if links > 0 then
          let rest := parts.drop (index + 1)
          fromHost machine (Path.ofParts (Path.parts (Path.parent guest) target ++ rest)) (links - 1)
      return
  -- What the directory at the end has.
  if (← machine.kernel.get).hostSeen.contains (guest ++ "/") then return
  machine.kernel.modify fun kernel => { kernel with hostSeen := kernel.hostSeen.insert (guest ++ "/") }
  if let .ok entries ← (System.FilePath.mk host).readDir.toBaseIO then
    for entry in entries do
      let _ ← bring (child guest entry.fileName) (child host entry.fileName)

/-- Whether a path from `/` may look at `/proc`: `/dev/stdin`, `/dev/stdout`, `/dev/stderr` and `/dev/fd` are links to `/proc/self/fd`. -/
private def looksAtProc (path : String) : Bool := ["/proc", "/dev/std", "/dev/fd"].any (path.startsWith ·)

/-- Makes `/proc` what it is for the threads that there are now. -/
private def makeProc (machine : Machine) (emu : Emu) (group : Nat) : IO Unit := do
  let self ← thread emu
  let live ← liveProcesses emu
  let tasks := (← emu.taskTable.get).tasks.filter (·.status.isNone)
  machine.kernel.modify (Proc.refresh · group self live fun pid => (tasks.filter (·.group == pid)).map (·.tid))

/-- Makes `/proc` what it has to be for a call that may look at it, which a path tells, or of `getdents` the directory that it reads,
which the directory that was read last says, if it is that one. -/
private def refreshProc (machine : Machine) (emu : Emu) (group : Nat) (call : Call) (args : List Nat) : IO Unit := do
  let kernel ← machine.kernel.get
  let looks ← if call == .getdents then
      match kernel.openFileOf group (args.getD 0 0) with
      | .error _ => pure false
      | .ok (_, file) =>
        match ← machine.listing.get with
        | some (_, number, _, proc) => if number == file.inode then pure proc else pure ((kernel.pathOfInode file.inode).any inProc)
        | none => pure ((kernel.pathOfInode file.inode).any inProc)
    else
      -- Of each path that it is given, of which one that is relative to a directory is of the argument before it, which may be in
      -- there.
      (pathArguments call).anyM fun (index, relative) => do
        match ← (readString emu (args.getD index 0)).toBaseIO with
        | .error _ => pure false
        | .ok path =>
          let base := if relative && !atCwd (args.getD (index - 1) 0) then
              (kernel.baseOf group (args.getD (index - 1) 0) false).toOption.getD ""
            else kernel.cwdOf group
          pure (looksAtProc (Path.ofParts (Path.parts base path)))
  if looks then
    makeProc machine emu group
    -- What was read of a directory before is of what was there then.
    if call == .getdents then machine.listing.set none

/-- `write`, on its own: nothing here holds on to the kernel, so that a program that writes a little at a time doesn't have what it wrote before copied each time. -/
private def writeDirect (machine : Machine) (emu : Emu) (group fd address count : Nat) : IO SyscallAction := do
  let current ← machine.kernel.get
  if let some number := current.pipeOf group fd then
    return ← writePipe machine emu group fd number count (fun at_ size => read emu (address + at_) size) !(current.nonblocking group fd)
  if let some errno := current.writeError group fd count then return errorOf errno
  let count := current.limitedCount group fd count
  let bytes ← readPrefix emu address count
  if bytes.isEmpty && count > 0 then return errorOf Errno.efault
  machine.kernel.modify (·.writeKnown group fd bytes)
  pure (.returnValue bytes.size)

/-- `pwrite`, on its own, as `writeDirect` is. -/
private def writeDirectAt (machine : Machine) (emu : Emu) (group fd address count offset : Nat) : IO SyscallAction := do
  let current ← machine.kernel.get
  if let some errno := current.writeAtError group fd count offset then return errorOf errno
  let count := current.limitedCount group fd count offset
  let bytes ← readPrefix emu address count
  if bytes.isEmpty && count > 0 then return errorOf Errno.efault
  machine.kernel.modify (·.writeKnownAt group fd bytes offset)
  pure (.returnValue bytes.size)

/-- `writev`, by `writeDirect`. -/
private def writeVectorDirect (machine : Machine) (emu : Emu) (group fd address count : Nat) : IO SyscallAction := do
  let current ← machine.kernel.get
  if let some number := current.pipeOf group fd then
    return ← writeVectorPipe machine emu group fd number address count !(current.nonblocking group fd)
  let word := machine.architecture.bits / 8
  let big := machine.architecture.big
  let mut total := 0
  let entries ← match ← (read emu address (2 * word * count)).toBaseIO with
    | .ok entries => pure entries
    | .error _ => return errorOf Errno.efault
  -- A length below 0 is `EINVAL`, before anything is done, as `import_iovec` has it.
  if (List.range count).any fun index => numberAt entries (2 * word * index + word) word big ≥ 2 ^ (8 * word - 1) then
    return errorOf Errno.einval
  for index in List.range count do
    let field (offset : Nat) : Nat := numberAt entries (2 * word * index + offset) word big
    match ← writeDirect machine emu group fd (field 0) (field word) with
    | .returnValue value =>
      if value ≥ 2 ^ 63 then
        return if total > 0 then .returnValue total else .returnValue value
      total := total + value
      if value < field word then return .returnValue total
    | other => return other
  pure (.returnValue total)

/-- What a call gives, as the guest has it. -/
private def handOver (machine : Machine) (emu : Emu) : SyscallAction → IO SyscallAction
  | .returnValue value => do
    -- A call that runs again has its registers as they were, with its flag of an error, which is `a3` on MIPS, among them.
    if (← emu.redirect.get).isSome then return .returnValue value
    if value ≥ 2 ^ 64 - 4096 then syscallReturn emu (.error (machine.architecture.errno (2 ^ 64 - value)))
    else syscallReturn emu (.ok value)
  | action => pure action

/-- Something may have been let go of: once in a while, what nothing holds goes. -/
private def released (machine : Machine) : IO Unit := do
  let count := (← machine.releases.get) + 1
  if count < 256 then machine.releases.set count
  else
    machine.releases.set 0
    machine.kernel.modify Kernel.collect

/-- What makes a descriptor makes none at or past RLIMIT_NOFILE, which is known before the call does anything, as Linux takes the
descriptor first: `EMFILE`, and of `dup2` and `dup3` to one past it `EBADF`, and of `F_DUPFD` from one past it `EINVAL`. Before that,
`dup3` takes no flag but `O_CLOEXEC`, nor a descriptor to itself: `EINVAL`. -/
private def descriptorLimit (machine : Machine) (group : Nat) (call : Call) (args : List Nat) : IO (Option SyscallAction) := do
  let kernel ← machine.kernel.get
  let limit := (kernel.limitOf group 7).1
  let descriptors := (kernel.process group).descriptors
  let free (from_ : Nat) : Nat := Kernel.lowestFree descriptors from_
  let arg (index : Nat) : Nat := args.getD index 0
  -- A descriptor that is none, as `signalfd` is given to make one.
  let none_ (value : Nat) : Bool := value % 2 ^ 32 == 2 ^ 32 - 1
  let full := free 0 ≥ limit
  pure <| match call with
    | .open_ | .openat | .dup | .socket | .accept | .accept4 | .eventfd | .eventfd2 | .epollCreate | .epollCreate1 | .timerfdCreate
    | .memfdCreate | .inotifyInit | .inotifyInit1 | .mqOpen | .ioUringSetup =>
      if full then some (errorOf Errno.emfile) else none
    | .signalfd | .signalfd4 => if none_ (arg 0) && full then some (errorOf Errno.emfile) else none
    -- Two of them.
    | .pipe | .pipe2 | .socketpair => if free (free 0 + 1) ≥ limit then some (errorOf Errno.emfile) else none
    | .dup2 | .dup3 =>
      let flags := arg 2 % 2 ^ 32
      if call == .dup3 && (flags - (flags &&& Kernel.oCloexec) != 0 || arg 0 % 2 ^ 32 == arg 1 % 2 ^ 32) then some (errorOf Errno.einval)
      -- Its target is unsigned, as `ksys_dup3` has it: a negative one is past any limit.
      -- No limit is past `sysctl_nr_open`, 2^20.
      else if arg 1 % 2 ^ 32 ≥ min limit (2 ^ 20) then some (errorOf Errno.ebadf) else none
    | .fcntl =>
      if arg 1 != 0 && arg 1 != 1030 then none
      else if arg 2 % 2 ^ 32 ≥ limit then some (errorOf Errno.einval)
      else if free (arg 2 % 2 ^ 32) ≥ limit then some (errorOf Errno.emfile) else none
    | _ => none

/-- The arguments of a call that are descriptors, which Linux takes as an `unsigned int` or an `int`: what is left of them in 32 bits
is the descriptor, whatever else a register of 64 bits has. A directory of the `*at` calls, which may be `AT_FDCWD`, isn't among them. -/
private def descriptorArguments : Call → List Nat
  | .read | .write | .pread | .pwrite | .readv | .writev | .preadv | .pwritev | .preadv2 | .pwritev2 | .close | .fstat | .lseek
  | .llseek | .dup | .fcntl | .ioctl | .getdents | .fchdir | .fchmod | .fchown | .ftruncate | .ftruncate64 | .fsync | .fdatasync
  | .syncfs | .flock | .fallocate | .fsetxattr | .fgetxattr | .flistxattr | .fremovexattr | .fstatfs | .fstatfs64 => [0]
  | .dup2 | .dup3 | .sendfile | .sendfile64 | .tee | .closeRange => [0, 1]
  | .splice | .copyFileRange => [0, 2]
  | _ => []

/-- The arguments of a call with its descriptors as Linux takes them: see `descriptorArguments`. -/
private def withDescriptors (call : Call) (args : List Nat) : List Nat :=
  match descriptorArguments call with
  | [] => args
  | places => args.mapIdx fun index value => if places.contains index then value % 2 ^ 32 else value

/-- What an `O_PATH` descriptor is refused of, as Linux's `fdget` refuses it where `fdget_raw` doesn't: what reads, writes, maps,
seeks, syncs, sizes, locks or asks it, `EBADF`, and of `fcntl` all but what duplicates it and its flags. What only names it (`fstat`,
`fchdir`, `close`, `dup` and a directory of the `*at` calls) goes on. -/
private def pathRefused (kernel : Kernel) (group : Nat) (call : Call) (args : List Nat) : Bool :=
  let arg (index : Nat) : Nat := args.getD index 0
  let named (index : Nat) : Bool := match kernel.openFileOf group (arg index % 2 ^ 32) with
    | .ok (_, file) => file.flags &&& Kernel.oPath != 0
    | .error _ => false
  match call with
  | .read | .write | .pread | .pwrite | .readv | .writev | .preadv | .pwritev | .preadv2 | .pwritev2 | .ioctl | .lseek | .llseek
  | .getdents | .fsync | .fdatasync | .syncfs | .ftruncate | .ftruncate64 | .fallocate | .fadvise64 | .fadvise6464 | .armFadvise6464
  | .flock | .fsetxattr | .fgetxattr | .flistxattr | .fremovexattr | .fchown => named 0
  -- What isn't anonymous maps a file.
  | .mmap | .mmap2 => arg 3 &&& 0x20 == 0 && named 4
  | .sendfile | .sendfile64 => named 0 || named 1
  | .splice | .tee | .copyFileRange => named 0 || named (if call == .tee then 1 else 2)
  | .fcntl => named 0 && ![0, 1, 2, 3, 1030].contains (arg 1 % 2 ^ 32)
  | _ => false

/-- What the io_urings of the process that runs have pending is done as far as it can be, as Linux does it without a call. -/
private def settleRings (machine : Machine) (emu : Emu) : IO Unit := do
  let machine := { machine with emu }
  let some task := (← emu.taskTable.get).find? (← thread emu) | return
  if task.status.isNone then Ring.settle (ringsOf machine (pollerOf machine) task.group (kernelCall machine emu)) emu task.group

/-- What a number of a system call has above it when it is a call of i386 that a process of 64 bits made by `int $0x80`: the
kernel serves it by the layouts of i386, in the memory of the process. -/
def compatMark : Nat := 2 ^ 32

private def serveKernelCalls (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu number args => do
    -- The compatibility entry: the call of i386 of that number, as the machine of i686 serves it, of the same kernel and memory.
    let (machine, number) :=
      if machine.architecture matches .x86_64 then
        if number ≥ compatMark && number < 2 * compatMark then ({ machine with architecture := .i686 }, number - compatMark)
        else (machine, number)
      else (machine, number)
    match machine.architecture.call number with
    -- What serveTaskCalls serves.
    | none => pure .default
    | some call =>
      machine.timers.entered emu
      let group := (← currentTask emu).group
      let args := withDescriptors call args
      if let some refused ← descriptorLimit machine group call args then return ← handOver machine emu refused
      if pathRefused (← machine.kernel.get) group call args then return ← handOver machine emu (errorOf Errno.ebadf)
      refreshProc machine emu group call args
      -- What it names of the directories of the host that the machine sees.
      if !(← machine.hostMounts.get).isEmpty then
        let kernel ← machine.kernel.get
        let cwd := kernel.cwdOf group
        for (index, relative) in pathArguments call do
          if let .ok path ← (readString emu (args.getD index 0)).toBaseIO then
            let base := if relative && !atCwd (args.getD (index - 1) 0) then
                (kernel.baseOf group (args.getD (index - 1) 0) false).toOption.getD cwd
              else cwd
            let (base, path) := kernel.pathIn group base path
            fromHost machine (Path.ofParts (Path.parts base path))
        if call == .getdents then
          if let .ok (_, file) := kernel.openFileOf group (args.getD 0 0) then
            if let some path := kernel.pathOfInode file.inode then fromHost machine path
      let mapped := !((← machine.kernel.get).process group).mappings.isEmpty
      -- A mapping of what is written has to hear of it. Otherwise a write is the only thing that a program does many of that gets longer with what it has done.
      let socket := (call == .write || call == .writev) && (← machine.kernel.get).isSocket group (args.getD 0 0)
      -- And what is written to an `eventfd` is counted, and to a terminal goes through it.
      let socket := socket || ((call == .write || call == .writev) && match (← machine.kernel.get).objectOf group (args.getD 0 0) with
        | .ok (_, _, { content := .eventfd .., .. }) | .ok (_, _, { content := .ptyMaster _, .. })
        | .ok (_, _, { content := .ptySlave _, .. }) => true
        | _ => false)
      -- And while `inotify` watches, what a write changes is found out from what it was before.
      let watching := !(← Notify.instancesOf machine.notifier (← machine.kernel.get)).isEmpty
      let args ← match checkedArguments machine.architecture (if ← takesTaggedAddresses emu then emu.config.untag else id) (ioReady (← machine.kernel.get) group call) call args with
        | .error errno => return ← handOver machine emu (errorOf errno)
        | .ok args => pure args
      let action ← match call, mapped || socket || watching with
      | .write, false => writeDirect machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0)
      | .writev, false =>
        try writeVectorDirect machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) catch error =>
          if ((toString error).splitOn "Emu address").length > 1 then pure (errorOf Errno.efault) else throw error
      | .pwrite, false =>
        -- Its offset, which on 32 bits is in two arguments in the order of the guest.
        let architecture := machine.architecture
        let offset := if architecture.bits == 64 then args.getD 3 0 else
          let (low, high) := if architecture.big then (args.getD (architecture.pairBase + 1) 0, args.getD architecture.pairBase 0)
            else (args.getD architecture.pairBase 0, args.getD (architecture.pairBase + 1) 0)
          high * 2 ^ 32 + low
        writeDirectAt machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) offset
      | _, _ => do
        let before ← machine.kernel.get
        -- An address of the program that a call can't read or write, wherever it is of what the call is given, an array of
        -- buffers or a name, is EFAULT, as it is of Linux, rather than what ends the run.
        let action ← try kernelCall machine emu call args catch error =>
          if ((toString error).splitOn "Emu address").length > 1 then pure (errorOf Errno.efault) else throw error
        -- A call that is over, rather than waiting to run again, has no site nor deadline left, which another at the same place,
        -- as `ipc` of i386 has all of its calls, would take as its own.
        if !(← Bap.Emu.stopped emu) then machine.timers.finish (← thread emu)
        refreshChanged machine emu before
        if [Call.close, .dup2, .dup3, .execve, .execveat].contains call then released machine
        if watching then
          let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
          if ← Notify.after machine.notifier machine.kernel group call args before action live then wakePipeReaders emu
        pure action
      brokenPipe machine emu group call args action
      fileTooBig machine emu group call action
      -- What an io_uring of the process has pending may be done now, as it is in Linux as soon as it can be.
      settleRings machine emu
      handOver machine emu action

/-- What is left: nothing else serves it, and it isn't there. -/
private def serveRest (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu _ _ => handOver machine emu (errorOf Errno.enosys)

/-- A register of x86 of its width, from the name of its 16 bits. -/
private def wordOf (wide : Nat) (name : String) : Bap.Var :=
  ⟨(if wide == 64 then "R" else "E") ++ name, .imm wide, 0, false⟩

/-- The bits of a word that are set. -/
private def bitsSet (positions : List Nat) : Nat := positions.foldl (fun word bit => word ||| (1 <<< bit)) 0

/-- The components of the state that XSAVE keeps past the legacy area and its header, each by its bit of XCR0, with its size and where
it is in the standard format: the upper halves of YMM0 to YMM15, the masks, the upper halves of ZMM0 to ZMM15, and ZMM16 to ZMM31. -/
private def xsaveComponents : List (Nat × Nat × Nat) := [(2, 256, 576), (5, 64, 1088), (6, 512, 1152), (7, 1024, 1664)]

/-- XCR0 as Linux has it of a processor of AVX-512: x87, SSE, AVX, the masks and both halves of what ZMM adds. -/
private def xcr0 : Nat := 0xe7

/-- What CPUID says of the processor: what the semantics have all of, so that a program that asks finds what runs. An AMD, of
x86-64 with AVX2, FMA, F16C, BMI, ADX, SHA, AES, PCLMULQDQ and their vector forms, GFNI, and AVX-512 with FP16 and BF16; the state
that XSAVE keeps, enabled by the system (OSXSAVE), with `xcr0`; RDTSCP, RDPID, CLZERO, FSGSBASE. What it hasn't, as RDRAND, TSX, the
keys of protection, 3DNow!, XOP, or what AVX10.2 adds, is an invalid instruction where a program runs it. -/
private def cpuidOf (leaf sub : Nat) : Nat × Nat × Nat × Nat :=
  match leaf with
  -- AuthenticAMD: libc reads the caches of an Intel from leaves that this doesn't have.
  | 0 => (0xd, 0x68747541, 0x444d4163, 0x69746e65)
  -- SSE3, PCLMULQDQ, SSSE3, FMA, CMPXCHG16B, SSE4.1, SSE4.2, MOVBE, POPCNT, AES, XSAVE, OSXSAVE, AVX, F16C
  | 1 => (0x800f00, 0, bitsSet [0, 1, 9, 12, 13, 19, 20, 22, 23, 25, 26, 27, 28, 29], 0x07888f9f)
  | 7 =>
    match sub with
    -- FSGSBASE, BMI1, AVX2, BMI2, ERMS, AVX512F, AVX512DQ, ADX, AVX512IFMA, CLFLUSHOPT, AVX512CD, SHA, AVX512BW, AVX512VL;
    -- AVX512VBMI, VBMI2, GFNI, VAES, VPCLMULQDQ, VNNI, BITALG, VPOPCNTDQ, RDPID; AVX512-FP16
    | 0 => (1, bitsSet [0, 3, 5, 8, 9, 16, 17, 19, 21, 23, 28, 29, 30, 31], bitsSet [1, 6, 8, 9, 10, 11, 12, 14, 22], bitsSet [23])
    -- AVX512-BF16
    | 1 => (bitsSet [5], 0, 0, 0)
    | _ => (0, 0, 0, 0)
  | 0xd =>
    match sub with
    | 0 => (xcr0, 2688, 2688, 0)
    -- XSAVEOPT and XSAVEC
    | 1 => (3, 2688, 0, 0)
    | index => match xsaveComponents.find? (·.1 == index) with
      | some (_, size, offset) => (size, offset, 0, 0)
      | none => (0, 0, 0, 0)
  | 0x80000000 => (0x80000008, 0, 0, 0)
  -- LAHF, LZCNT and PREFETCHW, and SYSCALL, NX, RDTSCP and long mode
  | 0x80000001 => (0, 0, bitsSet [0, 5, 8], 0x20100800 ||| bitsSet [27])
  -- addresses of 48 bits, and CLZERO
  | 0x80000008 => (0x3030, 1, 0, 0)
  | _ => (0, 0, 0, 0)

/-- What a program asks of the processor of x86: CPUID, the time stamp counter, and the state that FXSAVE and XSAVE keep. -/
private def serveCpu (emu : Emu) (kernel : IO.Ref Kernel) (wide : Nat) : IO Unit := do
  -- The registers, and how many of the vector ones there are.
  let a := wordOf wide "AX"
  let (b, c, d) := (wordOf wide "BX", wordOf wide "CX", wordOf wide "DX")
  let vectors := if wide == 64 then 16 else 8
  let value (emu : Emu) (var : Bap.Var) : IO Nat := do
    match Value.asBits (← reg emu var) with
    | .ok bits => pure bits.2.toNat
    | .error _ => pure 0
  let _ ← onIntrinsic emu "cpuid" fun current _ => do
    let (eax, ebx, ecx, edx) := cpuidOf ((← value current a) % 2 ^ 32) ((← value current c) % 2 ^ 32)
    -- In the registers: what follows the intrinsic in its code doesn't run after a hook has served it.
    for (var, value) in [(a, eax), (b, ebx), (c, ecx), (d, edx)] do
      setReg current var (bits wide value)
    pure .proceed
  -- What ld.so saves around resolving a function. The layout is that of the manual: the controls, MXCSR, ST and XMM. The rest of
  -- the x87 state, as what instruction faulted, isn't kept.
  let target (emu : Emu) : IO Nat := value emu ⟨"intrinsic:x0", .imm wide, 0, false⟩
  let zmm (index : Nat) : Bap.Var := ⟨s!"ZMM{index}", .imm 512, 0, false⟩
  -- The legacy area: the words of x87 and its registers, MXCSR, and XMM.
  let legacy (emu : Emu) : IO ByteArray := do
    let control ← value emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩
    let status ← value emu ⟨"FPU_STATUS", .imm 16, 0, false⟩
    let tags ← value emu ⟨"FPU_TAG", .imm 16, 0, false⟩
    let mxcsr ← value emu ⟨"MXCSR", .imm 32, 0, false⟩
    -- The abridged tag has a bit for each register, set unless the full tag says that it is empty.
    let abridged := (List.range 8).foldl (fun out index => if (tags >>> (2 * index)) % 4 == 3 then out else out + 2 ^ index) 0
    let mut image := Abi.bytesOf 2 control ++ Abi.bytesOf 2 status ++ Abi.bytesOf 2 abridged ++ Abi.bytesOf 18 0 ++
      Abi.bytesOf 4 mxcsr ++ Abi.bytesOf 4 0xffff
    for index in List.range 8 do
      image := image ++ Abi.bytesOf 16 (← value emu ⟨s!"ST{index}", .imm 80, 0, false⟩)
    for index in List.range vectors do
      image := image ++ Abi.bytesOf 16 ((← value emu (zmm index)) % 2 ^ 128)
    pure image
  let fieldOf (image : ByteArray) (offset size : Nat) : Nat :=
    (List.range size).foldl (fun out index => out + (image.get! (offset + index)).toNat * 256 ^ index) 0
  -- Bits `low` to `low + size` of a vector register, as given.
  let setPart (emu : Emu) (index low size part : Nat) : IO Unit := do
    let old ← value emu (zmm index)
    setReg emu (zmm index) (bits 512 (old - (old >>> low % 2 ^ size) * 2 ^ low + (part % 2 ^ size) * 2 ^ low))
  let loadLegacy (emu : Emu) (image : ByteArray) (x87 mxcsr sse : Bool) : IO Unit := do
    let field := fieldOf image
    if x87 then
      setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 (field 0 2))
      -- The summary of an exception that is pending is of the words that are loaded.
      let status := field 2 2 &&& 0x7f7f
      setReg emu ⟨"FPU_STATUS", .imm 16, 0, false⟩ (bits 16 (if status &&& (0x3f - field 0 2 % 64) != 0 then status ||| 0x8080 else status))
      let abridged := field 4 1
      setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 ((List.range 8).foldl (fun out index =>
        if (abridged >>> index) % 2 == 1 then out else out + 3 * 4 ^ index) 0))
      for index in List.range 8 do
        setReg emu ⟨s!"ST{index}", .imm 80, 0, false⟩ (bits 80 (field (32 + 16 * index) 10))
    if mxcsr then setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 (field 24 4))
    if sse then
      for index in List.range vectors do
        setPart emu index 0 128 (field (160 + 16 * index) 16)
  for name in ["fxsave", "fxsave64"] do
    let _ ← onIntrinsic emu name fun current _ => do
      -- What is after the registers, reserved and for the program's own use, isn't written.
      writeGuest current (← target current) (← legacy current)
      pure .proceed
  for name in ["fxrstor", "fxrstor64"] do
    let _ ← onIntrinsic emu name fun current _ => do
      loadLegacy current (← read current (← target current) 512) true true true
      pure .proceed
  -- XSAVE, XSAVEOPT and XSAVEC, and XRSTOR: of the components that EDX:EAX asks for of those of `xcr0`. Each component is said
  -- to be in use, which a processor may say of any. XSAVEC packs what is past the header, in the order of the components, and says
  -- so in XCOMP_BV; XRSTOR takes either format, and what the area doesn't have of what is asked for is as a program starts with.
  let component (emu : Emu) (index : Nat) : IO ByteArray := do
    let mut out := ByteArray.empty
    match index with
    | 2 => for register in List.range 16 do out := out ++ Abi.bytesOf 16 ((← value emu (zmm register)) >>> 128 % 2 ^ 128)
    | 5 => for register in List.range 8 do out := out ++ Abi.bytesOf 8 (← value emu ⟨s!"K{register}", .imm 64, 0, false⟩)
    | 6 => for register in List.range 16 do out := out ++ Abi.bytesOf 32 ((← value emu (zmm register)) >>> 256)
    | _ => for register in List.range 16 do out := out ++ Abi.bytesOf 64 (← value emu (zmm (16 + register)))
    pure out
  let setComponent (emu : Emu) (index : Nat) (image : Option ByteArray) : IO Unit := do
    let field (offset size : Nat) : Nat := match image with
      | some image => fieldOf image offset size
      | none => 0
    match index with
    | 2 => for register in List.range vectors do setPart emu register 128 128 (field (16 * register) 16)
    | 5 => for register in List.range 8 do setReg emu ⟨s!"K{register}", .imm 64, 0, false⟩ (bits 64 (field (8 * register) 8))
    | 6 => for register in List.range vectors do setPart emu register 256 256 (field (32 * register) 32)
    | _ => if wide == 64 then for register in List.range 16 do setReg emu (zmm (16 + register)) (bits 512 (field (64 * register) 64))
  let requested (emu : Emu) : IO Nat := do
    let high ← value emu ⟨"intrinsic:x1", .imm 32, 0, false⟩
    let low ← value emu ⟨"intrinsic:x2", .imm 32, 0, false⟩
    pure ((high * 2 ^ 32 + low) &&& xcr0)
  -- Where a component is past the header: by the standard format, or packed after those of `packed` before it.
  let offsetOf (packed : Option Nat) (index : Nat) : Nat := match packed with
    | none => ((xsaveComponents.find? (·.1 == index)).map (·.2.2)).getD 576
    | some present => xsaveComponents.foldl (fun offset (other, size, _) =>
        if other < index && present.testBit other then offset + size else offset) 576
  for (name, compact) in [("xsave", false), ("xsave64", false), ("xsaveopt", false), ("xsaveopt64", false), ("xsavec", true), ("xsavec64", true)] do
    let _ ← onIntrinsic emu name fun current _ => do
      let address ← target current
      let wanted ← requested current
      let image ← legacy current
      if wanted.testBit 0 then
        writeGuest current address (image.extract 0 24)
        writeGuest current (address + 32) (image.extract 32 160)
      if wanted &&& 6 != 0 then writeGuest current (address + 24) (image.extract 24 32)
      if wanted.testBit 1 then writeGuest current (address + 160) (image.extract 160 image.size)
      for (index, _, _) in xsaveComponents do
        if wanted.testBit index then
          writeGuest current (address + offsetOf (if compact then some wanted else none) index) (← component current index)
      if compact then
        writeGuest current (address + 512) (Abi.bytesOf 8 wanted ++ Abi.bytesOf 8 (wanted + 2 ^ 63) ++ Abi.bytesOf 48 0)
      else
        let header ← read current (address + 512) 8
        let before := fieldOf header 0 8
        writeGuest current (address + 512) (Abi.bytesOf 8 ((before &&& (2 ^ 64 - 1 - wanted)) ||| wanted))
      pure .proceed
  for name in ["xrstor", "xrstor64"] do
    let _ ← onIntrinsic emu name fun current _ => do
      let address ← target current
      let wanted ← requested current
      let header ← read current (address + 512) 16
      let present := fieldOf header 0 8
      let format := fieldOf header 8 8
      let packed := if format.testBit 63 then some format else none
      let image ← read current address 512
      let fresh := Abi.bytesOf 2 0x37f ++ Abi.bytesOf 510 0
      if wanted.testBit 0 then loadLegacy current (if present.testBit 0 then image else fresh) true false false
      if wanted &&& 6 != 0 then loadLegacy current image false true false
      if wanted.testBit 1 then loadLegacy current (if present.testBit 1 then image else fresh) false false true
      for (index, size, _) in xsaveComponents do
        if wanted.testBit index then
          if present.testBit index then
            setComponent current index (some (← read current (address + offsetOf packed index) (size)))
          else setComponent current index none
      pure .proceed
  -- It counts up, so that what measures with it sees time pass. RDTSCP says the processor too, the first one.
  for name in ["rdtsc", "rdtscp"] do
    let _ ← onIntrinsic emu name fun current _ => do
      let now := (← kernel.get).cycles
      kernel.modify fun kernel => { kernel with cycles := now + 1000 }
      setReg current a (bits wide (now % 2 ^ 32))
      setReg current d (bits wide (now / 2 ^ 32))
      if name == "rdtscp" then setReg current c (bits wide 0)
      pure .proceed
  pure ()

/-- What the semantics of an architecture call an instruction that is undefined where a program runs, and the `si_code` and the rest of
the `siginfo_t` that Linux raises `SIGILL` with for it at an address:
- AArch64, `do_el0_undef`; ARM, `do_undefinstr`; RISC-V, `do_trap_insn_illegal`; PowerPC, `program_check_exception`: `ILL_ILLOPC`, at
  the instruction (qemu says `ILL_ILLOPN` on ARM, which Linux doesn't);
- x86, `exc_invalid_op` of `ud2` and `ud1`: `ILL_ILLOPN`, at the instruction;
- MIPS, `do_ri` and `do_cpu`: `force_sig`, which is `SI_KERNEL` with no address. -/
private def illegalOf (architecture : Architecture) : String × (Nat → Nat × SignalDetail) :=
  match architecture with
  | .x86_64 | .i686 => ("__ud2", fun pc => (2, .fault pc))
  | .mips .. => ("undefined-instruction", fun _ => (0x80, .sent 0 0 0))
  | _ => ("undefined-instruction", fun pc => (1, .fault pc))

/-- Whether the undefined instruction at `pc` of a thread of ARM is one that Linux takes as a breakpoint, by the hooks of
`arch/arm/kernel/ptrace.c` on the exception of undefined instructions, which debuggers put where they break: `arm_break_hook`, the
word `0x07f001f0` under any condition in ARM state, and in Thumb state `thumb_break_hook`, the halfword `0xde01`, and
`thumb2_break_hook`, `0xf7f0 0xa000`. `break_trap` sends `SIGTRAP` of `TRAP_BRKPT` at the instruction for them, where any other
undefined instruction is `SIGILL`. What can't be read isn't one. -/
private def armBreakpoint (emu : Emu) (pc : Nat) : IO Bool := do
  let thumb ← match ← (reg emu ⟨"ISET", .imm 1, 0, false⟩).toBaseIO with
    | .ok (.bits value) => pure (value.toNat == 1)
    | _ => pure false
  let word (size : Nat) : IO (Option Nat) := do
    match ← (read emu pc size).toBaseIO with
    | .ok bytes => pure (some ((List.range size).foldl (fun word index => word + bytes[index]!.toNat * 256 ^ index) 0))
    | .error _ => pure none
  if thumb then
    match ← word 2 with
    | some 0xde01 => pure true
    | some 0xf7f0 => pure ((← word 4) == some 0xa000f7f0)
    | _ => pure false
  else pure (((← word 4).map fun word => word &&& 0x0fffffff == 0x07f001f0).getD false)

/-- An instruction that is undefined where a program runs raises `SIGILL` at it, forced as Linux forces it: if the thread blocks it or its
process ignores it, the process ends of it. A handler sees the instruction as where the thread was, or, of one in the delay slot of a
branch, the branch, as MIPS says in EPC with BD, and goes on after it only if it says so. This is the one place that raises it, and
nothing outside the machine serves what the semantics call the instruction. -/
private def serveIllegalInstructions (machine : Machine) (emu : Emu) : IO Unit := do
  let (name, info) := illegalOf machine.architecture
  let _ ← onIntrinsic emu name fun current pc => do
    let tid ← thread current
    let group := (← currentTask current).group
    let (code, detail) := info pc
    -- Of ARM, the undefined instructions that Linux has as breakpoints are `SIGTRAP` of `TRAP_BRKPT` at them.
    let (signal, code) := if machine.architecture == .arm && (← armBreakpoint current pc) then (machine.signals.trapNumber, 1)
      else (machine.signals.illNumber, code)
    machine.signals.force current tid group ⟨signal, code, detail⟩
    let resume := match ← current.pendingRef.get with
      | some pending => pending.branch
      | none => pc
    machine.signals.deliverAt current resume
    pure .proceed
  pure ()

/-- What a trap of an instruction raises: the signal, its `si_code` and the rest of its `siginfo_t`, and where the thread is then. -/
private structure Trap where
  signal : Nat
  code : Nat
  detail : SignalDetail
  resume : Nat

/-- The intrinsics that the semantics of x86 name for instructions of extensions that the processor of the machine hasn't, by
`cpuidOf`, each of which is an invalid instruction where a program runs it: the random numbers, RDRAND and RDSEED; RDPRU; WAITPKG,
TPAUSE, UMONITOR and UMWAIT; PTWRITE; ENQCMD; the user's registers of the system, URDMSR and UWRMSR; SM3, SM4 and SHA-512; the
floating point of the tiles of AMX; and of AVX10.2, the arithmetic of BF16 and the conversions to the formats of 8 bits. -/
private def absentOfX86 : List String :=
  ["rdrand", "rdseed", "rdpru", "rdpru_valid", "tpause", "umonitor", "umwait", "ptwrite", "enqcmd", "enqcmds", "urdmsr", "uwrmsr",
    "vsm3msg1", "vsm3msg2", "vsm3rnds2", "sm4key4", "sm4rnds4", "vsha512msg1", "vsha512msg2", "vsha512rnds2",
    "tcmmimfp16ps", "tcmmrlfp16ps", "tdpbf16ps", "tdpbf8ps", "tdpbhf8ps", "tdpfp16ps", "tdphbf8ps", "tdphf8ps",
    "cast_ibs_rne_bfloat_16_16", "cast_ibs_rtz_bfloat_16_16", "cast_iubs_rne_bfloat_16_16", "cast_iubs_rtz_bfloat_16_16",
    "fadd_rne_bfloat_16", "fsub_rne_bfloat_16", "fmul_rne_bfloat_16", "fdiv_rne_bfloat_16", "fsqrt_rne_bfloat_16", "fmad_rne_bfloat_16",
    "fgetexp_rne_bfloat_16", "fgetmant_rne_bfloat_16", "fminmax_rne_bfloat_16", "fpclass_rne_bfloat_16", "frcp_rne_bfloat_16",
    "freduce_rne_bfloat_16", "frndscale_rne_bfloat_16", "frsqrt_rne_bfloat_16", "fscalef_rne_bfloat_16", "forder_bfloat_16",
    "forders_bfloat_16", "is_nan_bfloat_16",
    "vcvt2ph2bf8_rne", "vcvt2ph2bf8s_rne", "vcvt2ph2hf8_rne", "vcvt2ph2hf8s_rne", "vcvtbiasph2bf8_rne", "vcvtbiasph2bf8s_rne",
    "vcvtbiasph2hf8_rne", "vcvtbiasph2hf8s_rne", "vcvthf82ph", "vcvtph2bf8_rne", "vcvtph2bf8s_rne", "vcvtph2hf8_rne", "vcvtph2hf8s_rne"]

/-- The `si_code` of `SIGFPE` that `math_error` of x86 has for the exceptions that are raised and not masked, as their flags: invalid 7,
division by zero 3, overflow 4, underflow or a denormal 5, inexact 6. -/
private def mathErrorCode (raised : Nat) : Nat :=
  if raised &&& 0x01 != 0 then 7 else if raised &&& 0x04 != 0 then 3 else if raised &&& 0x08 != 0 then 4
  else if raised &&& 0x12 != 0 then 5 else if raised &&& 0x20 != 0 then 6 else 7

/-- What the semantics of an architecture call the instructions that trap where a program runs, other than the undefined ones, and what
Linux raises for each at an address, which is where the thread is then unless said. `SI_KERNEL`, 0x80, is of `force_sig`, which gives no
address.
- x86, `int3`, `exc_int3`: `SIGTRAP` of `SI_KERNEL`, after the instruction, as it is a trap; `hlt`, which is privileged,
  `exc_general_protection`: `SIGSEGV` of `SI_KERNEL`; a division without a quotient, `exc_divide_error`: `SIGFPE` of `FPE_INTDIV` at it;
- AArch64, `brk`, `do_el0_brk64`; RISC-V, `ebreak`, `do_trap_break`; PowerPC, the traps, `program_check_exception`: `SIGTRAP` of
  `TRAP_BRKPT` at the instruction;
- ARM, `bkpt`, `hw_breakpoint_pending`, which doesn't know it: `SIGTRAP` of `TRAP_HWBKPT` at the instruction, as `hook_ifault_code` of
  the debug exception says (qemu says `TRAP_BRKPT`);
- MIPS, `break`, `do_bp`, and the traps, `do_tr`, by the code that the instruction has, of which those of a division, which compilers
  put after one, are `SIGFPE`: `do_trap_or_bp`; and an addition or a subtraction that overflows, `add`, `addi`, `sub` and those of
  doublewords, `do_ov`: `SIGFPE` of `FPE_INTOVF` at the instruction;
- MIPS, a write of FCSR that leaves a cause whose exception is enabled, or that of what isn't implemented, `do_fpe`: `SIGFPE` at the
  instruction, of the code of the first of the causes that it has, invalid, division by zero, overflow, underflow and inexact, or
  `FPE_FLTUNK` of none of them (`force_fcr31_sig`);
- PowerPC, an instruction or a special purpose register of the supervisor, the privileged instruction type of the program interrupt,
  `program_check_exception`: `SIGILL` of `ILL_PRVOPC` at the instruction; a `hashchk` whose hash isn't what is stored, the trap
  type of it, which Linux has as `SIGILL` of `ILL_ILLOPN` there; and `paste.` to memory that isn't of an accelerator, a data storage
  interrupt of `DSISR_BAD_COPYPASTE`, `SIGBUS` of `BUS_OBJERR` at the address. -/
private def trapsOf (machine : Machine) : List (String × (Emu → Nat → IO Trap)) :=
  let signals := machine.signals
  let breakpoint (code : Nat) : Emu → Nat → IO Trap := fun _ pc => pure ⟨signals.trapNumber, code, .fault pc, pc⟩
  match machine.architecture with
  | .x86_64 | .i686 =>
    let invalid : Emu → Nat → IO Trap := fun _ pc => pure ⟨signals.illNumber, 2, .fault pc, pc⟩
    let first : List (String × (Emu → Nat → IO Trap)) :=
    [("breakpoint", fun _ pc => pure ⟨signals.trapNumber, 0x80, .sent 0 0 0, pc + 1⟩),
     ("hlt", fun _ pc => pure ⟨signals.segvNumber, 0x80, .sent 0 0 0, pc⟩),
     -- What is privileged, `in`, `out`, `cli`, `rdmsr`, a move of a control register, `iret` and the like, a selector that isn't
     -- the program's, and `int` to a gate that isn't for it: a general protection fault, `exc_general_protection`, which is
     -- `SIGSEGV` of `SI_KERNEL` at the instruction.
     ("general-protection", fun _ pc => pure ⟨signals.segvNumber, 0x80, .sent 0 0 0, pc⟩),
     -- `int $3`, of two bytes, is the breakpoint, and `int $4` and `into` the overflow trap, `exc_overflow`, `SIGSEGV` of
     -- `SI_KERNEL`: traps, after the instruction.
     ("interrupt-3", fun _ pc => pure ⟨signals.trapNumber, 0x80, .sent 0 0 0, pc + 2⟩),
     ("interrupt-4", fun _ pc => pure ⟨signals.segvNumber, 0x80, .sent 0 0 0, pc + 2⟩),
     ("into", fun _ pc => pure ⟨signals.segvNumber, 0x80, .sent 0 0 0, pc + 1⟩),
     -- `int1`, the byte `f1`, is the debug exception with nothing in DR6, `exc_debug_user`: `SIGTRAP` of `TRAP_BRKPT` after it.
     ("int1", fun _ pc => pure ⟨signals.trapNumber, 1, .fault (pc + 1), pc + 1⟩),
     ("divide-error", fun _ pc => pure ⟨signals.fpeNumber, 1, .fault pc, pc⟩)]
    -- What the semantics have of the instructions of what the processor of `cpuidOf` hasn't: an invalid instruction, each.
    let absent : List (String × (Emu → Nat → IO Trap)) := absentOfX86.map fun name => (name, invalid)
    let floating : List (String × (Emu → Nat → IO Trap)) := [-- An exception of floating point that isn't masked, `math_error`: `SIGFPE` at the instruction, with the code of the first
     -- of what is raised and not masked: invalid, division by zero, overflow, underflow or a denormal, and inexact. Of SSE, #XM, it
     -- is the instruction that raised it, by MXCSR; of x87, #MF, the next one of x87 that waits, by the status and control words.
     ("float-exception", fun emu pc => do
        let mxcsr := match Value.asBits (← reg emu ⟨"MXCSR", .imm 32, 0, false⟩) with
          | .ok value => value.2.toNat
          | .error _ => 0x1f80
        pure ⟨signals.fpeNumber, mathErrorCode (mxcsr &&& (0x3f - (mxcsr >>> 7) % 64)), .fault pc, pc⟩),
     ("x87-exception", fun emu pc => do
        let word (name : String) (otherwise : Nat) : IO Nat := do
          match Value.asBits (← reg emu ⟨name, .imm 16, 0, false⟩) with
          | .ok value => pure value.2.toNat
          | .error _ => pure otherwise
        let status ← word "FPU_STATUS" 0
        let control ← word "FPU_CONTROL" 0x37f
        pure ⟨signals.fpeNumber, mathErrorCode (status &&& (0x3f - control % 64)), .fault pc, pc⟩)]
    first ++ absent ++ floating
  | .arm => [("breakpoint", breakpoint 4)]
  | .mips _ big _ =>
    -- The code of a `break` is of 20 bits, whose halves the kernel swaps if the high one is set, as assemblers put a code in either;
    -- that of a trap is of 10.
    let raise (isBreak : Bool) : Emu → Nat → IO Trap := fun emu pc => do
      let bytes ← read emu pc 4
      let bytes := if big then bytes.toList else bytes.toList.reverse
      let word := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
      let code := if isBreak then
          let code := (word >>> 6) % 2 ^ 20
          if code ≥ 2 ^ 10 then (code % 2 ^ 10) * 2 ^ 10 + code / 2 ^ 10 else code
        else (word >>> 6) % 2 ^ 10
      if code == 6 || code == 7 then pure ⟨signals.fpeNumber, if code == 7 then 1 else 2, .fault pc, pc⟩
      else if isBreak && code != 12 && code != 514 then pure ⟨signals.trapNumber, 1, .fault 0, pc⟩
      else pure ⟨signals.trapNumber, 0x80, .sent 0 0 0, pc⟩
    [("breakpoint", raise true), ("trap", raise false),
     ("integer-overflow", fun _ pc => pure ⟨signals.fpeNumber, 2, .fault pc, pc⟩),
     ("floating-point-exception", fun emu pc => do
        -- The causes that FCSR has, of which the first of these says the code, and of which those that are enabled, and that of
        -- what isn't implemented, are cleared before the signal, as `do_fpe` clears them.
        let wide := machine.architecture.bits
        let fcsr := match Value.asBits (← reg emu ⟨"FCSR", .imm wide, 0, false⟩) with
          | .ok value => value.2.toNat
          | .error _ => 0
        let cause := (fcsr >>> 12) % 64
        let code := if cause.testBit 4 then 7 else if cause.testBit 3 then 3 else if cause.testBit 2 then 4
          else if cause.testBit 1 then 5 else if cause.testBit 0 then 6 else 14
        let taken := cause &&& (((fcsr >>> 7) % 32) ||| 32)
        setReg emu ⟨"FCSR", .imm wide, 0, false⟩ (bits wide (fcsr - (taken <<< 12)))
        pure ⟨signals.fpeNumber, code, .fault pc, pc⟩)]
  | .powerpc _ big =>
    -- Where `paste.` would paste: (RA|0) + (RB), of the fields of the instruction.
    let pasteAddress : Emu → Nat → IO Nat := fun emu pc => do
      let bytes := (← read emu pc 4).toList
      let word := (if big then bytes else bytes.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0
      let wide := machine.architecture.bits
      let register (number : Nat) : IO Nat := do
        match Value.asBits (← reg emu ⟨s!"R{number}", .imm wide, 0, false⟩) with
        | .ok value => pure value.2.toNat
        | .error _ => pure 0
      let base ← if (word >>> 16) % 32 == 0 then pure 0 else register ((word >>> 16) % 32)
      pure ((base + (← register ((word >>> 11) % 32))) % 2 ^ wide)
    [("trap", breakpoint 1), ("privileged-instruction", fun _ pc => pure ⟨signals.illNumber, 5, .fault pc, pc⟩),
     ("hash-check", fun _ pc => pure ⟨signals.illNumber, 2, .fault pc, pc⟩),
     ("paste-wrong-memory", fun emu pc => do pure ⟨7, 3, .fault (← pasteAddress emu pc), pc⟩)]
  | .aarch64 | .riscv64 | .riscv32 => [("breakpoint", breakpoint 1)]

/-- An instruction that traps where a program runs raises its signal, forced as that of an undefined one is. A handler sees where Linux
has the thread, the branch for a trap in a delay slot, and goes on from there when it returns: at a breakpoint of x86 that is after it,
and elsewhere the instruction, which traps again unless the handler moved the thread. -/
private def serveTraps (machine : Machine) (emu : Emu) : IO Unit := do
  for (name, trapOf) in trapsOf machine do
    let _ ← onIntrinsic emu name fun current pc => do
      let tid ← thread current
      let group := (← currentTask current).group
      let pending ← current.pendingRef.get
      let trap ← trapOf current pc
      -- The exception program counter of MIPS is the branch, and what it says faulted is that too.
      let (detail, resume) := match pending, trap.detail with
        | some pending, .fault address => (.fault (if address == pc then pending.branch else address), pending.branch)
        | some pending, detail => (detail, pending.branch)
        | none, detail => (detail, trap.resume)
      machine.signals.force current tid group ⟨trap.signal, trap.code, detail⟩
      machine.signals.deliverAt current resume
      -- A handler of an exception of floating point of x86 runs with the state of floating point of a program that starts, as
      -- Linux gives every handler (`fpu__clear_user_states`), without which the exception that is pending would be raised in it
      -- again.
      if (machine.architecture matches .x86_64 | .i686) && (name == "float-exception" || name == "x87-exception") then
        setReg current ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 0x37f)
        setReg current ⟨"FPU_STATUS", .imm 16, 0, false⟩ (bits 16 0)
        setReg current ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 0xffff)
        setReg current ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 0x1f80)
      pure .proceed

/-- Registers hold zeros at the start, as the kernel leaves them, but for the state of the floating point units. -/
private def resetRegisters (emu : Emu) : Architecture → IO Unit
  | .aarch64 => do
    for index in List.range 31 do
      setReg emu (word s!"X{index}") (bits 64 0)
    for name in ["SP", "TPIDR_EL0", "TPIDRRO_EL0", "CNTVCT_EL0"] do
      setReg emu (word name) (bits 64 0)
    for name in ["NF", "ZF", "CF", "VF"] do
      setReg emu ⟨name, .imm 1, 0, false⟩ (bits 1 0)
    for index in List.range 32 do
      setReg emu ⟨s!"Q{index}", .imm 128, 0, false⟩ (bits 128 0)
    -- The predicates of SVE and FFR, of a bit for each byte of a vector of 128 bits, as the lifter has them: zero, as Linux's
    -- `sve_flush_live` leaves them, rather than nothing, which the first instruction that reads one would find unbound.
    for name in (List.range 16).map (s!"P{·}") ++ ["FFR"] do
      setReg emu ⟨name, .imm 16, 0, false⟩ (bits 16 0)
    for name in ["FPCR", "FPSR"] do
      setReg emu ⟨name, .imm 32, 0, false⟩ (bits 32 0)
    -- Addresses with a tag aren't taken until the program asks, as `flush_tagged_addr_state` leaves it.
    setReg emu taggedAddresses (bits 1 0)
    -- SME, as a program starts, out of the streaming mode and with ZA off, as `fpsimd_flush_thread` leaves it: what ZA and ZT0 hold
    -- is zeros, which is what turning ZA on makes of them.
    for (name, width) in Target.LLVMLift.aarch64SmeRegisters do
      setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
  | .riscv64 | .riscv32 => do
    let wide ← wordWidth emu
    for index in List.range 32 do
      setReg emu ⟨s!"X{index}", .imm wide, 0, false⟩ (bits wide 0)
      setReg emu (word s!"F{index}") (bits 64 0)
    for name in ["FCSR", "VXRM"] do
      setReg emu ⟨name, .imm 32, 0, false⟩ (bits 32 0)
  | .powerpc wide _ => do
    for (name, width) in Target.LLVMLift.powerpcRegisters wide do
      setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
    -- The priority that Linux starts a program at, medium low (`INIT_PPR`).
    if wide == 64 then setReg emu ⟨"PPR", .imm 64, 0, false⟩ (bits 64 (3 <<< 50))
  | .mips wide _ release6 => do
    for index in List.range 32 do
      setReg emu ⟨s!"R{index}", .imm wide, 0, false⟩ (bits wide 0)
      let float := if wide == 64 || release6 then 64 else 32
      setReg emu ⟨s!"F{index}", .imm float, 0, false⟩ (bits float 0)
    for name in ["HI", "LO", "USERLOCAL", "FCSR"] do
      setReg emu ⟨name, .imm wide, 0, false⟩ (bits wide 0)
    for index in List.range 8 do
      setReg emu ⟨s!"FCC{index}", .imm 1, 0, false⟩ (bits 1 0)
  | .arm => do
    -- Without `ISET`, which says what comes first.
    for (name, width) in Target.LLVMLift.arm32Registers do
      if name != "ISET" then setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
  | .i686 => do
    for (name, width) in Target.LLVMLift.x8632Registers do
      setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
    for name in Target.LLVMLift.x86Flags do
      setReg emu ⟨name, .imm 1, 0, false⟩ (bits 1 (if name == "EFLAGS_1" || name == "IF" then 1 else 0))
    -- The selectors of a process of 32 bits under a kernel of 64, `__USER32_CS` and `__USER_DS`, as `start_thread` of the
    -- compatibility has them.
    for (name, selector) in [("CS", 0x23), ("DS", 0x2b), ("ES", 0x2b), ("FS", 0), ("GS", 0), ("SS", 0x2b)] do
      setReg emu ⟨name, .imm 16, 0, false⟩ (bits 16 selector)
    setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 0x37f)
    setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 0xffff)
    setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 0x1f80)
  | .x86_64 => do
  for name in ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15",
      "FS_BASE", "GS_BASE"] do
    setReg emu (word name) (bits 64 0)
  -- Every bit of the flags, which `pushfq` reads all of: the one that is always set, and that interrupts are let in.
  for name in Target.LLVMLift.x86Flags do
    setReg emu ⟨name, .imm 1, 0, false⟩ (bits 1 (if name == "EFLAGS_1" || name == "IF" then 1 else 0))
  for index in List.range 32 do
    for (name, width) in [(s!"XMM{index}", 128), (s!"YMM{index}", 256), (s!"ZMM{index}", 512)] do
      setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
  for index in List.range 8 do
    setReg emu ⟨s!"ST{index}", .imm 80, 0, false⟩ (bits 80 0)
    -- The masks of AVX-512 and the registers of MMX, which nothing has written.
    setReg emu ⟨s!"K{index}", .imm 64, 0, false⟩ (bits 64 0)
    setReg emu ⟨s!"MM{index}", .imm 64, 0, false⟩ (bits 64 0)
  -- The selectors of a process of 64 bits, `__USER_CS` and `__USER_DS` of `start_thread`; the others are null.
  for (name, selector) in [("CS", 0x33), ("SS", 0x2b), ("DS", 0), ("ES", 0), ("FS", 0), ("GS", 0)] do
    setReg emu ⟨name, .imm 16, 0, false⟩ (bits 16 selector)
  setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 0x37f)
  setReg emu ⟨"FPU_STATUS", .imm 16, 0, false⟩ (bits 16 0)
  setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 0xffff)
  setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 0x1f80)

/-- The segments of a file in pages at `base`, as the kernel maps them, one after the other over what is there: the pages of
a segment hold the file, and zeros after what of it is in the file when it is larger in memory. Returns where they end. A
page that two segments share is that of the later one, with its bytes of the file and its protection. The pages of a segment after
those that have something of the file are zeros that take nothing of the host until they are written, as Linux maps them, whatever
the file says their size is. -/
private def mapProgram (emu : Emu) (data : ByteArray) (program : Elf.Program) (base : Nat) : IO Nat := do
  let sorted := program.segments.toArray.qsort fun left right => left.address < right.address
  -- Each with whether it is zeros that nothing was written to.
  let mut regions : Array (Region × Bool) := #[]
  let mut top := 0
  for segment in sorted do
    let first := base + segment.address
    let start := pageDown first
    let stop := pageUp (first + segment.memorySize)
    if start < stop then
      let fileStop := if segment.memorySize > segment.fileSize then first + segment.fileSize
        else pageUp (first + segment.fileSize)
      -- Where the pages that have something of the file end.
      let fileEnd := min stop (pageUp fileStop)
      let from_ := segment.offset - (first - start)
      let bytes := data.extract from_ (from_ + (fileStop - start))
      let bytes := bytes ++ Bap.zeroBytes (fileEnd - start - bytes.size)
      -- What it covers of those before it is its own.
      regions := regions.flatMap fun (region, zeros) =>
        let finish := region.address + region.data.size
        if finish ≤ start || stop ≤ region.address then #[(region, zeros)]
        else (if region.address < start then #[({ region with data := Jit.slice region.data 0 (start - region.address) }, zeros)] else #[]) ++
          (if stop < finish then
            #[({ region with address := stop, data := Jit.slice region.data (stop - region.address) region.data.size }, zeros)]
            else #[])
      let protection : Primus.Protection := ⟨segment.flags &&& 4 != 0, segment.flags &&& 2 != 0, segment.flags &&& 1 != 0⟩
      if start < fileEnd then regions := regions.push (⟨start, bytes, protection⟩, false)
      if fileEnd < stop then regions := regions.push (⟨fileEnd, ← reserveZeros (stop - fileEnd), protection⟩, true)
      top := max top stop
  for (region, zeros) in regions do
    map emu region (zeros := zeros)
  pure top

/-- Why Linux doesn't run a program at `base`, with its interpreter where that goes, if it doesn't: a segment that `Elf.Program.refused`
says of, or zeros of one, which are the process's own to write, that are more than the machine could ever give, as `vm_brk_flags` has
them counted. Linux finds out once the process has let go of what it ran, and ends it with SIGSEGV. -/
private def unloadable (architecture : Architecture) (program : Elf.Program) (base : Nat)
    (interpreter : Option (Elf.Program × Nat)) : Option String :=
  let limit := userLimit architecture
  let zeros (program : Elf.Program) : Bool := program.segments.any fun segment =>
    overcommitted (pageUp (segment.address + segment.memorySize) - pageUp (segment.address + segment.fileSize))
  if program.refused base limit then some "a segment that is larger in the file than in memory, or that ends past the address space"
  else if zeros program then some "a segment of more zeros than the machine has memory"
  else match interpreter with
    | some (loaded, bias) =>
      if loaded.refused bias limit then some "an interpreter with a segment that is larger in the file than in memory, or that ends past the address space"
      else if zeros loaded then some "an interpreter with a segment of more zeros than the machine has memory"
      else none
    | none => none

/-- Where a program goes that can go anywhere, and an interpreter. Those of Linux, without the randomness. -/
private def programBase (architecture : Architecture) : Nat := if architecture.bits == 32 then 0x400000 else 0x555555554000
private def interpreterBase (architecture : Architecture) : Nat := if architecture.bits == 32 then 0x70000000 else 0x7ffff7fc0000

def fileOf (kernel : Kernel) (path : String) : Result ByteArray := do
  let (_, found) ← kernel.resolve "/" path
  let some number := found | .error Errno.enoent
  match kernel.inodes.get? number with
  | some { content := .file data, .. } => .ok data
  | _ => .error Errno.einval

/-- The page of helpers at the top of the memory of 32-bit ARM, of which old code calls these: `__kuser_cmpxchg`, which `ldrex` and
`strex` make atomic, `__kuser_memory_barrier`, `__kuser_get_tls`, and the version of them. -/
private def mapHelpers (emu : Emu) : IO Unit := do
  let base := 0xffff0000
  let words (offset : Nat) (values : List Nat) (page : ByteArray) : ByteArray :=
    (values.zipIdx).foldl (init := page) fun page (value, index) =>
      (List.range 4).foldl (init := page) fun page byte =>
        page.set! (offset + 4 * index + byte) ((value >>> (8 * byte)).toUInt8)
  let page := Bap.zeroBytes 4096
  let page := words 0xfa0 [0xe12fff1e] page
  let page := words 0xfc0 [0xe1923f9f, 0xe0533000, 0x01823f91, 0x03330001, 0x0afffffa, 0xe2730000, 0xe12fff1e] page
  let page := words 0xfe0 [0xee1d0f70, 0xe12fff1e] page
  let page := words 0xffc [5] page
  map emu ⟨base, page, ⟨true, false, true⟩⟩

/-- The stack that the kernel hands over: where the arguments, the environment and the auxiliary vector are. As Linux lays it out, at
its top is a copy of the path that the program was run by, which `AT_EXECFN` points at, and below that the strings of the arguments
and then those of the environment, one after the other, with what `AT_PLATFORM` and `AT_RANDOM` point at below them. Linux leaves a
word above the copy, and this 16 bytes: code that reads a string 16 bytes at a time, as `memchr` of musl does that clang 21 makes
for 32 bits, faults on Linux reading past the top when a string that it looks at ends there. -/
private def mapStack (emu : Emu) (architecture : Architecture) (path : String) (arguments environment : List String)
    (auxiliary : List (Nat × Nat)) (executable : Bool := false) : IO (List (Nat × Nat)) := do
  mapZeros emu (stackTop architecture - stackSize) stackSize ⟨true, true, executable⟩
  let wordSize := architecture.bits / 8
  let place (cursor : Nat) (text : ByteArray) : IO Nat := do
    let at_ := cursor - text.size
    write emu at_ text
    pure at_
  let execfn ← place (stackTop architecture - 16) (path ++ "\x00").toUTF8
  let strings := (arguments ++ environment).map fun text => (text ++ "\x00").toUTF8
  let start := execfn - strings.foldl (· + ·.size) 0
  let _ ← place execfn (strings.foldl (· ++ ·) ByteArray.empty)
  let addresses := (strings.foldl (init := ([], start)) fun (found, at_) text => (at_ :: found, at_ + text.size)).1.reverse
  let (cursor, platform) ← match architecture.platform with
    | some name => do
      let at_ ← place (start / 16 * 16) (name ++ "\x00").toUTF8
      pure (at_, [(15, at_)])
    | none => pure (start / 16 * 16, [])
  let random ← place cursor (ByteArray.mk ((List.range 16).map fun index => (index * 37 + 11).toUInt8).toArray)
  let given := auxiliary ++ platform ++ [(25, random), (31, execfn)]
  let vector := given ++ [(0, 0)]
  let cells := [arguments.length] ++ addresses.take arguments.length ++ [0] ++ addresses.drop arguments.length ++ [0] ++
    vector.flatMap fun entry => [entry.1, entry.2]
  -- It is aligned to 16 where the program starts.
  let pointer := (random - wordSize * cells.length) / 16 * 16
  for (cell, index) in cells.zipIdx do
    write emu (pointer + wordSize * index) (Abi.field architecture.big wordSize cell)
  setReg emu ⟨(threadRegisters emu.config.syscallAbi).1, .imm architecture.bits, 0, false⟩ (bits architecture.bits pointer)
  -- All of it but its end, which is what `/proc/self/auxv` has too.
  pure given

/-- `unloadable` of a program and its interpreter, each where `loadProgram` puts it. -/
private def loadRefusal (architecture : Architecture) (program : Elf.Program) (interpreter : Option (ByteArray × Elf.Program))
    (base : Option Nat := none) : Option String :=
  let base := if program.relocatable then base.getD (programBase architecture) else 0
  unloadable architecture program base
    (interpreter.map fun (_, loaded) => (loaded, if loaded.relocatable then interpreterBase architecture else 0))

/-- A parsed program and what interprets it in an emulator that has nothing mapped, for a process of `credentials` that ran it by
`path`: its registers, its memory, its stack and where it starts. It gives where its heap starts and its auxiliary vector, as a type and
a value by turns. -/
private def loadProgram (emu : Emu) (architecture : Architecture) (credentials : Credentials) (path : String) (data : ByteArray)
    (program : Elf.Program) (interpreter : Option (ByteArray × Elf.Program)) (arguments environment : List String)
    (base : Option Nat := none) : IO (Nat × List Nat) := do
  let base := if program.relocatable then base.getD (programBase architecture) else 0
  if let some why := loadRefusal architecture program interpreter (some base) then throw <| IO.userError s!"{path}: {why}"
  resetRegisters emu architecture
  let top ← mapProgram emu data program base
  -- Where the program headers are: in the segment that has them of the file, as Linux finds them.
  let headers := program.segments.foldl (init := 0) fun found segment =>
    if segment.offset ≤ program.headerOffset && program.headerOffset < segment.offset + segment.fileSize then
      program.headerOffset - segment.offset + segment.address
    else found
  -- Where the interpreter goes: of one that is `ET_EXEC`, where it says, as `load_elf_interp` has it, and otherwise at a base of its own.
  let interpreterBias := match interpreter with
    | some (_, loaded) => if loaded.relocatable then interpreterBase architecture else 0
    | none => 0
  let entry ← match interpreter with
    | some (bytes, loaded) =>
      let _ ← mapProgram emu bytes loaded interpreterBias
      pure (interpreterBias + loaded.entry)
    | none => pure (base + program.entry)
  -- ELFv1: where a program starts is a function descriptor, of the address of its code and its table of contents.
  let (bias, flags) := match interpreter with
    | some (_, loaded) => (interpreterBias, loaded.flags)
    | none => (base, program.flags)
  let descriptor := match architecture with
    | .powerpc 64 _ => flags % 4 != 2
    | _ => false
  let doubleword (address : Nat) : IO Nat := do
    let bytes ← read emu address 8
    pure ((if architecture.big then bytes.toList else bytes.toList.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0)
  let table ← if descriptor then doubleword (entry + 8) else pure 0
  let entry ← if descriptor then pure ((← doubleword entry) + bias) else pure entry
  -- What the processor has: on AArch64, FP and ASIMD, and not CPUID, so that libc doesn't choose routines by the implementer, and
  -- on RISC-V, a bit for each of the letters of IMAFDC.
  let capabilities := match architecture with
    | .x86_64 | .i686 => 0x07888f9f
    | .aarch64 => 3
    -- HALF, THUMB, FAST_MULT, VFP, EDSP, NEON, VFPv3 and TLS
    | .arm => 0xb0d6
    | .riscv64 | .riscv32 => 0x112d
    | .mips _ _ _ => 0
    -- A 32-bit machine with floating point, AltiVec and VSX, or a POWER10, whose instructions the semantics have, as Linux says it
    -- (`COMMON_USER_POWER10` and what the device tree adds): 32 and 64 bits, AltiVec, floating point, an MMU, the ISA 2.06, SMT,
    -- the snoop of the instruction cache, decimal floating point, VSX, the compatibility of the performance monitor, and both byte
    -- orders, with the one that it runs in if that is the little one.
    | .powerpc wide big => if wide == 64 then 0xdc0065c2 + (if big then 0 else 1) else 0x98000080
  -- What a POWER10 has more of, in AT_HWCAP2 (`COMMON_USER2_POWER10`): the ISA 2.07, 3.0 and 3.1, DSCR, `isel`, TAR, the vector
  -- cryptography, the quad precision, `darn` and the matrix-multiply assist. The vectored system call isn't said, and isn't there:
  -- Linux says it only where its kernel has it.
  let capabilities2 := match architecture with
    | .powerpc 64 _ => 0xaee60000
    | _ => 0
  -- AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_BASE, AT_FLAGS, AT_ENTRY, AT_UID, AT_EUID, AT_GID, AT_EGID, AT_HWCAP, AT_CLKTCK,
  -- AT_SECURE, which says that the program runs with ids other than the real ones, and AT_HWCAP2
  let secure := credentials.euid != credentials.uid || credentials.egid != credentials.gid
  -- PowerPC: `ARCH_DLINFO` has, before the rest and after two entries that are to be ignored, the sizes of a block of the data cache,
  -- which is what `dcbz` zeros, of the instruction cache, and of a unified one, which there isn't.
  let caches := match architecture with
    | .powerpc wide _ => let block := if wide == 64 then 128 else 32; [(22, 22), (22, 22), (19, block), (20, block), (21, 0)]
    | _ => []
  let auxiliary := caches ++ [(3, base + headers), (4, program.headerSize), (5, program.headerCount), (6, 4096),
    (7, interpreterBias), (8, 0), (9, base + program.entry), (11, credentials.uid),
    (12, credentials.euid), (13, credentials.gid), (14, credentials.egid), (16, capabilities), (17, 100), (23, if secure then 1 else 0),
    (26, capabilities2)]
  let auxiliary ← mapStack emu architecture path arguments environment auxiliary program.executableStack
  -- On ARM, the low bit of where a program starts says that it is in Thumb.
  let entry ← if architecture == .arm then do
      setReg emu ⟨"ISET", .imm 1, 0, false⟩ (bits 1 (entry % 2))
      mapHelpers emu
      pure (entry / 2 * 2)
    else pure entry
  setPc emu entry
  -- ELFv2: a function that is called from elsewhere finds its table of contents from where it is, and a program is called so.
  if let .powerpc 64 _ := architecture then
    if descriptor then setReg emu (word "R2") (bits 64 (table + bias))
    else setReg emu (word "R12") (bits 64 entry)
  pure (top, auxiliary.flatMap fun entry => [entry.1, entry.2])

/-- A program of a path that a process gives that it may run, as far as it can be told that it will run, with the path of its file
and what its arguments come to: a script is run by what its first line names, with the path of the script as it was given after that,
to a depth that Linux has too. What runs it, and the interpreter of a program of ELF, are to be run by the process too, as
`Kernel.executable` has it, from its working directory. -/
private def programOf (kernel : Kernel) (group : Nat) (architecture : Architecture) : Nat → String → List String →
    Result (String × ByteArray × Elf.Program × Option (ByteArray × Elf.Program) × List String)
  | 0, _, _ => .error Errno.enoexec
  | depth + 1, path, arguments => do
    let data ← kernel.executable group (treePath kernel group path)
    if data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33 then
      let first := (String.fromUTF8? (data.extract 2 (min data.size 256))).getD ""
      -- As `load_script` has it: the name is after spaces and tabs, to the next of them, and all of the line after it, without them
      -- at either end, is one argument.
      let blank (char : Char) : Bool := char == ' ' || char == '\t'
      let line := ((first.splitOn "\n").headD "").dropWhile blank |>.toString
      let name := (line.takeWhile (!blank ·)).toString
      if name.isEmpty then .error Errno.enoexec
      let given := ((line.drop name.length).dropWhile blank |>.dropEndWhile blank).toString
      programOf kernel group architecture depth name (name :: (if given.isEmpty then [] else [given]) ++ [path] ++ arguments.drop 1)
    else
      let some program := (Elf.parse data).toOption | .error Errno.enoexec
      if Architecture.ofElf program.machine program.bits program.big program.flags != some architecture then .error Errno.enoexec
      let interpreter ← match program.interpreter with
        | none => .ok none
        | some name => do
          let bytes ← kernel.executable group (treePath kernel group name)
          -- What isn't of ELF, or is of another machine, is `ELIBBAD`, as `load_elf_binary` has it.
          let some loaded := (Elf.parse bytes).toOption | .error 80
          if Architecture.ofElf loaded.machine loaded.bits loaded.big loaded.flags != some architecture then .error 80
          .ok (some (bytes, loaded))
      -- The file, by where the links lead, as `/proc/PID/exe` has it.
      let (file, _) ← kernel.resolve "/" (treePath kernel group path)
      .ok (file, data, program, interpreter, arguments)

/-- What `execve` of a process runs, of the directories of the host that the machine sees: the program, what a script names to run it,
and the interpreter of a program of ELF, as `programOf` looks for them. -/
private def programFromHost (machine : Machine) (group : Nat) (path : String) : IO Unit := do
  if (← machine.hostMounts.get).isEmpty then return
  let mut path := path
  for _ in [0:4] do
    let kernel ← machine.kernel.get
    path := treePath kernel group path
    fromHost machine path
    let .ok data := fileOf (← machine.kernel.get) path | return
    if data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33 then
      let first := (String.fromUTF8? (data.extract 2 (min data.size 256))).getD ""
      let blank (char : Char) : Bool := char == ' ' || char == '\t'
      path := (((first.splitOn "\n").headD "").dropWhile blank |>.takeWhile (!blank ·)).toString
    else
      if let some name := (Elf.parse data).toOption.bind (·.interpreter) then fromHost machine (treePath kernel group name)
      return

/-- The strings of a list of pointers that a null ends, as `execve` is given them, as far as `room` bytes of them with their pointers: one
more than that, which is `E2BIG`, ends it, so that no more of the guest's is read than a program may be given. -/
private def readStrings (emu : Emu) (architecture : Architecture) (address : Nat) (room : Nat) : IO (List String) := do
  if address == 0 then return []
  let size := architecture.bits / 8
  let rec go : Nat → Nat → Nat → List String → IO (List String)
    | 0, _, _, found => pure found.reverse
    | fuel + 1, at_, used, found => do
      let bytes ← read emu at_ size
      let bytes := if architecture.big then bytes.toList else bytes.toList.reverse
      let pointer := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
      if pointer == 0 then pure found.reverse
      else
        -- Of `MAX_ARG_STRLEN`, a byte more than it takes, which is `E2BIG`.
        let text ← readString emu pointer (32 * 4096 + 1)
        let used := used + text.utf8ByteSize + 1 + size
        if used > room then pure (text :: found).reverse else go fuel (at_ + size) used (text :: found)
  go 65536 address 0 []

/-- `execve`, and `execveat`, whose path is from the directory that a descriptor is open on, or with `AT_EMPTY_PATH` is the file that
it is open on when it is empty, and which with `AT_SYMLINK_NOFOLLOW` doesn't follow a link at its end: nothing of the process changes
until the program is known to run, and then all its memory and its threads other than this one are gone, and its descriptors but for
those that stay open over it, and this one goes on with the id of the process, with the credentials that `Credentials.executed` says.
A program of a descriptor is run by `/dev/fd/N`, or `/dev/fd/N/path`, as Linux names it, and of an empty path named by its file; a
script so is `ENOENT` if the descriptor closes on exec, as what runs it couldn't open it. -/
private def execute (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO SyscallAction := do
  let architecture := machine.architecture
  let kernel ← machine.kernel.get
  let group := (← currentTask emu).group
  let (directory, flags, args) := if call == .execveat then (some (args.getD 0 0), args.getD 4 0, args.drop 1) else (none, 0, args)
  -- As much of them as there may be, and a string more, which the check of `E2BIG` below finds.
  let room := (kernel.limitOf group 3).1 / 4
  match ← (do pure (← readString emu (args.getD 0 0), ← readStrings emu architecture (args.getD 1 0) room,
      ← readStrings emu architecture (args.getD 2 0) room) : IO _).toBaseIO with
  | .error _ => pure (errorOf Errno.efault)
  | .ok (given, arguments, environment) =>
    if flags ||| 0x1100 != 0x1100 then return errorOf Errno.einval
    -- Of `MAX_ARG_STRLEN` each, and of a quarter of the stack all of them with their pointers, as `fs/exec.c` has it, before anything
    -- of the process changes: more is `E2BIG`.
    let strings := arguments ++ environment
    let total := strings.foldl (fun total text => total + (Path.toBytes text).size + 1 + architecture.bits / 8) 0
    if strings.any (fun text => (Path.toBytes text).size > 32 * 4096) || total > (kernel.limitOf group 3).1 / 4 then
      return errorOf Errno.e2big
    if given.isEmpty && flags &&& 0x1000 == 0 then return errorOf Errno.enoent
    -- The descriptor that the path is from, if it is from one.
    let descriptor := directory.filter fun fd => !atCwd fd && !given.startsWith "/"
    if let some fd := descriptor then
      if let .error errno := kernel.openFileOf group fd then return errorOf errno
    let path := match descriptor with
      | some fd => if given.isEmpty then s!"/dev/fd/{fd}" else s!"/dev/fd/{fd}/{given}"
      | none => given
    -- This is served before `serveKernelCalls`, which makes `/proc` for the calls that it serves.
    if looksAtProc (Path.ofParts (Path.parts (kernel.cwdOf group) path)) then makeProc machine emu group
    programFromHost machine group path
    let kernel ← machine.kernel.get
    if flags &&& 0x100 != 0 then
      if let .ok (_, some number) := kernel.resolve "/" (treePath kernel group path) (follow := false) then
        if let .ok { content := .symlink _, .. } := kernel.inodeOf number then return errorOf Errno.eloop
    if let some fd := descriptor then
      if ((kernel.process group).descriptors.get? fd).any (·.closeOnExec) then
        if let .ok data := kernel.executable group (treePath kernel group path) then
          if data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33 then return errorOf Errno.enoent
    -- With no arguments, a program has one that is empty, as Linux gives it since 5.18.
    match programOf kernel group architecture 4 path (if arguments.isEmpty then [""] else arguments) with
    | .error errno => pure (errorOf errno)
    | .ok (name, data, program, interpreter, arguments) =>
      -- What Linux can't load once it has begun to, it ends with SIGSEGV, as `bprm_execve` has it past its point of no return.
      if (loadRefusal architecture program interpreter).isSome then
        kill emu group 11
        return .returnValue 0
      let table ← emu.taskTable.get
      let current ← thread emu
      -- What its threads hold for others is let go of, as each of them ends and as the one that goes on leaves its memory
      -- (`exec_mm_release`); and its descriptors are its own from here, and it is dumpable as a process is at first.
      for task in table.tasks do
        if task.group == group && task.status.isNone then
          for hook in ← emu.taskExiting.get do hook task.tid
      machine.notes.modify fun notes => { notes with
        files := (notes.files.map (·.erase group)).filter (·.length > 1), dumpable := notes.dumpable.erase group }
      for task in table.tasks do
        if task.group == group && task.tid != current && task.status.isNone then
          emu.taskTable.modify (·.exitTask task.tid 0 group)
          emu.threadsRef.modify (setThreadStopped · task.tid true)
      -- It goes on as the process, by its id.
      executeAsLeader emu
      -- A child of `vfork` has its parent's memory, which the parent keeps: the program goes in memory of its own.
      let space := (← currentTask emu).space
      if table.tasks.any fun task => task.space == space && task.group != group && task.status.isNone then
        leaveSharedMemory emu
      for region in ← emu.regions.get do
        unmap emu region.address region.data.size
      let process := kernel.process group
      -- Of a script, as Linux has it, what is set-user-ID or set-group-ID is ignored.
      let script := match kernel.executable group (treePath kernel group path) with
        | .ok data => data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33
        | .error _ => false
      let (setUser, setGroup) := if script then (none, none) else kernel.setIdsOf (treePath kernel group path)
      let credentials := process.credentials.executed setUser setGroup
      let (top, auxiliary) ← loadProgram emu architecture credentials path data program interpreter arguments environment
      emu.redirect.set (some (← pc emu))
      wakePipeReaders emu
      machine.kernel.set (kernel.setProcess group { process with
        descriptors := process.descriptors.filter fun _ entry => !entry.closeOnExec
        breakStart := top, breakEnd := top, command := arguments, environment, program := name
        name := commOf (Path.name (if given.isEmpty then name else path)), auxiliary, threadNames := []
        mappings := [], forkAdvice := [], guards := [], executed := true, credentials })
      releaseVfork emu group
      machine.timers.executed group
      pure (.returnValue 0)

/-- Whether an intrinsic is of x87, of 80 bits, from or to them too, as a load of 64 bits is: the rest of x86 is of SSE. -/
private def isX87 (name : String) : Bool := (name.splitOn "_").contains "80"

/-- What the name of an intrinsic of SSE ends with while FTZ of MXCSR is set, and the name without it. -/
private def flushMark : String := "_ftz"

private def withoutFlushMark (name : String) : String :=
  if name.endsWith flushMark then (name.dropEnd flushMark.length).toString else name

/-- A conversion between a half and a single of F16C, `VCVTPH2PS` and `VCVTPS2PH`, which the semantics call `fconvert`: the half
is as it is, whatever DAZ and FTZ say, and a denormal half isn't said. Those of AVX512-FP16, `VCVTPH2PSX` and the like, which go by
MXCSR as any operation does, are `fconvertx`. -/
private def halfOfF16C (name : String) : Bool :=
  let name := withoutFlushMark name
  name.startsWith "fconvert_" && (name.endsWith "_16_32" || name.endsWith "_32_16")

/-- The name that `Bap.Float` knows an intrinsic of x86 by: without the mark of FTZ, and `fconvert` of `fconvertx`. -/
private def plainName (name : String) : String :=
  let name := withoutFlushMark name
  if name.startsWith "fconvertx_" then "fconvert_" ++ (name.drop 10).toString else name

/-- Whether an intrinsic of SSE gives a zero for what is tiny with FTZ: what makes a number of a format, but a half of F16C, which
`VCVTPS2PH` gives as a denormal whatever MXCSR says. -/
private def flushedToZero (name : String) : Bool :=
  let parts := name.splitOn "_"
  (Bap.Float.formatsOf (plainName name)).2.isSome && !isX87 name && !halfOfF16C name &&
    ["fadd", "fsub", "fmul", "fdiv", "fsqrt", "fmad", "fmadh", "fconvert", "fconvertx", "fscalef"].contains (parts.headD "")

/-- BF16, in the upper half of a single, as it is: the bits. -/
private def singleOfBf16 (bits : Nat) : Nat := (bits % 2 ^ 16) * 2 ^ 16

/-- A single as BF16, to nearest, as `VCVTNEPS2BF16` has it: a denormal is a zero, a NaN is made quiet, and nothing is raised. -/
private def bf16OfSingle (bits : Nat) : Nat :=
  let bits := bits % 2 ^ 32
  let exponent := bits >>> 23 % 256
  if exponent == 0 then (bits >>> 31) * 2 ^ 15
  else if exponent == 255 then (bits >>> 16) ||| (if bits % 2 ^ 23 != 0 then 0x40 else 0)
  else ((bits + 0x7fff + (bits >>> 16) % 2) >>> 16) % 2 ^ 16

/-- What serves the intrinsics of floating point of x86: `Bap.Float`, and of a name that `roundedName` marked, a zero of the sign
of what is tiny. -/
private def serveX86 (name : String) (inputs : List Nat) : Option (Nat × Nat) :=
  -- The rounds of AES-NI, which are no theory of the semantics.
  match name, inputs with
  | "aesenc", [state, key] => some (128, Bap.Crypto.AES.encryptRound false state key)
  | "aesenclast", [state, key] => some (128, Bap.Crypto.AES.encryptRound true state key)
  | "aesdec", [state, key] => some (128, Bap.Crypto.AES.decryptRound false state key)
  | "aesdeclast", [state, key] => some (128, Bap.Crypto.AES.decryptRound true state key)
  | "aesimc", [key] => some (128, Bap.Crypto.AES.inverseMix key)
  | "aeskeygenassist", [key, constant] => some (128, Bap.Crypto.AES.keygenAssist key constant)
  -- The inverse of a byte in the field of AES, and the affine map of GFNI of it: bit `i` is the parity of the inverse under
  -- byte `7 - i` of the matrix, with that bit of the constant.
  | "gf2p8affineinvqb", [byte, matrix, constant] =>
    let inverse := Bap.Crypto.AES.inverse byte
    some (8, (List.range 8).foldl (fun out bit =>
      let row := (matrix >>> (8 * (7 - bit))) % 256 &&& inverse
      let parity := (List.range 8).foldl (fun parity index => parity ^^^ (row >>> index) % 2) 0
      out ||| ((parity ^^^ (constant >>> bit) % 2) <<< bit)) 0)
  -- BF16 of AVX512-BF16, which is of the bits: the conversions, and the dot product, of two fused multiplications to nearest,
  -- with denormals as zeros and what is tiny a zero, and nothing raised.
  | "fconvert_rne_bfloat_16_32", [half] => some (32, singleOfBf16 half)
  | "fconvert_rne_bfloat_32_16", [single] => some (16, bf16OfSingle single)
  | "dpbf16_rne_bfloat_32", [sum, x, y] =>
    let format : Bap.Float.Format := ⟨8, 23, false⟩
    let fused (a b c : Nat) : Nat :=
      let operands := [a, b, c].map (Bap.Float.flush format)
      let name := "fmad_rne_ieee754_binary_32"
      match Bap.Float.evaluateWith .x86 name operands with
      | some (_, bits) => if Bap.Float.isTiny .x86 name operands then bits &&& 2 ^ 31 else bits
      | none => 0
    some (32, fused (singleOfBf16 x) (singleOfBf16 y) (fused (singleOfBf16 (x >>> 16)) (singleOfBf16 (y >>> 16)) sum))
  | _, _ =>
  let flushes := name.endsWith flushMark
  let name := plainName name
  match Bap.Float.evaluateWith .x86 name inputs with
  | some (width, bits) =>
    if flushes && Bap.Float.isTiny .x86 name inputs then some (width, bits &&& (1 <<< (width - 1))) else some (width, bits)
  | none => none

/-- The name of an intrinsic that goes by the rounding mode of the machine, by its mode. That is to nearest nearly always, so
that a register is all that it costs then. -/
private def roundedName (architecture : Architecture) (env : Bil.Env) (name : String) : String :=
  let field (register : String) (width shift : Nat) (modes : List String) : String :=
    match Bil.lookup env ⟨register, .imm width, 0, false⟩ with
    | .ok (.bits value) =>
      let index := (value.toNat >>> shift) % 8
      if index == 0 then name else "_".intercalate ((name.splitOn "_").map fun part =>
        if part == "rne" then modes.getD index "rne" else part)
    | _ => name
  let binaryModes := ["rne", "rtp", "rtn", "rtz", "rne", "rtp", "rtn", "rtz"]
  match architecture with
  | .x86_64 | .i686 =>
    if isX87 name then
      -- Of the precision control of single or double, an operation of x87 rounds to odd here, and to its precision by its mode after,
      -- as `controlled` does: that is rounded once.
      let precision := match Bil.lookup env ⟨"FPU_CONTROL", .imm 16, 0, false⟩ with
        | .ok (.bits value) => (value.toNat >>> 8) % 4
        | _ => 3
      let arithmetic := ["fadd", "fsub", "fmul", "fdiv", "fsqrt"].contains ((name.splitOn "_").headD "")
      if (precision == 0 || precision == 2) && arithmetic && (name.splitOn "_rne_").length > 1 then
        "_".intercalate ((name.splitOn "_").map fun part => if part == "rne" then "rod" else part)
      else field "FPU_CONTROL" 16 10 ["rne", "rtn", "rtp", "rtz", "rne", "rtn", "rtp", "rtz"]
    else
      -- What is of BF16 isn't of MXCSR.
      if (name.splitOn "_bfloat_").length > 1 then name else
      let named := field "MXCSR" 32 13 ["rne", "rtn", "rtp", "rtz", "rne", "rtn", "rtp", "rtz"]
      -- With the flush to zero of MXCSR, what serves it is told so by the name, as it has no more than that and the operands.
      let flushes := match Bil.lookup env ⟨"MXCSR", .imm 32, 0, false⟩ with
        | .ok (.bits value) => value.toNat.testBit 15
        | _ => false
      if flushes && flushedToZero name then named ++ flushMark else named
  | .aarch64 => field "FPCR" 32 22 binaryModes
  | .arm => field "FPSCR" 32 22 binaryModes
  -- What frm has of 5 to 7 is reserved, of which the semantics raise an illegal instruction before it is rounded.
  | .riscv64 | .riscv32 => field "FCSR" 32 5 ["rne", "rtz", "rtn", "rtp", "rna", "rne", "rne", "rne"]
  | .powerpc _ _ => field "FPSCR" 64 0 ["rne", "rtz", "rtp", "rtn", "rne", "rtz", "rtp", "rtn"]
  | .mips bits _ _ => field "FCSR" bits 0 ["rne", "rtz", "rtp", "rtn", "rne", "rtz", "rtp", "rtn"]

/-- Whether denormal operands are zeros, whether denormal results are, and whether a NaN that results is the default one: FZ
and DN of ARM, and DAZ and FZ of SSE. -/
private def floatControls (architecture : Architecture) (env : Bil.Env) (name : String) : Bool × Bool × Bool :=
  let test (register : String) (width bit : Nat) : Bool :=
    match Bil.lookup env ⟨register, .imm width, 0, false⟩ with
    | .ok (.bits value) => value.toNat.testBit bit
    | _ => false
  match architecture with
  | .aarch64 => let zero := test "FPCR" 32 24; (zero, zero, test "FPCR" 32 25)
  -- Of `rns`, the standard value of FPSCR that NEON goes by: denormals are zeros, and a NaN is the default.
  | .arm => if (name.splitOn "_rns_").length > 1 then (true, true, true) else
    let zero := test "FPSCR" 32 24; (zero, zero, test "FPSCR" 32 25)
  | .x86_64 | .i686 =>
    if isX87 name then (false, false, false)
    else
      -- The halves of F16C are as they are: `VCVTPH2PS` takes a denormal whatever DAZ says, and `VCVTPS2PH` gives one whatever FTZ does.
      let f16c := halfOfF16C name
      (test "MXCSR" 32 6 && !(f16c && name.endsWith "_16_32"), test "MXCSR" 32 15 && !(f16c && name.endsWith "_32_16"), false)
  | _ => (false, false, false)

private def floatRules : Architecture → Bap.Float.NaNRules
  | .x86_64 | .i686 => .x86
  | .aarch64 | .arm => .arm
  | .riscv64 | .riscv32 => .riscv
  | .mips _ _ true => .powerpc
  | .mips _ _ false => .mips
  | .powerpc _ _ => .powerpc

/-- What the controls make of an intrinsic. -/
private def controlled (architecture : Architecture) (env : Bil.Env) (name : String) : (List Nat → List Nat) × (Nat → Nat) :=
  let given := withoutFlushMark name
  let name := plainName name
  -- Of x87 by its precision control, what was rounded to odd is rounded to that precision by its mode.
  if (architecture == .x86_64 || architecture == .i686) && (name.splitOn "_rod_ieee754_binary_80").length > 1 then
    let control := match Bil.lookup env ⟨"FPU_CONTROL", .imm 16, 0, false⟩ with
      | .ok (.bits value) => value.toNat
      | _ => 0x37f
    let mode : Bap.Float.Mode := match (control >>> 10) % 4 with
      | 0 => .rne
      | 1 => .rtn
      | 2 => .rtp
      | _ => .rtz
    let precision := if (control >>> 8) % 4 == 0 then 24 else 53
    (id, Bap.Float.narrowPrecision ⟨15, 63, true⟩ mode precision)
  else
  let (zeroIn, zeroOut, defaultNaN) := floatControls architecture env given
  if !zeroIn && !zeroOut && !defaultNaN then (id, id) else
  let (source, target) := Bap.Float.formatsOf name
  let inputs (values : List Nat) : List Nat :=
    match source, zeroIn with
    | some format, true => Bap.Float.flushOperands name format values
    | _, _ => values
  let result (bits : Nat) : Nat :=
    let bits := if defaultNaN then Bap.Float.defaultFor (floatRules architecture) name bits else bits
    match target, zeroOut with
    | some format, true => Bap.Float.flush format bits
    | _, _ => bits
  (inputs, result)

/-- The flags of the machine that an intrinsic raises. Each is sticky, in a register whose bits for invalid, division by zero,
overflow, underflow and inexact are these. -/
private def raisedFlags (architecture : Architecture) (env : Bil.Env) (name : String) (inputs : List Nat) (result : Nat) :
    List (Bap.Var × Bap.Value) :=
  let given := withoutFlushMark name
  let name := plainName name
  -- What is quiet, as AltiVec's operations of PowerPC are, says nothing.
  if ["rnq", "rzq", "rpq", "rmq"].any fun mode => (name.splitOn s!"_{mode}_").length > 1 then [] else
  let rules := floatRules architecture
  let (register, width, invalid, divide, over, under, inexact) : String × Nat × Nat × Nat × Nat × Nat × Nat := match architecture with
    | .x86_64 | .i686 =>
      if isX87 name then ("FPU_STATUS", 16, 0, 2, 3, 4, 5) else ("MXCSR", 32, 0, 2, 3, 4, 5)
    | .aarch64 => ("FPSR", 32, 0, 1, 2, 3, 4)
    | .arm => ("FPSCR", 32, 0, 1, 2, 3, 4)
    | .riscv64 | .riscv32 => ("FCSR", 32, 4, 3, 2, 1, 0)
    | .mips bits _ _ => ("FCSR", bits, 6, 5, 4, 3, 2)
    | .powerpc _ _ => ("FPSCR", 64, 29, 26, 28, 27, 25)
  let var : Bap.Var := ⟨register, .imm width, 0, false⟩
  match Bil.lookup env var with
  | .ok (.bits value) =>
    let old := value.toNat
    let (zeroIn, zeroOut, _) := floatControls architecture env given
    let x86 := architecture == .x86_64 || architecture == .i686
    let (source, target) := Bap.Float.formatsOf name
    let flushedIn := match source with
      | some format => inputs.any (Bap.Float.isDenormal format)
      | none => false
    let effective := match source, zeroIn with
      | some format, true => Bap.Float.flushOperands name format inputs
      | _, _ => inputs
    let raised := Bap.Float.raisedBy rules name effective result (old.testBit inexact && !zeroOut)
    -- A denormal half that `VCVTPH2PS` of F16C takes isn't said.
    let raised := if x86 && halfOfF16C given && given.endsWith "_16_32" then { raised with denormal := false } else raised
    -- What a denormal result would have been, had it not been a zero: of x86, what is tiny, which is a zero then.
    let flushedOut := zeroOut && (if x86 then Bap.Float.isTiny rules name effective else
      match target, Bap.Float.evaluateWith rules name effective with
      | some format, some unflushed => Bap.Float.isDenormal format unflushed.2
      | _, _ => false)
    -- Of x87 with a precision control of less than its format, what was rounded to odd in the format and then to the precision,
    -- by `controlled`, is inexact when that changed it, and underflows when it is tiny too.
    let raised := if x86 && (name.splitOn "_rod_ieee754_binary_80").length > 1 then
        match Bap.Float.evaluateWith rules name effective with
        | some (_, wide) =>
          let narrowed := result != wide
          let tiny := (wide >>> 64) % 2 ^ 15 == 0 || (result >>> 64) % 2 ^ 15 == 0
          { raised with inexact := raised.inexact || narrowed, underflow := raised.underflow || (narrowed && tiny) }
        | none => raised
      else raised
    -- What underflows to a zero isn't inexact on ARM, as what is a zero is what it was to be.
    let raised := if flushedOut then { raised with underflow := true, inexact := x86 }
      else if zeroOut && !x86 && raised.underflow then { raised with inexact := false }
      else raised
    let flag (on : Bool) (bit : Nat) : Nat := if on then 1 <<< bit else 0
    -- Of PowerPC, which invalid operation it was, of which VX is the summary; FX of any exception that comes to be; and of an
    -- operation that rounds, FI and FR of it, and of one whose result is a number, its class, FPRF, the last four of which are FPCC.
    if architecture matches .powerpc .. then
      let details := if raised.invalid then
          let found := Bap.Float.powerpcInvalid name effective
          if found == 0 then 1 <<< 10 else found
        else 0
      let exceptions := details ||| flag raised.divideByZero divide ||| flag raised.overflow over |||
        flag raised.underflow under ||| flag raised.inexact inexact
      let updated := old ||| exceptions
      let summary := (if updated &&& 0x01f80700 != 0 then 1 <<< 29 else 0) |||
        (if exceptions &&& (old ^^^ (2 ^ 64 - 1)) &&& 0x1ff80700 != 0 then 1 <<< 31 else 0)
      let operation := (name.splitOn "_").headD ""
      let rounds := ["fadd", "fsub", "fmul", "fdiv", "fsqrt", "fmad", "fround", "fconvert", "cast"].contains operation
      let classOf : Option Nat := match target with
        | some format => if rounds then some (Bap.Float.powerpcClass format result) else none
        | none => none
      let status := if rounds then
          (if raised.inexact then 1 <<< 17 else 0) |||
          (if raised.inexact && Bap.Float.roundedUp rules name effective result then 1 <<< 18 else 0) |||
          (match classOf with | some c => (c >>> 4) <<< 16 | none => 0)
        else 0
      let kept := if rounds then (updated ||| summary) - ((updated ||| summary) &&& (7 <<< 16)) else updated ||| summary
      let fpscr := kept ||| status
      let bit (name : String) (value : Nat) : Bap.Var × Bap.Value := (⟨name, .imm 1, 0, false⟩, .bits (BitVec.ofNat 1 value))
      let fpcc := match classOf with
        | some c => [bit "FL" (c >>> 3 % 2), bit "FG" (c >>> 2 % 2), bit "FE" (c >>> 1 % 2), bit "FU" (c % 2)]
        | none => []
      (if fpscr == old then [] else [(var, .bits (BitVec.ofNat width fpscr))]) ++ fpcc
    else
    let added := flag raised.invalid invalid ||| flag raised.divideByZero divide ||| flag raised.overflow over |||
      flag raised.underflow under ||| flag raised.inexact inexact |||
      (if x86 then flag raised.denormal 1 else flag (zeroIn && flushedIn) 7)
    -- Of MIPS, Cause, bits 12 to 17, is what this operation raised, the flags it is of shifted up, whatever it was before.
    let new := if architecture matches .mips .. then (old - (old &&& 0x3f000)) ||| added ||| ((added &&& 0x7c) <<< 10)
      else old ||| added
    -- Of x87, C1 says that what isn't exact was rounded away from zero, and is clear otherwise.
    let new := if x86 && isX87 name then
        let up := raised.inexact && (if (name.splitOn "_rod_ieee754_binary_80").length > 1 then
            (Bap.Float.evaluateWith rules name effective).any fun (_, wide) =>
              Bap.Float.narrowPrecision ⟨15, 63, true⟩ .rtz (if ((Bil.lookup env ⟨"FPU_CONTROL", .imm 16, 0, false⟩ |>.toOption.bind
                fun value => match value with | .bits control => some ((control.toNat >>> 8) % 4) | _ => none).getD 3) == 0 then 24 else 53)
                wide != result
          else Bap.Float.roundedUp rules name effective result)
        let new := (new &&& (0xffff - 0x200)) ||| (if up then 0x200 else 0)
        -- An exception that the control word doesn't mask is pending, which the summary and the busy bit say: the next
        -- instruction of x87 that waits raises it (`x87-wait` of the semantics).
        let control := match Bil.lookup env ⟨"FPU_CONTROL", .imm 16, 0, false⟩ with
          | .ok (.bits value) => value.toNat
          | _ => 0x37f
        if new &&& (0x3f - control % 64) != 0 then new ||| 0x8080 else new
      else new
    -- Of SSE, an exception that MXCSR doesn't mask is raised at once, and the rest of the instruction isn't run.
    let trap : List (Bap.Var × Bap.Value) :=
      if x86 && !isX87 name && added &&& (0x3f - (old >>> 7) % 64) != 0 then
        [(⟨Bap.Emu.floatTrap, .imm 1, 0, false⟩, .bits (BitVec.ofNat 1 1))]
      else []
    (if new == old then [] else [(var, .bits (BitVec.ofNat width new))]) ++ trap
  | _ => []

/-- The system calls of i386 that a process of 64 bits has by `int $0x80`, the compatibility entry (`do_int80_emulation`). Those of
tasks and signals that take numbers alone, or what both lay out the same, are the calls of x86-64 of these numbers. -/
private def compatTaskCalls : List (Nat × Nat) :=
  [(1, 60), (2, 57), (20, 39), (37, 62), (64, 110), (91, 11), (125, 10), (158, 24), (175, 14), (190, 58), (219, 28), (224, 186),
    (238, 200), (252, 231), (270, 234)]

/-- The calls of the kernel that the compatibility entry doesn't have: those that go by where the task's memory or its registers are,
of which a process of 64 bits has what i386 hasn't room for, and those of timers and signals, whose structures the machine lays out
by the architecture it was made of. A program that makes one by `int $0x80` is an error of the run. -/
private def compatWithout : List Call :=
  [.execve, .execveat, .setThreadArea, .sigaltstack, .nanosleep, .clockNanosleep, .clockNanosleep64, .setitimer, .getitimer,
    .timerCreate, .timerSettime, .timerSettime64, .timerGettime, .timerGettime64, .timerGetoverrun, .timerDelete, .timerfdSettime,
    .timerfdSettime64, .timerfdGettime, .timerfdGettime64, .ppoll, .ppoll64, .pselect6, .pselect664, .epollPwait, .epollPwait2,
    .signalfd, .signalfd4, .mmap, .mmap2, .mremap, .prctl, .seccomp]

/-- The number that the hooks of the machine have a call of i386 by: of x86-64 for what `compatTaskCalls` has, with `compatMark` for
what the kernel serves by the layouts of i386, and one that is of no call past the table of i386, which is ENOSYS. -/
private def compatNumber (number : Nat) : Option Nat :=
  match List.lookup number compatTaskCalls with
  | some native => some native
  | none =>
    match Architecture.i686.call number with
    | some call => if compatWithout.contains call then none else some (compatMark + number)
    | none => if number > 467 then some 0xffffffff else none

/-- An emulator of an architecture, as a Linux machine needs it, with nothing mapped. -/
private def emulatorOf (architecture : Architecture) : IO Emu := do
  -- A real program runs more code than the working set of a few thousand blocks that the default is for, and past it, each one
  -- would be lifted each time it runs. Most of its code runs at its start, a few times, and compiling that takes longer than
  -- running it, up to about this threshold: at 16 a short program takes half as long again, and a long one no less.
  -- What is kept has a bound all the same, as each lifted block takes about 4 KB of the host and each piece of native code about
  -- 45 KB: 131072 blocks and 16384 of native code come to some 500 and 700 MB at most, where a million blocks and as much native code
  -- as there were blocks took a long program to gigabytes. Less than what a program keeps running makes it compile all of that again
  -- and again: 14000 functions that run in turn take twice as long with 8192 of native code.
  let tuned (config : Config) : Config :=
    { config with cacheLimit := 131072, rangeCacheLimit := some 16384, nativeLimit := some 16384, hotThreshold := 64 }
  -- Nothing is in its one page, which goes at once.
  let page := ByteArray.mk (Array.replicate 16 0)
  let emu ← match architecture with
    | .x86_64 => x86_64 page 0x1000 0 tuned
    | .i686 => x86_32 page 0x1000 0 tuned
    | .aarch64 => aarch64 page 0x1000 0 tuned
    | .arm => arm32 page 0x1000 0 false tuned
    | .riscv64 => riscv64 page 0x1000 0 tuned
    | .riscv32 => riscv32 page 0x1000 0 tuned
    | .mips 32 big release6 => mips32 page 0x1000 0 release6 (if big then .big else .little) tuned
    | .mips _ big release6 => mips64 page 0x1000 0 release6 (if big then .big else .little) tuned
    | .powerpc wide big => powerpc page 0x1000 0 { bits := wide, endian := if big then .big else .little } tuned
  unmap emu 0x1000 16
  if architecture matches .x86_64 then emu.compatCall.set compatNumber
  emu.intrinsicName.set (roundedName architecture)
  -- What PowerPC has besides the floating point, `powerpc-`, is of `Bap.PowerPC`, and raises nothing of FPSCR but what its semantics
  -- write of what it gives them.
  let powerpc := match architecture with
    | .powerpc .. => true
    | _ => false
  emu.intrinsicRaises.set fun env name inputs result =>
    if powerpc && name.startsWith "powerpc-" then [] else raisedFlags architecture env name inputs result
  emu.intrinsicControls.set (controlled architecture)
  let float := Bap.Float.evaluateWith (match architecture with
    | .x86_64 | .i686 => .x86
    | .aarch64 | .arm => .arm
    | .riscv64 | .riscv32 => .riscv
    | .mips _ _ true => .powerpc
    | .mips _ _ false => .mips
    | .powerpc _ _ => .powerpc)
  emu.intrinsicServer.set (some fun name inputs =>
    if powerpc && name.startsWith "powerpc-" then Bap.PowerPC.serve name inputs
    else if architecture matches .x86_64 | .i686 then serveX86 name inputs else float name inputs)
  pure emu

/-- What sees a system call before the kernel does, with its number and arguments as the guest gave them. `.default` hands it on, and
`.returnValue` answers it, with what goes in the register of the result as it is: `syscallReturn` makes that of a result or an error
on any architecture, as some say that a call failed apart from its value. -/
abbrev SyscallHandler := Emu → Nat → List Nat → IO SyscallAction

/-- What a checkpoint knows the heaps of `Machine.malloc` by. -/
private def heapModelId : String := "bap.heap"

/-- What a checkpoint knows what `Machine.loadLibrary` has loaded by. -/
private def libraryModelId : String := "bap.libraries"

/-- What a checkpoint has of the trace of instructions and accesses, all of it, as the machine of it is to go on with it. -/
private def traceModelId : String := "bap.trace"

/-- What a checkpoint knows what a machine keeps of its tasks by: see `TaskNotes`. -/
private def notesModelId : String := "bap.tasks"

/-- The models that every machine has, with the versions of what they keep: of the signals, 3 has the last
exception of each thread; of ptrace, 2 has the stops that tracees have yet to make
and those that stopped for their end, 3 the exits that tracers that aren't parents have yet to hear of, 4 the steps that tracees have yet to make, 5 the system call that
each tracee last started, 6 what a tracer said a call that a tracee is stopped at the start of is to be, and 7 the processes that are
over that no one waits for, and 10 the tracees that were left to listen; of the timers, 3 has the fraction of what is left of a wait that goes back as a `timespec` or a `timeval`,
and 4 the semaphore that a call of `semop` waits for. -/
private def builtinModels : List (String × Nat) :=
  [(notesModelId, 1), (Signals.modelId, 3), (Ptrace.modelId, 10), (Seccomp.modelId, 1), (Timers.modelId, 4), (Ring.modelId, 2), (heapModelId, 1), (libraryModelId, 2),
    (traceModelId, 6)]

private def builtinVersion (id : String) : Nat := (builtinModels.lookup id).getD 1

/-- Where a word is to `futex` that is in the file of a shared mapping, which is no address space, of which there are as many as tasks. -/
private def sharedFutexSpace : Nat := Kernel.fileSpace

/-- Runs this as another thread, and comes back. Going there and back is a switch of threads to the emulator, which takes what threads
hold exclusively and what is left of a turn, and nothing runs for it, so that those stay. -/
private def inThread (emu : Emu) (target : ThreadId) (action : IO α) : IO α := do
  let home ← thread emu
  let width ← wordWidth emu
  let monitorVar := exclusiveMonitor width
  let monitorOf (id : ThreadId) : IO (Option Bap.Value) := do
    match ← (threadReg emu id monitorVar).toBaseIO with
    | .ok value => pure (some value)
    | .error _ => pure none
  let turn ← emu.turnUsed.get
  let homeMonitor ← monitorOf home
  let targetMonitor ← monitorOf target
  let arrived ← emu.switchedIn.get
  emu.switchedIn.set none
  try
    switchThread emu target
    try action
    finally switchThread emu home
  finally
    emu.switchedIn.set arrived
    if let some value := homeMonitor then setThreadReg emu home monitorVar value
    if let some value := targetMonitor then setThreadReg emu target monitorVar value
    emu.turnUsed.set turn

/-- The numbers of the calls of tasks that the kernel has no `Call` for: `set_robust_list`, `get_robust_list`, `clock_settime`, with
that of 64 bits where there is one, and `clone` and `clone3`. -/
private def taskNumbers : Architecture → Nat × Nat × List Nat × Nat × Nat
  | .x86_64 => (273, 274, [227], 56, 435)
  | .i686 => (311, 312, [264, 404], 120, 435)
  | .arm => (338, 339, [262, 404], 120, 435)
  | .aarch64 | .riscv64 => (99, 100, [112], 220, 435)
  | .riscv32 => (99, 100, [404], 220, 435)
  | .mips 32 _ _ => (4309, 4310, [4262, 4404], 4120, 4435)
  | .mips _ _ _ => (5268, 5269, [5221], 5055, 5435)
  | .powerpc 32 _ => (300, 299, [245, 404], 120, 435)
  | .powerpc _ _ => (300, 299, [245], 120, 435)

/-- A thread that ends lets go of the locks of its robust list, as `exit_robust_list` has it: of each futex word of the list, and of the
one that it was about to take or to let go of, that holds its id, the word says that its owner died, `FUTEX_OWNER_DIED`, keeps
`FUTEX_WAITERS`, and one thread that waits on it is woken, which takes the lock and finds that out. A lock of priority inheritance
that others wait for in the kernel goes to the first of them, with the bit. No further than 2048 entries, as Linux has it, nor than
the list can be read. It runs in the memory of the thread, which is still there. -/
private def releaseRobust (machine : Machine) (emu : Emu) (tid : Nat) : IO Unit := do
  let some head := (← machine.notes.get).robust.get? tid | return
  machine.notes.modify fun notes => { notes with robust := notes.robust.erase tid }
  let architecture := machine.architecture
  let word := architecture.bits / 8
  let big := architecture.big
  let table ← emu.taskTable.get
  let some task := table.find? tid | return
  let walk : IO Unit := do
    let numberAt_ (address size : Nat) : IO (Option Nat) := do
      match ← (read emu address size).toBaseIO with
      | .ok bytes => pure (some (numberAt bytes 0 size big))
      | .error _ => pure none
    let some first ← numberAt_ head word | return
    let some offset ← numberAt_ (head + word) word | return
    let some pending ← numberAt_ (head + 2 * word) word | return
    let wakeOne (address : Nat) : IO Unit := do
      let (space, key) ← match ← emu.futexKey.get with
        | some key => pure ((← key address).getD (task.space, address))
        | none => pure (task.space, address)
      let (table, woken) := (← emu.taskTable.get).futexWake space key (2 ^ 32 - 1) 1
      emu.taskTable.set table
      for other in woken do wakeThread emu other
    let handle (entry : Nat) (pi pendingOp : Bool) : IO Unit := do
      let address := (entry + offset) % 2 ^ architecture.bits
      if address % 4 != 0 then return
      let some value ← numberAt_ address 4 | return
      if pendingOp && !pi && value == 0 then return ← wakeOne address
      if value % 2 ^ 30 != tid then return
      let (space, key) ← match ← emu.futexKey.get with
        | some found => pure ((← found address).getD (task.space, address))
        | none => pure (task.space, address)
      let table ← emu.taskTable.get
      let (heirs, rest) := if pi then table.futexes.partition fun waiter => waiter.space == space && waiter.address == key && waiter.bitset == 2 ^ 32
        else ([], table.futexes)
      let changed := match heirs with
        | next :: others => next.thread ||| 2 ^ 30 ||| (if others.isEmpty then 0 else 2 ^ 31)
        | [] => (value &&& 2 ^ 31) ||| 2 ^ 30
      if let .error _ ← (write emu address (Abi.field big 4 changed)).toBaseIO then return
      match heirs with
      | next :: others =>
        emu.taskTable.set { table with futexes := rest ++ others }
        setSyscallResult emu next.thread (.ok 0)
        wakeThread emu next.thread
      | [] => if !pi && value &&& 2 ^ 31 != 0 then wakeOne address
    let mut entry := first
    for _ in [0:2048] do
      let at_ := entry / 2 * 2
      if at_ == head then break
      -- Where it goes on is read before the lock is let go of, which may let another thread take the entry away.
      let next ← numberAt_ at_ word
      if at_ != pending / 2 * 2 then handle at_ (entry % 2 == 1) false
      let some next := next | break
      entry := next
    if pending / 2 * 2 != 0 then handle (pending / 2 * 2) (pending % 2 == 1) true
  -- What it wrote of memory that processes share is in the file of that before the mappings of a process that is over go.
  let walk : IO Unit := do
    walk
    flushShared machine emu
  if table.spaceOf tid == table.spaceOf (← thread emu) then walk else inThread emu tid walk

/-- The calls of tasks that the kernel has no `Call` for, of what `TaskNotes` keeps: `set_robust_list`, of a head of the size that
there is, `get_robust_list`, of a thread that there is, and `clock_settime`, of which the clock of the machine, which is all of its
clocks, can't be set: of the clock of the day and those of processor time, `EPERM`, once what it is given is looked at, and of any
other, `EINVAL`. -/
private def serveTaskNotes (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu number args => do
    let architecture := machine.architecture
    let (setRobust, getRobust, setTime, _, _) := taskNumbers architecture
    let arg (index : Nat) : Nat := args.getD index 0
    let word := architecture.bits / 8
    let tid ← thread emu
    if number == setRobust then
      if arg 1 != 3 * word then return ← handOver machine emu (errorOf Errno.einval)
      machine.notes.modify fun notes => { notes with robust := if arg 0 == 0 then notes.robust.erase tid else notes.robust.insert tid (arg 0) }
      handOver machine emu (.returnValue 0)
    else if number == getRobust then
      let target := if arg 0 % 2 ^ 32 == 0 then tid else arg 0 % 2 ^ 32
      let some other := (← emu.taskTable.get).tasks.find? fun task => task.tid == target && task.status.isNone
        | return ← handOver machine emu (errorOf 3)
      -- Of a thread of another user, without `CAP_SYS_PTRACE`, `EPERM`, as `ptrace_may_access` has it.
      let kernel ← machine.kernel.get
      let (mine, theirs) := ((kernel.process (← currentTask emu).group).credentials, (kernel.process other.group).credentials)
      if !(mine.uid == theirs.euid && mine.uid == theirs.suid && mine.uid == theirs.uid) && !mine.capable 19 then
        return ← handOver machine emu (errorOf Errno.eperm)
      let head := ((← machine.notes.get).robust.get? target).getD 0
      let written ← (do
        writeGuest emu (arg 2) (Abi.field architecture.big word (3 * word))
        writeGuest emu (arg 1) (Abi.field architecture.big word head)
        pure true).catchExceptions fun _ => pure false
      handOver machine emu (if written then .returnValue 0 else errorOf Errno.efault)
    else if setTime.contains number then
      let clock := arg 0 % 2 ^ 32
      if clock != 0 && clock != 2 && clock != 3 then return ← handOver machine emu (errorOf Errno.einval)
      let size := if number % 1000 == 404 then 8 else word
      match ← (read emu (arg 1) (2 * size)).toBaseIO with
      | .error _ => handOver machine emu (errorOf Errno.efault)
      | .ok bytes =>
        let seconds := numberAt bytes 0 size architecture.big
        let fraction := numberAt bytes size size architecture.big % 2 ^ architecture.bits
        if clock == 0 && (seconds ≥ 2 ^ (8 * size - 1) || fraction ≥ 1000000000) then handOver machine emu (errorOf Errno.einval)
        else handOver machine emu (errorOf Errno.eperm)
    else pure .default

/-- The clock of the kernel goes on by the instructions that have run since it last did, at `instructionNanos` each, as a device's does
by the work that it does: what a program times is that work, and not the host or a step for each time that it looks. Every clock is
this one, of `clock_gettime`, the deadlines of waits, the timers and `CNTVCT_EL0`, so that none disagrees with another; and it is in
the kernel, which a checkpoint has. It goes on as each system call starts, as the counter is read, at the end of each turn and before
the machine is kept, so that what reads it has every instruction up to it counted (`Emu.retired`). -/
private def Machine.advanceClock (machine : Machine) : IO Unit := do
  let retired ← machine.emu.retired.get
  let counted ← machine.clockCounted.get
  if retired > counted then
    machine.kernel.modify fun kernel => { kernel with clock := kernel.clock + (retired - counted) * instructionNanos }
    machine.clockCounted.set retired

/-- `CNTVCT_EL0` and `CNTPCT_EL0`, which `a64-counter` reads once `virtual-counter` has set it: the clock of the kernel in ticks of
`CNTFRQ_EL0` since boot. -/
private def serveCounter (machine : Machine) (emu : Emu) : IO Unit := do
  let _ ← onIntrinsic emu "virtual-counter" fun current _ => do
    machine.advanceClock
    setReg current (word "CNTVCT_EL0") (bits 64 (((← machine.kernel.get).clock - bootClock) / counterNanos))
    pure .proceed
  pure ()

/-- What a program of RISC-V, MIPS or PowerPC reads of its processor that isn't of its state, which the semantics leave to intrinsics.
Each is of an instruction that writes a register, which its hook does, by the fields of the instruction: what follows an intrinsic in
its code doesn't run once a hook has served it.
- RISC-V, `riscv_csr_time` and, of RV32, `riscv_csr_timeh`: the CSR `time` and its upper half, the clock of the kernel since boot in
  ticks of 100 ns, a time base of 10 MHz;
- MIPS, `mips_count`: `RDHWR` of the count, `CC`, which goes on by one each two cycles, a cycle being an instruction's time, of
  which the register has the low word, sign-extended;
- PowerPC, `time-base`: `mftb` and `mfspr` of the time base, 268, or of its upper half, 269, the clock of the kernel since boot in
  ticks of a time base of 512 MHz; and `darn`, a random number of 32 bits conditioned, of 64 conditioned, or of 64 raw, by its `L`,
  from where `getrandom` has its bytes, and all the bits, which is how it says that it failed, of the `L` that is reserved. -/
private def serveProcessor (machine : Machine) (emu : Emu) : IO Unit := do
  let wide := machine.architecture.bits
  -- The word of the instruction, and a field of it.
  let instruction (current : Emu) (pc : Nat) : IO Nat := do
    let bytes := (← read current pc 4).toList
    pure ((if machine.architecture.big then bytes else bytes.reverse).foldl (fun value byte => value * 256 + byte.toNat) 0)
  let field (word low size : Nat) : Nat := (word >>> low) % 2 ^ size
  let elapsed : IO Nat := do
    machine.advanceClock
    pure ((← machine.kernel.get).clock - bootClock)
  -- A general register by its number, of which the one that is zero isn't written. The result of the intrinsic, of its width, is
  -- there too, for what runs the rest of the instruction after it.
  let write (current : Emu) (pre : String) (number value : Nat) (zero : Bool := true) (result : Nat := wide) : IO Unit := do
    setReg current ⟨"intrinsic:y0", .imm result, 0, false⟩ (bits result value)
    unless zero && number == 0 do
      setReg current ⟨s!"{pre}{number}", .imm wide, 0, false⟩ (bits wide value)
  match machine.architecture with
  | .riscv64 | .riscv32 =>
    for (name, high) in [("riscv_csr_time", false), ("riscv_csr_timeh", true)] do
      let _ ← onIntrinsic emu name fun current pc => do
        let ticks := (← elapsed) / 100 % 2 ^ 64
        write current "X" (field (← instruction current pc) 7 5) (if high then ticks >>> 32 else ticks)
        pure .proceed
  | .mips .. =>
    let _ ← onIntrinsic emu "mips_count" fun current pc => do
      let count := (← elapsed) / (2 * instructionNanos) % 2 ^ 32
      write current "R" (field (← instruction current pc) 16 5) (if count ≥ 2 ^ 31 then count + 2 ^ wide - 2 ^ 32 else count)
        (result := 32)
      pure .proceed
  | .powerpc .. =>
    let _ ← onIntrinsic emu "time-base" fun current pc => do
      let word ← instruction current pc
      let ticks := (← elapsed) * 512 / 1000 % 2 ^ 64
      let upper := field word 16 5 + 32 * field word 11 5 == 269
      write current "R" (field word 21 5) (if upper then ticks >>> 32 else ticks) (zero := false)
      pure .proceed
    let _ ← onIntrinsic emu "darn" fun current pc => do
      let word ← instruction current pc
      let size := match field word 16 2 with
        | 0 => 4
        | 3 => 0
        | _ => 8
      let given := (← machine.kernel.get).randomGiven
      machine.kernel.modify fun kernel => { kernel with randomGiven := given + size }
      let random := (Kernel.randomBytes given size).toList.foldl (fun value byte => value * 256 + byte.toNat) 0
      -- All the bits are what an error is, which a number isn't.
      let value := if size == 0 then 2 ^ 64 - 1 else if size == 8 && random == 2 ^ 64 - 1 then 0 else random
      write current "R" (field word 21 5) value (zero := false)
      pure .proceed
  | _ => pure ()

/-- What makes an emulator a machine: its kernel behind its system calls. None of it is in a checkpoint. -/
private def machineOf (architecture : Architecture) (emu : Emu) (kernel : Kernel) (watch : Option (Nat → List Nat → IO Unit))
    (handler : Option SyscallHandler) (target : Nat) (models : List RuntimeModel) : IO Machine := do
  let signals : Signals := { architecture, returnPage := stackTop architecture + 4096, table := ← IO.mkRef {}
                             failures := ← IO.mkRef #[], skipIgnoredFaults := ← IO.mkRef false
                             intercept := ← IO.mkRef fun _ _ _ => pure false, tracer := ← IO.mkRef fun _ => pure none
                             jobControl := ← IO.mkRef fun _ _ _ => pure (), interrupted := ← IO.mkRef fun _ _ _ _ _ => pure ()
                             sent := ← IO.mkRef fun _ => pure (), taken := ← IO.mkRef fun _ _ => pure (), pgidOf := ← IO.mkRef pure, members := ← IO.mkRef fun _ => pure []
                             waitAnswered := ← IO.mkRef fun _ _ => pure false
                             permits := ← IO.mkRef fun _ _ _ => pure true, pendingLimit := ← IO.mkRef fun _ => pure (2 ^ 64, fun _ => true) }
  let ptrace ← Ptrace.make architecture signals
  let kernelRef ← IO.mkRef kernel
  let timers ← Timers.make architecture kernelRef signals
  let machine : Machine := { architecture, emu, kernel := kernelRef, models := ← IO.mkRef [], target, handled := handler.isSome, signals, ptrace, timers, notifier := ← Notify.make, hostMounts := ← IO.mkRef [], rings := ← IO.mkRef {}, releases := ← IO.mkRef 0, siblingFaults := ← IO.mkRef (0, 0, none), heaps := ← IO.mkRef {}, libraries := ← IO.mkRef {}, history := ← IO.mkRef none, restored := ← IO.mkRef [], listing := ← IO.mkRef none, hostHooks := ← IO.mkRef {}, importSlots := ← IO.mkRef {}, clockCounted := ← IO.mkRef (← emu.retired.get), notes := ← IO.mkRef {} }
  if let some watch := watch then
    let _ ← onSyscall emu fun _ number args => do
      watch number args
      pure .default
  if let some handler := handler then
    let _ ← onSyscall emu handler
  -- The trap flag of x86: an instruction that starts with TF set is followed by the debug exception, `exc_debug_user`, which is
  -- `SIGTRAP` of `TRAP_TRACE` at the instruction after it. Its handler runs without the flag, as every handler does, and the frame
  -- has it, so that `sigreturn` sets it again. While a thread has it, a hook of every instruction looks: it is put there by what
  -- sets the flag, `popf`, which says so (`trap-flag`), and a call that ends, as `sigreturn` does, and goes once no thread has it.
  if architecture matches .x86_64 | .i686 then
    let flag : Bap.Var := ⟨"TF", .imm 1, 0, false⟩
    let isSet (emu : Emu) : IO Bool := do
      match ← (reg emu flag).toBaseIO with
      | .ok value => pure (match Value.asBits value with | .ok bits => bits.2.toNat == 1 | .error _ => false)
      | .error _ => pure false
    -- Of each thread that steps, whether the instruction that it ran last started with the flag.
    let stepping ← IO.mkRef ({} : Std.HashMap Nat Bool)
    let hook ← IO.mkRef (none : Option HookId)
    let arm (emu : Emu) : IO Unit := do
      let tid ← thread emu
      if !(← stepping.get).contains tid then stepping.modify (·.insert tid false)
      if (← hook.get).isNone then
        let width ← wordWidth emu
        let id ← onCode emu (0, 2 ^ width - 1) fun current address => do
          let tid ← thread current
          let some traced := (← stepping.get).get? tid | return
          if traced then
            let group := (← currentTask current).group
            signals.force current tid group ⟨signals.trapNumber, 2, .fault address⟩
            signals.deliverPending current
            setReg current flag (bits 1 0)
          if ← isSet current then stepping.modify (·.insert tid true)
          else
            stepping.modify (·.erase tid)
            if (← stepping.get).isEmpty then
              if let some id := ← hook.get then
                removeHook current id
                hook.set none
        hook.set (some id)
    let _ ← onIntrinsic emu "trap-flag" fun current _ => do
      arm current
      pure .proceed
    emu.syscallEnds.modify ((fun _ => do if ← isSet emu then arm emu) :: ·)
  -- `syscall` of x86-64 leaves where it returns to in RCX and the flags in R11, as the instruction does before the kernel has the
  -- call, which a program sees after it: a call by `int $0x80`, through the same hooks, leaves both.
  if architecture matches .x86_64 then
    emu.syscallStarts.modify ((fun _ _ => do
      let at_ ← pc emu
      match ← (read emu at_ 2).toBaseIO with
      | .ok bytes =>
        if bytes.toList == [0x0f, 0x05] then
          let mut flags := 0
          for name in Target.LLVMLift.x86Flags do
            let bit := match Value.asBits (← reg emu ⟨name, .imm 1, 0, false⟩) with
              | .ok value => value.2.toNat % 2
              | .error _ => 0
            flags := flags * 2 + bit
          setReg emu ⟨"RCX", .imm 64, 0, false⟩ (bits 64 (at_ + 2))
          setReg emu ⟨"R11", .imm 64, 0, false⟩ (bits 64 flags)
      | .error _ => pure ()) :: ·)
  -- `arch_prctl` of the base of GS, `ARCH_SET_GS` and `ARCH_GET_GS`, as `do_arch_prctl_64` has them: a base past the addresses of a
  -- program is EPERM, and where the base can't be written EFAULT. That of FS is for `serveTaskCalls`.
  if architecture matches .x86_64 then
    let gsBase : Bap.Var := ⟨"GS_BASE", .imm 64, 0, false⟩
    let _ ← onSyscall emu fun emu number args => do
      match number, args.getD 0 0 with
      | 158, 0x1001 =>
        let base := args.getD 1 0
        if base ≥ 2 ^ 47 - 4096 then handOver machine emu (errorOf Errno.eperm)
        else
          setReg emu gsBase (bits 64 base)
          handOver machine emu (.returnValue 0)
      | 158, 0x1004 =>
        let base := match Value.asBits (← reg emu gsBase) with
          | .ok value => value.2.toNat
          | .error _ => 0
        match ← (writeGuest emu (args.getD 1 0) (Abi.bytesOf 8 base)).toBaseIO with
        | .ok _ => handOver machine emu (.returnValue 0)
        | .error _ => handOver machine emu (errorOf Errno.efault)
      | _, _ => pure .default
  -- What a process wrote to shared memory is in the file before anything can look at the file.
  let _ ← onSyscall emu fun emu _ _ => do
    flushShared machine emu
    -- What the call reads and writes of the program is as the program was given it.
    protectSiblings machine emu true
    -- What the call walks is within the root of its process.
    if let some group ← runningGroup emu then
      let kernel ← machine.kernel.get
      let root := kernel.baseIn (kernel.process group).root
      machine.kernel.set { kernel with walkRoot := root, walkSearch := some ((kernel.process group).credentials, false) }
    pure .default
  emu.leavingSpace.set (some (flushShared machine emu))
  -- What was found of the instances of `inotify` is of the kernel that was.
  machine.restored.modify ((fun _ => Notify.forget machine.notifier) :: ·)
  -- The mappings of what comes to run hold what their files do, and are as long.
  emu.enteredSpace.set (some do
    refreshShared machine emu
    settleMappings machine emu
    protectSiblings machine emu false)
  -- A call may have made a file longer or shorter, or mapped one, and is over.
  emu.syscallEnds.modify (· ++ [fun (_ : Option Nat) => do
    settleMappings machine emu
    protectSiblings machine emu false])
  emu.futexKey.set (some fun address => do
    let some group ← runningGroup emu | return none
    let mappings := ((← machine.kernel.get).process group).mappings
    pure ((mappings.find? fun mapping => mapping.shared && mapping.overlaps address (address + 1)).map fun mapping =>
      (sharedFutexSpace + mapping.inode, mapping.offset + (address - mapping.start))))
  for model in models do
    let _ ← machine.attachModel model
  -- Signals are part of what it is, and it is in a checkpoint like what a model holds.
  machine.models.modify (· ++ [{ id := Signals.modelId, version := builtinVersion Signals.modelId, state := { save := signals.save, load := signals.load } }])
  -- So is what is traced and stopped, which serves the waits, and so is before the signals.
  ptrace.install emu
  -- A stop signal of the default but SIGSTOP doesn't stop a process group that is orphaned, as `get_signal` has it, as nothing would
  -- let it go on: none of it has a parent in another group of its session. The first process has a parent as a shell would be, which
  -- is of another group of its session.
  let (stopSignal, contSignal) := if architecture matches .mips .. then (23, 25) else (19, 18)
  signals.jobControl.set fun emu group signal => do
    if signal != stopSignal && signal != contSignal then
      let kernel ← kernelRef.get
      let table ← emu.taskTable.get
      if Identity.orphaned kernel (← liveProcesses emu) (fun member => (table.find? member).map (·.parent)) (kernel.pgidOf group) then
        return
    -- A thread that a stop finds waiting in `epoll_wait` leaves it with `EINTR`, which it has when its process goes on, whatever
    -- handlers there are: Linux doesn't make that call again, as it does a sleep or a read.
    if signal != contSignal then
      let calls := (← machine.notes.get).calls
      let table ← emu.taskTable.get
      for task in table.tasks do
        if task.group == group && task.status.isNone && task.tid != (← thread emu) then
          let waits := ((calls.get? task.tid).bind architecture.call).any [Call.epollWait, .epollPwait, .epollPwait2].contains
          if waits && table.futexes.any (fun waiter => waiter.thread == task.tid && waiter.space == readySpace) then
            signals.breakCall emu task.tid
    ptrace.jobControl emu group signal
  machine.models.modify (· ++ [{ id := Ptrace.modelId, version := builtinVersion Ptrace.modelId, state := { save := ptrace.save, load := ptrace.load emu } }])
  -- And what a thread may call, which ptrace asks of each call once a tracer saw it start.
  let seccomp ← Seccomp.attach architecture signals ptrace emu
  machine.models.modify (· ++ [{ id := Seccomp.modelId, version := builtinVersion Seccomp.modelId, state := seccomp.modelState emu }])
  -- Time goes on as instructions run, and to what happens next when nothing can.
  emu.now.set (some do pure (← kernelRef.get).clock)
  -- The thread that is current, which a timer or a deadline woke there, takes what came for it, as a switch to it would have it; and
  -- one that runs takes what a timer sent it where it is, as an interrupt has it, rather than at the end of its next system call.
  let resumingCurrent (action : IO Bool) : IO Bool := do
    let waited ← Bap.Emu.stopped emu
    let changed ← action
    if waited && !(← Bap.Emu.stopped emu) then
      signals.switchedIn emu
      timers.resumed emu
    else if !waited then signals.deliverPending emu
    pure changed
  emu.idle.set (some (resumingCurrent (timers.idle emu)))
  -- A signal that comes has what waits to read one look again, and what it woke from a call that runs again hear of it.
  signals.sent.set wakePipeReaders
  signals.pgidOf.set fun group => do pure ((← kernelRef.get).pgidOf group)
  -- Who may send a signal to whom, as `kill_ok_by_cred` has it: to its own process, to one whose real or saved user is its real or
  -- effective one, to any with `CAP_KILL`, which is 5, and SIGCONT to any of its session.
  signals.permits.set fun sender target signal => do
    let kernel ← kernelRef.get
    let (mine, theirs) := ((kernel.process sender).credentials, (kernel.process target).credentials)
    let cont := if architecture matches .mips .. then 25 else 18
    pure (sender == target || mine.euid == theirs.suid || mine.euid == theirs.uid || mine.uid == theirs.suid || mine.uid == theirs.uid ||
      mine.capable 5 || (signal == cont && kernel.sidOf sender == kernel.sidOf target))
  signals.pendingLimit.set fun group => do
    let kernel ← kernelRef.get
    let user := (kernel.process group).credentials.uid
    pure ((kernel.limitOf group 11).1, fun other => (kernel.process other).credentials.uid == user)
  signals.members.set fun pgid => do
    let present := ((← emu.taskTable.get).present.map (·.group)).eraseDups
    pure (Identity.members (← kernelRef.get) present pgid)
  signals.interrupted.set fun emu tid restart spaces traced => do
    timers.interrupted emu tid restart spaces traced
    if traced then ptrace.restarted emu tid
  signals.taken.set timers.taken
  -- The clock goes on first, so that the timers and the deadlines go by what ran.
  emu.betweenTurns.modify (· ++ [machine.advanceClock])
  emu.syscallStarts.modify (· ++ [fun (_ : Nat) (_ : List Nat) => machine.advanceClock])
  if architecture == .aarch64 then serveCounter machine emu
  serveProcessor machine emu
  -- A system call leaves the streaming mode of SME and discards the predicates of SVE, as Linux's `fp_user_discard` has it, before what
  -- serves it, e.g., `clone`, sees it.
  if architecture == .aarch64 then emu.syscallStarts.modify (· ++ [fun (_ : Nat) (_ : List Nat) => Signals.leaveStreamingMode emu false])
  emu.betweenTurns.modify (· ++ [do let _ ← resumingCurrent (do timers.tick emu; pure true)])
  -- A thread that goes on running turn after turn has time go on with it: at the end of each turn the timers that are due send
  -- their signals, of which it takes its own there, and what waited until a time that has come is one to run next.
  emu.turnEnds.modify (· ++ [do
    machine.advanceClock
    let _ ← resumingCurrent (do timers.tick emu; pure true)])
  emu.betweenTurns.modify (· ++ [settleRings machine emu])
  let timeState : ModelState := { save := timers.save, load := timers.load }
  machine.models.modify (· ++ [{ id := Timers.modelId, version := builtinVersion Timers.modelId, state := timeState }])
  -- And what AIO and io_uring have.
  machine.models.modify (· ++ [{ id := Ring.modelId, version := builtinVersion Ring.modelId
                                 state := { save := Ring.save machine.rings, load := Ring.load machine.rings } }])
  -- What the timers and the rings keep of a thread goes with it when it takes its leader's id.
  emu.leaderTaken.modify (· ++ [fun (former leader : Nat) => do
    timers.state.modify fun state =>
      { state with
        deadlines := moveThread state.deadlines former leader, sites := moveThread state.sites former leader
        sleeps := moveThread state.sleeps former leader }
    machine.rings.modify fun state =>
      { state with submitted := state.submitted.filterMap fun (tid, at_, count) =>
          if tid == leader then none else some (if tid == former then leader else tid, at_, count) }])
  signals.serve emu
  -- A fault where a file that is mapped has no page is of the bus.
  emu.faultHandler.set (some fun fault => do
    if ← siblingFault machine emu fault then return true
    if ← growStack machine emu fault then return true
    -- What an instruction that was run by itself did is what faulted.
    let fault := (← failure emu).getD fault
    signals.faulted emu fault (← isPastEnd machine emu fault.address))
  -- A thread that a switch has run again has what was left of a sleep that a signal ended.
  let arrived ← emu.switchedIn.get
  emu.switchedIn.set (some do
    if let some arrived := arrived then arrived
    timers.resumed emu)
  -- What is kept of the tasks is in a checkpoint too.
  machine.models.modify (· ++ [{ id := notesModelId, version := builtinVersion notesModelId
                                 state := { save := do pure (← machine.notes.get).encode
                                            load := fun data => do machine.notes.set (← IO.ofExcept (TaskNotes.decode data)) } }])
  -- A task that is about to end lets go of the locks of its robust list, and the children that its process has are kept for
  -- what hears that the process is over, when they have another parent.
  emu.taskExiting.modify (· ++ [fun (tid : ThreadId) => do
    let table ← emu.taskTable.get
    if let some task := table.find? tid then
      machine.notes.modify fun notes => { notes with children := notes.children.insert task.group (table.childrenOf task.group) }
    releaseRobust machine emu tid
    machine.notes.modify fun notes =>
      { notes with deathSignals := notes.deathSignals.erase tid, cloning := notes.cloning.erase tid, calls := notes.calls.erase tid }])
  -- The call that each thread makes, and of `clone`, its flags, for what hears of the process that it makes.
  let (_, _, _, cloneNumber, clone3Number) := taskNumbers architecture
  emu.syscallStarts.modify (· ++ [fun (number : Nat) (args : List Nat) => do
    let tid ← thread emu
    let flags ← if number == cloneNumber then pure (some (args.getD 0 0))
      else if number == clone3Number then do
        match ← (read emu (args.getD 0 0) 8).toBaseIO with
        | .ok bytes => pure (some (numberAt bytes 0 8 architecture.big))
        | .error _ => pure none
      else pure none
    machine.notes.modify fun notes =>
      { notes with calls := notes.calls.insert tid number
                   cloning := match flags with
                     | some flags => notes.cloning.insert tid flags
                     | none => notes.cloning.erase tid }])
  -- What a process does to its descriptors is done to those of the processes that share them with it, `CLONE_FILES`, as they have
  -- one table: each has the table as the call left it.
  emu.syscallEnds.modify (· ++ [fun (_ : Option Nat) => do
    let sets := (← machine.notes.get).files
    if sets.isEmpty then return
    let some group ← runningGroup emu | return
    if let some sharing := sets.find? (·.contains group) then
      machine.kernel.modify fun kernel =>
        let descriptors := (kernel.process group).descriptors
        sharing.foldl (init := kernel) fun kernel other =>
          if other == group || (kernel.process other).ended then kernel
          else kernel.setProcess other { kernel.process other with descriptors }])
  -- A process that is over has closed what it had open.
  let heard ← emu.processExited.get
  emu.processExited.set (some fun group status => do
    if let some heard := heard then heard group status
    -- Each descriptor that it had is closed, as `__fput` has it, which `inotify` hears of; and then it holds nothing.
    let live ← liveProcesses emu
    for (fd, _) in ((← kernelRef.get).process group).descriptors.toList do
      let before ← kernelRef.get
      if let .ok next := before.close group fd then
        kernelRef.set next
        let _ ← Notify.after machine.notifier kernelRef group .close [fd] before (.returnValue 0) live
    -- The leader of a session lets its terminal go, of which its foreground job hears.
    if (← kernelRef.get).sidOf group == group then Tty.disassociate (pollerOf machine) emu group true
    -- What `SEM_UNDO` did of it is taken back, its segments are let go, its timers end, and what `inotify` it had is looked for again.
    kernelRef.modify (SysV.exited · group)
    kernelRef.modify (·.exitProcess group)
    -- A group that this exit orphans, of which something is stopped, hears SIGHUP and SIGCONT, as Linux's `kill_orphaned_pgrp` has
    -- it: its own, if its parent was of another group of its session, and that of each child that it had which was, as their
    -- link to the rest of the session was this process. A group that was orphaned before, or one that has nothing to do with
    -- this process, hears nothing of it. The first process has a parent as a shell would be.
    let kernel ← kernelRef.get
    let table ← emu.taskTable.get
    let alive := (← liveProcesses emu).filter (· != group)
    let parentOf (other : Nat) : Option Nat := (table.find? other).map (·.parent)
    let apart (parent child : Nat) : Bool := kernel.pgidOf parent != kernel.pgidOf child && kernel.sidOf parent == kernel.sidOf child
    let linked (pgid : Nat) : Bool := alive.any fun member => kernel.pgidOf member == pgid && match parentOf member with
      | some parent => parent == 0 || (alive.contains parent && apart parent member)
      | none => false
    let own := match parentOf group with
      | some parent => if parent == 0 || apart parent group then [kernel.pgidOf group] else []
      | none => []
    let notes ← machine.notes.get
    let had := notes.children.getD group []
    let children := (had.filter fun child => alive.contains child && apart group child).map kernel.pgidOf
    for pgid in (own ++ children).eraseDups do
      let members := alive.filter (kernel.pgidOf · == pgid)
      if !linked pgid && (← members.anyM (ptrace.jobStopped emu)) then
        let cont := if machine.architecture matches .mips .. then 25 else 18
        for member in members do
          for signal in [1, cont] do signals.send emu none member ⟨signal, 0x80, .sent 0 0 0⟩
    -- Its children go to the nearest of its ancestors that takes them in, `PR_SET_CHILD_SUBREAPER`, as `find_new_reaper` has it,
    -- rather than to the first process; and each thread of them that asked to hear of its parent's end, `PR_SET_PDEATHSIG`, has
    -- its process sent that signal.
    let first := (table.tasks.head?.map (·.tid)).getD 0
    let reaper : Option Nat := Id.run do
      let mut at_ := group
      for _ in [0:table.tasks.length + 1] do
        match parentOf at_ with
        | none | some 0 => return none
        | some parent =>
          if parent == first then return none
          if notes.subreapers.contains parent && alive.contains parent then return some parent
          at_ := parent
      return none
    if let some reaper := reaper then
      let adopted (task : Tasks.Entry) : Tasks.Entry :=
        if had.contains task.group && task.parent == first then { task with parent := reaper } else task
      emu.taskTable.modify fun table => { table with tasks := table.tasks.map adopted }
    for task in table.tasks do
      if had.contains task.group && task.status.isNone then
        if let some signal := notes.deathSignals.get? task.tid then
          signals.send emu none task.group ⟨signal, 0, .sent group 0 0⟩
    -- What was kept of it goes with it, and what shared its descriptors has them without it.
    machine.notes.modify fun notes => { notes with
      children := notes.children.erase group, dumpable := notes.dumpable.erase group, subreapers := notes.subreapers.erase group
      files := (notes.files.map (·.erase group)).filter (·.length > 1) }
    timers.exited emu group
    Notify.forget machine.notifier
    released machine
    wakePipeReaders emu
    Tty.hangUp (pollerOf machine) emu
    ptrace.processExited emu group status)
  -- So is what was allocated in it, as what has an address has to go on having it.
  machine.models.modify (· ++ [{
    id := heapModelId, version := builtinVersion heapModelId,
    state := {
      save := do
        -- Of what is still there, as a process that went doesn't say so.
        let table ← emu.taskTable.get
        pure (GuestHeap.encode ((← machine.heaps.get).filter fun space _ => table.tasks.any (·.space == space)))
      load := fun data => do machine.heaps.set (← IO.ofExcept (GuestHeap.decode data)) } }])
  -- And the trace, whose pcs and accesses a machine of a checkpoint has as the one it was of did, rather than none.
  machine.models.modify (· ++ [{
    id := traceModelId, version := builtinVersion traceModelId,
    state := { save := traceSave emu, load := traceLoad emu } }])
  machine.models.modify (· ++ [{
    id := libraryModelId, version := builtinVersion libraryModelId,
    state := {
      save := do
        let table ← emu.taskTable.get
        pure (LoadedLibrary.encode ((← machine.libraries.get).filter fun space _ => table.tasks.any (·.space == space)))
      load := fun data => do machine.libraries.set (← IO.ofExcept (LoadedLibrary.decode data)) } }])
  let _ ← onSyscall emu fun emu number args => do
    if let some call := (machine.architecture.call number).filter [Call.execve, .execveat].contains then
      let former ← thread emu
      let action ← handOver machine emu (← execute { machine with emu } emu call args)
      -- It is a new program if it is going there, and nothing else sends it anywhere in the middle of a system call.
      if (← emu.redirect.get).isSome then
        signals.executed (← currentTask emu).group (← thread emu)
        ptrace.executed emu former
        -- What it had is gone with its memory.
        let space := (← currentTask emu).space
        machine.heaps.modify (·.erase space)
        machine.libraries.modify (·.erase space)
      pure action
    else pure .default
  let _ ← serveTaskNotes machine
  let _ ← serveKernelCalls machine
  let _ ← serveTaskCalls emu
  let _ ← serveRest machine
  if architecture == .x86_64 || architecture == .i686 then serveCpu emu machine.kernel architecture.bits
  serveIllegalInstructions machine emu
  serveTraps machine emu
  -- What was advised for a child of `fork`: what it leaves out isn't mapped there, and what it wipes is zeros, but a child that has its
  -- parent's memory, of `vfork`, has it as it is. This comes once the child is a process of the kernel.
  emu.processHooks.modify ((fun _ child => do
    let table ← emu.taskTable.get
    let advice := ((← machine.kernel.get).process child).forkAdvice
    if advice.isEmpty || table.spaceOf child == table.spaceOf (← thread emu) then return
    machine.kernel.modify fun kernel =>
      advice.foldl (fun kernel advice => if advice.wipe then kernel else kernel.dropMappings child advice.start (advice.start + advice.size)) kernel
    inThread emu child do
      for advice in advice do
        if advice.wipe then clearMapped emu advice.start advice.size else unmap emu advice.start advice.size) :: ·)
  -- A new process is dumpable as its parent is, and of `CLONE_FILES`, has its parent's descriptors as its own.
  emu.processHooks.modify ((fun parent child => do
    let notes ← machine.notes.get
    let flags := (notes.cloning.get? (← thread emu)).getD 0
    let files := if flags &&& 0x400 == 0 then notes.files
      else match notes.files.find? (·.contains parent) with
        | some sharing => (notes.files.filter (· != sharing)) ++ [sharing ++ [child]]
        | none => notes.files ++ [[parent, child]]
    machine.notes.set { notes with
      files
      dumpable := match notes.dumpable.get? parent with
        | some value => notes.dumpable.insert child value
        | none => notes.dumpable }) :: ·)
  emu.processHooks.modify ((fun parent child => machine.kernel.modify (·.fork parent child)) :: ·)
  -- A new process has its own copy of the memory, and what is allocated in it.
  emu.processHooks.modify ((fun _ child => do
    let space := (← currentTask emu).space
    machine.heaps.modify fun heaps => match heaps.get? space with
      | some heap => heaps.insert child heap
      | none => heaps) :: ·)
  emu.processHooks.modify ((fun _ child => do
    let space := (← currentTask emu).space
    machine.libraries.modify fun table => match table.get? space with
      | some libraries => table.insert child libraries
      | none => table) :: ·)
  pure machine

/-- What a program is to a checkpoint: its architecture and its bytes. -/
def targetDigest (architecture : Architecture) (program : ByteArray) : Nat :=
  let (number, bits, big, flags) := architecture.elf
  (Wire.digest program (Wire.digest s!"{number} {bits} {big} {flags}".toUTF8)).toNat

/-- A machine at the start of `path`, which is in `kernel`. Its first process has the standard descriptors, on a console, with
`input` to read. `watch` sees each system call before it is served, and then `handler`, which may serve it in place of the kernel. A position-independent program goes at `base` if one is given, such as 0 for where it was linked, and otherwise where Linux would put it. That is the program
alone: its interpreter, and what it runs with `execve`, go where they always do. At 0, its first page is at address 0, so that a null pointer into it reads it instead of faulting, as on
Linux it can't. -/
def start (kernel : Kernel) (path : String) (arguments : List String) (environment : List String := [])
    (input : ByteArray := ByteArray.empty) (watch : Option (Nat → List Nat → IO Unit) := none)
    (handler : Option SyscallHandler := none) (models : List RuntimeModel := []) (base : Option Nat := none) : IO Machine := do
  let data ← IO.ofExcept ((fileOf kernel path).mapError fun errno => s!"{path}: error {errno}")
  let program ← IO.ofExcept (Elf.parse data)
  if let some at_ := base then
    if !program.relocatable && at_ != 0 then
      throw <| IO.userError s!"{path} isn't position-independent: it goes where it was linked, and only a base of 0 says that"
    if at_ % 4096 != 0 then
      throw <| IO.userError s!"a base of {at_} isn't at the start of a page"
  let some architecture := Architecture.ofElf program.machine program.bits program.big program.flags
    | throw <| IO.userError s!"{path}: no Linux machine for ELF machine {program.machine} of {program.bits} bits"
  let interpreter ← match program.interpreter with
    | none => pure none
    | some name =>
      let bytes ← IO.ofExcept ((fileOf kernel name).mapError fun errno => s!"{name}: error {errno}")
      pure (some (bytes, ← IO.ofExcept (Elf.parse bytes)))
  -- A real program runs more code than the working set of a few thousand blocks that the default is for, and past it, each one
  -- would be lifted each time it runs. Most of its code runs at its start, a few times, and compiling that takes longer than
  -- running it, up to about this threshold: at 16 a short program takes half as long again, and a long one no less.
  let emu ← emulatorOf architecture
  let first := (← currentTask emu).group
  let arguments := if arguments.isEmpty then [path] else arguments
  -- The file, from `/` and by where the links lead, as `/proc/PID/exe` has it.
  let file := match kernel.resolve "/" path with
    | .ok (file, _) => file
    | _ => path
  let (top, auxiliary) ← loadProgram emu architecture (kernel.process first).credentials path data program interpreter arguments
    environment base
  let kernel := kernel.withConsole first input
  let kernel := kernel.setProcess first { kernel.process first with
    breakStart := top, breakEnd := top, command := arguments, environment, program := file, name := commOf (Path.name path), auxiliary }
  let kernel := Proc.install kernel.installDevices
  machineOf architecture emu kernel watch handler (targetDigest architecture data) models

/-- Runs `fuel` instructions at most in turns of the scheduler, in pieces that end where `every` says from where it starts, which is what it goes by when it runs them again. Each piece ends
with shared memory in its files and what was written gone to `output`, and then `after` sees how many instructions it ran and whether that was all of them. -/
private def Machine.runPieces (machine : Machine) (output : ByteArray → IO Unit) (quantum fuel every : Nat)
    (after : Nat → Bool → IO Unit) : IO ScheduleOutcome := do
  -- What it writes goes out as the call that wrote it ends, rather than with the turn, which may be long, or not at all, of a
  -- turn that an error ends: then what is left goes out before the error does.
  let drain : IO Unit := do
    let (kernel, written) := (← machine.kernel.get).takeOutput
    if written.size > 0 then
      machine.kernel.set kernel
      output written
  let ends ← machine.emu.syscallEnds.get
  machine.emu.syscallEnds.set ((fun _ => drain) :: ends)
  let rec go : Nat → Nat → Nat → IO ScheduleOutcome
    | 0, _, _ => pure .outOfFuel
    | rounds + 1, left, since => do
      let turn := min left (min (64 * quantum) (every - since))
      let before ← machine.emu.executed.get
      let outcome ← try runProcesses machine.emu quantum turn catch error => do
        drain
        throw error
      flushShared machine machine.emu
      -- What the host walks of the tree is from its own root.
      let (kernel, written) := (← machine.kernel.get).takeOutput
      machine.kernel.set { kernel with walkRoot := "/", walkSearch := none }
      if written.size > 0 then output written
      let ran := (← machine.emu.executed.get) - before
      after ran (outcome == .outOfFuel)
      match outcome with
      | .outOfFuel =>
        let since := if since + turn ≥ every then 0 else since + turn
        if left ≤ turn then pure .outOfFuel else go rounds (left - turn) since
      | other => pure other
  try go (fuel + 1) fuel 0 finally machine.emu.syscallEnds.set ends

private def Machine.modelBytes (machine : Machine) : IO (List (AttachedModel × ByteArray)) := do
  (← machine.models.get).mapM fun model => do pure (model, ← model.state.save)

/-- It is as whole as a checkpoint has to be: not in the middle of an instruction, or from a worker of a parallel round. -/
private def Machine.keep (machine : Machine) : IO Machine.Kept := do
  if (← machine.emu.serving.get) || machine.emu.engine.deferMemorySync then
    throw <| IO.userError "a machine can't be saved in the middle of an instruction, or by a worker of a parallel round: stop the thread, and save it once the run returns"
  machine.advanceClock
  pure {
    emulator := ← snapshot machine.emu
    run := ← runState machine.emu
    kernel := ← machine.kernel.get
    models := (← machine.modelBytes).map fun (model, bytes) => (model.id, model.version, bytes)
  }

/-- What is kept goes back only if each model that is attached now has its state in it, of the version that it is: one that was
attached since, or is of another version, has nothing to go back to, and the machine would go on with what it holds now. -/
private def Machine.restoreKept (machine : Machine) (kept : Machine.Kept) : IO Unit := do
  for model in ← machine.models.get do
    match kept.models.find? (·.1 == model.id) with
    | none => throw <| IO.userError s!"model {model.id} is attached, and what is restored has nothing of it, as it was attached since"
    | some (_, version, _) =>
      if version != model.version then
        throw <| IO.userError s!"what is restored has version {version} of model {model.id}, and this is version {model.version}"
  Bap.Emu.restore machine.emu kept.emulator
  -- Which breakpoints there are is up to who is debugging it now.
  setRunState machine.emu { kept.run with breakpoints := [] }
  machine.kernel.set kept.kernel
  -- The clock is what was kept, from the instructions that have run now, which are more.
  machine.clockCounted.set (← machine.emu.retired.get)
  for model in ← machine.models.get do
    if let some (_, _, bytes) := kept.models.find? (·.1 == model.id) then model.state.load bytes

/-- What the machine is, and where it is in what it keeps for `stepBack`, if it keeps that. -/
def Machine.save (machine : Machine) : IO Machine.Saved := do
  pure { toKept := ← machine.keep, history := ← machine.history.get }

/-- The machine is what it was saved as. If it keeps a history, that is the history it had then: where it was, and what it could step back to from there, and not what it ran
after. One that was saved before it kept any has nothing to step back to, as nothing says where it was. It is refused, with nothing
restored, where a model that is attached now has nothing in what was saved, or is of another version. -/
def Machine.restore (machine : Machine) (saved : Machine.Saved) (label : String := "Machine.restore") : IO Unit := do
  machine.restoreKept saved.toKept
  if let some current := ← machine.history.get then
    machine.history.set (some (saved.history.getD { every := current.every, limit := current.limit }))
  for heard in ← machine.restored.get do heard label

/-- How a machine's instructions run from the next one on: see `ExecutionMode`. It can be changed whenever the machine isn't in the middle of an instruction, and a machine that goes on from a checkpoint
starts with the JIT, as it is no part of what is saved. -/
def Machine.setExecutionMode (machine : Machine) (mode : ExecutionMode) : IO Unit :=
  Bap.Emu.setExecutionMode machine.emu mode

def Machine.executionMode (machine : Machine) : IO ExecutionMode :=
  Bap.Emu.executionMode machine.emu

/-- Runs it until nothing can run, with what it writes to the console going to `output` as it comes. If it keeps a history, what it is when it starts is kept, as the host may have
changed it since, and so is what it is every so often after. -/
def Machine.run (machine : Machine) (output : ByteArray → IO Unit) (quantum : Nat := 100000) (fuel : Nat := 1000000000) :
    IO ScheduleOutcome := do
  let some history ← machine.history.get
    | machine.runPieces output quantum fuel (64 * quantum) fun _ _ => pure ()
  let keep (history : Machine.History) : IO Machine.History := do
    let saved := history.saved.push (history.position, quantum, ← machine.keep)
    pure { history with saved := if saved.size > history.limit then saved.extract (saved.size - history.limit) saved.size else saved }
  -- Where it already has what it is at this place, that is what the host may have changed.
  let start := match history.saved.back? with
    | some (at_, _, _) => if at_ == history.position then { history with saved := history.saved.pop } else history
    | none => history
  machine.history.set (some (← keep start))
  let since ← IO.mkRef 0
  machine.runPieces output quantum fuel history.every fun ran whole => do
    let some current ← machine.history.get | return
    let current := { current with position := current.position + ran }
    since.modify (· + ran)
    if whole && (← since.get) ≥ current.every then
      since.set 0
      machine.history.set (some (← keep current))
    else machine.history.set (some current)

/-- Starts keeping what `Machine.stepBack` needs, from here on: what the machine is each time `Machine.run` starts, and every `every` instructions, of which the latest `limit` stay. A step back runs again
at most `every` instructions, and each kept state is a copy of all memory. What it had kept before goes. Models that are attached after this aren't in what it keeps, and stay as they are when it steps back. -/
def Machine.keepHistory (machine : Machine) (every : Nat := 100000) (limit : Nat := 100) : IO Unit :=
  machine.history.set (some { every := max every 1, limit := max limit 1 })

/-- Where it is, in the instructions of all threads that `Machine.run` has run since it started keeping a history. -/
def Machine.position (machine : Machine) : IO Nat := do
  match ← machine.history.get with
  | some history => pure history.position
  | none => throw <| IO.userError "a machine that keeps no history has no position: call keepHistory first"

/-- Undoes the last `count` instructions, of whichever threads ran them, as if they had never run: memory, registers, the kernel and the models are what they were, and the next run goes on from there. It goes
back to what it kept last before that place and runs the rest again, the way the run did, in the interpreter or the JIT and without stopping at breakpoints, which stay. What the program wrote
to the console has gone out, and isn't written again. Hooks of the host see what runs again, and a handler of system calls is asked again, which has to answer the same.

What the host did in the middle of a run, such as a hook that changed memory, has to be the same when it runs again, or it is what it does then. -/
def Machine.stepBack (machine : Machine) (count : Nat := 1) : IO Unit := do
  if count == 0 then return
  let some history ← machine.history.get
    | throw <| IO.userError "a machine that keeps no history can't step back: call keepHistory first"
  if (← machine.emu.serving.get) then
    throw <| IO.userError "a machine can't step back in the middle of an instruction"
  let some (oldest, _, _) := history.saved[0]? | throw <| IO.userError "nothing has run since it started keeping a history"
  if count > history.position || history.position - count < oldest then
    throw <| IO.userError s!"it can step back {history.position - oldest} instructions at most, of what it keeps"
  let target := history.position - count
  let some index := (List.range history.saved.size).reverse.find? fun index => (history.saved[index]?.map fun entry => decide (entry.1 ≤ target)).getD false
    | throw <| IO.userError "nothing kept is before that"
  let some (at_, quantum, saved) := history.saved[index]? | throw <| IO.userError "nothing kept is before that"
  machine.restoreKept saved
  -- What hears of it forgets what it knew of after what was kept, before that runs again: which files of the host it brought in, what
  -- inotify watches, as the kernel that it goes back to has none of them.
  for heard in ← machine.restored.get do heard s!"Machine.stepBack {count}"
  if target > at_ then
    let muted ← machine.emu.breakpointsMuted.get
    machine.emu.breakpointsMuted.set true
    try
      let _ ← machine.runPieces (fun _ => pure ()) quantum (target - at_) history.every fun _ _ => pure ()
    finally
      machine.emu.breakpointsMuted.set muted
  -- What came after is what may not happen again.
  machine.history.set (some { history with position := target, saved := history.saved.extract 0 (index + 1) })

/-! Memory of a guest for who runs it. -/

/-- Runs this in the address space of a process, which is that of the thread that runs if it is of that process, as `inThread` does, as a
look at memory isn't to change what a guest does. It can't be done in the middle of an instruction. -/
private def Machine.inProcess (machine : Machine) (pid : Option Nat) (action : IO α) : IO α := do
  let emu := machine.emu
  let home ← thread emu
  let some wanted := pid | action
  let table ← emu.taskTable.get
  if (table.find? home).map (·.group) == some wanted then return ← action
  let some target := table.tasks.find? (fun task => task.group == wanted && task.status.isNone)
    | throw <| IO.userError s!"no running process {wanted}"
  if ← emu.serving.get then
    throw <| IO.userError "the memory of another process can't be reached in the middle of an instruction: stop the thread, and do it once the run returns"
  inThread emu target.tid action

/-- The bytes at a virtual address, of the process that runs or of the one given, as the program itself could read them: what isn't
mapped or readable is an error. -/
def Machine.read (machine : Machine) (address size : Nat) (pid : Option Nat := none) : IO ByteArray :=
  machine.inProcess pid (Bap.Emu.read machine.emu address size)

/-- Writes at a virtual address, of the process that runs or of the one given, as the program itself could: what isn't mapped or
writable is an error, and then nothing has been written. Code that it changes runs as changed. -/
def Machine.write (machine : Machine) (address : Nat) (data : ByteArray) (pid : Option Nat := none) : IO Unit :=
  machine.inProcess pid do
    let emu := machine.emu
    let regions ← emu.regions.get
    -- What has to hold all of it, to have written none of it otherwise.
    let rec pieces : Nat → Nat → List (Nat × Nat) → IO (List (Nat × Nat))
      | 0, _, done => pure done.reverse
      | fuel + 1, position, done => do
        if position ≥ address + data.size then return done.reverse
        match lookupRegion regions position with
        | none => throw <| IO.userError s!"unmapped address {position}"
        | some region =>
          if !region.protection.writable then throw <| IO.userError s!"read-only address {position}"
          let stop := min (region.address + region.data.size) (address + data.size)
          pieces fuel stop ((position, stop) :: done)
    let parts ← pieces (regions.length + 1) address []
    for starts in ← emu.hostStarts.get do starts s!"Machine.write {address} {data.size}"
    try
      for (first, stop) in parts do
        Bap.Emu.write emu first (data.extract (first - address) (stop - address))
    finally
      for ends in ← emu.hostEnds.get do ends none

/-- `Emu.patch` in the process that runs or in the one given: the replacement goes only where the bytes are what the patch expects,
whatever their protection, which stays as it was, and what came of it is said rather than thrown. A patch that waits waits in that
process. -/
def Machine.patch (machine : Machine) (patch : Emu.Patch) (pid : Option Nat := none) : IO Emu.Patch.Result :=
  machine.inProcess pid do
    let emu := machine.emu
    for starts in ← emu.hostStarts.get do starts s!"Machine.patch {patch.address} {patch.replacement.size}"
    try Bap.Emu.patch emu patch
    finally
      for ends in ← emu.hostEnds.get do ends none

/-- The most that one block can have: a mapping is held in memory of the host from the start. -/
def Machine.mallocLimit : Nat := 2 ^ 32

/-- The heap of the address space that runs, with what is no longer mapped gone from it. -/
private def Machine.currentHeap (machine : Machine) : IO (Nat × GuestHeap) := do
  let space := (← currentTask machine.emu).space
  let regions ← machine.emu.regions.get
  let heap := ((← machine.heaps.get).getD space {}).keepChunks fun chunk => coversRange regions chunk.1 (chunk.1 + chunk.2)
  pure (space, heap)

/-- How many bytes a block that `Machine.malloc` gave has, of the process that runs, if it gave it and hasn't had it back. -/
def Machine.allocationSize (machine : Machine) (address : Nat) : IO (Option Nat) := do
  pure ((← machine.currentHeap).2.sizeOf address)

/-- Memory of a guest that nothing else there has: of the process that runs or of the one given, at a multiple of 16, readable and
writable, and not cleared if it was used before. It has its own mappings, so that it is nothing that the program's `malloc` knows of,
and a `free` of that program doesn't take it. It stays through a checkpoint and a `fork`, and goes on `execve`. -/
def Machine.malloc (machine : Machine) (size : Nat) (pid : Option Nat := none) : IO Nat :=
  machine.inProcess pid do
    if size > Machine.mallocLimit then throw <| IO.userError s!"malloc of {size} bytes is more than a block can have"
    let (space, heap) ← machine.currentHeap
    let heap ← match heap.alloc size with
      | some _ => pure heap
      | none =>
        let mapping := GuestHeap.mappingFor size
        pure (heap.addChunk (← placeZeros machine.emu 0 false mapping 3) mapping)
    match heap.alloc size with
    | some (address, heap) =>
      machine.heaps.modify (·.insert space heap)
      pure address
    | none => throw <| IO.userError s!"malloc of {size} bytes found no room after mapping it"

/-- Gives back what `Machine.malloc` gave, of the process that runs or of the one given. Of 0 it does nothing, as `free` does. Anything
else is an error, such as what it didn't give or has had back, or what the program has unmapped since. -/
def Machine.free (machine : Machine) (address : Nat) (pid : Option Nat := none) : IO Unit := do
  if address == 0 then return
  machine.inProcess pid do
    let (space, heap) ← machine.currentHeap
    match heap.release address with
    | none => throw <| IO.userError s!"free of {address}, which malloc didn't give or has had back"
    | some (heap, empty) =>
      machine.heaps.modify (·.insert space heap)
      if let some (first, size) := empty then unmap machine.emu first size

/-- `count` blocks of `size`, as one, cleared: what `Machine.malloc` gives may have been used before. That they come to more than a block
can have is an error, however much that is in the words of a target. -/
def Machine.calloc (machine : Machine) (count size : Nat) (pid : Option Nat := none) : IO Nat := do
  let total := count * size
  if total > Machine.mallocLimit then throw <| IO.userError s!"calloc of {count} of {size} bytes is more than a block can have"
  machine.inProcess pid do
    let address ← machine.malloc total
    machine.write address (zeroBytes total)
    pure address

/-- Another size for a block, keeping what it has as far as both go: where it is if it can, and somewhere else if not. Of 0 it is
`Machine.malloc`. To 0 it keeps the least that a block can be and says where, as what a libc does with that is its own, and an address
always means that it worked. If it fails, the block is as it was. What is more than it had isn't cleared. -/
def Machine.realloc (machine : Machine) (address size : Nat) (pid : Option Nat := none) : IO Nat := do
  if address == 0 then return ← machine.malloc size pid
  machine.inProcess pid do
    if size > Machine.mallocLimit then throw <| IO.userError s!"realloc to {size} bytes is more than a block can have"
    let (space, heap) ← machine.currentHeap
    let some held := heap.sizeOf address
      | throw <| IO.userError s!"realloc of {address}, which malloc didn't give or has had back"
    if let some resized := heap.resize address size then
      machine.heaps.modify (·.insert space resized)
      return address
    let moved ← machine.malloc size
    try
      machine.write moved (← Bap.Emu.read machine.emu address held)
      for copied in ← machine.emu.memoryCopied.get do copied address moved held
    catch error =>
      machine.free moved
      throw error
    machine.free address
    pure moved

private def checkpointMagic : ByteArray := "BAPLINUX".toUTF8

/-- What the bytes after the magic mean. -/
def checkpointFormat : Nat := 23

/-- What this BAP does with a guest, which goes up when the same state could go on differently. A checkpoint is refused by a BAP
of another, as nothing else tells two builds apart: the sources that it was built from aren't known to it when it runs. -/
def bapRevision : String := s!"bap-2 lean-{Lean.versionString}"

/-- What a directory holds, as all of its files in the order of their paths under it, however the directory itself is written. -/
def directoryDigest (root : System.FilePath) : IO Nat := do
  if !(← root.pathExists) then return 0
  -- Without what ends it, as what is under it is written from that, and the names shouldn't say.
  let trimmed := (root.toString.dropEndWhile (· == System.FilePath.pathSeparator)).toString
  let root : System.FilePath := if trimmed.isEmpty then root else trimmed
  let prefixLength := root.toString.length + 1
  let files ← root.walkDir
  let mut named : List (String × System.FilePath) := []
  for file in files do
    unless ← file.isDir do
      named := ((file.toString.drop prefixLength).toString.replace "\\" "/", file) :: named
  let mut hash := Wire.digest ByteArray.empty
  for (name, file) in named.mergeSort (fun left right => left.1 ≤ right.1) do
    hash := Wire.digest (← IO.FS.readBinFile file) (Wire.digest name.toUTF8 hash)
  return hash.toNat

/-- The semantics that a machine lifts by. -/
def semanticsDigest : IO Nat := do
  directoryDigest (← Bap.Target.LLVMLift.semanticsRoot)

/-- What a checkpoint says that it belongs to. -/
structure Machine.Identity where
  format : Nat := checkpointFormat
  bap : String := bapRevision
  semantics : Nat
  target : Nat
  deriving DecidableEq, Repr

/-- Why a checkpoint of `saved` can't go on here, if it can't. -/
def Machine.Identity.conflict (saved here : Machine.Identity) (expectedTarget : Option Nat := none) : Option String :=
  if saved.format != here.format then
    some s!"a checkpoint of format {saved.format}, and this BAP reads {here.format}"
  else if saved.bap != here.bap then
    some s!"a checkpoint of {saved.bap}, and this is {here.bap}"
  else if saved.semantics != here.semantics then
    some "a checkpoint of other semantics than those here"
  else match expectedTarget with
    | some target => if target != saved.target then some "a checkpoint of another program than was asked for" else none
    | none => none

/-- What a checkpoint has of a model: its name, what its bytes mean and the bytes. -/
private def putModel (out : ByteArray) (model : String × Nat × ByteArray) : ByteArray :=
  Wire.putBytes (Wire.putNat (Wire.putText out model.1) model.2.1) model.2.2

private def getModel : Wire.Decoder (String × Nat × ByteArray) := fun data at_ => do
  let (id, at_) ← Wire.getText data at_
  let (version, at_) ← Wire.getNat data at_
  let (bytes, at_) ← Wire.getBytes data at_
  .ok ((id, version, bytes), at_)

/-- All that a machine is, as bytes: what it belongs to, its architecture, its kernel with the files in it, its emulator, what its
models hold and a digest of all that. What is compiled isn't in them, and is compiled again as it runs. All of it is of one moment,
as nothing runs while it is made, and if a part can't be saved there is no checkpoint. -/
def Machine.checkpoint (machine : Machine) : IO ByteArray := do
  let (number, bits, big, flags) := machine.architecture.elf
  -- First, as it refuses to save in the middle of an instruction, when the rest wouldn't be of one moment either.
  let emulator ← checkpointBytes machine.emu
  -- The clock has what ran since it last went on, which only the emulator counts, and a checkpoint has none of it.
  machine.advanceClock
  let out := Wire.putNat checkpointMagic checkpointFormat
  let out := Wire.putText out bapRevision
  let out := Wire.putNat out (← semanticsDigest)
  let out := Wire.putNat out machine.target
  let out := Wire.putNat (Wire.putNat (Wire.putNat (Wire.putNat out number) bits) (if big then 1 else 0)) flags
  let out := Wire.putFlag out machine.handled
  let out := Image.encode out (← machine.kernel.get).image
  let out := Wire.putBytes out emulator
  let models := (← machine.modelBytes).map fun (model, bytes) => (model.id, model.version, bytes)
  let out := Wire.putSorted putModel out models
  pure (out ++ Wire.fixedBytes (Wire.digest out))

/-- What a checkpoint says of itself, read without making a machine of it: what it belongs to, its architecture, whether it had a handler
of system calls, the models that it has the state of with their versions, and what each process had loaded, where and of which file. It
is for finding out early whether a checkpoint is one that can go on here, before anything is restored. -/
structure Machine.CheckpointInfo where
  identity : Machine.Identity
  architecture : Architecture
  handled : Bool
  models : List (String × Nat)
  /-- By address space, each library that was loaded, with where, the digest of its file and whether its initializers ran. -/
  libraries : List (Nat × LoadedLibrary)
  /-- The files of the kernel, by path: how big each is, and its digest. -/
  files : List (String × Nat × Nat)
  /-- The files that a generator makes, by path, with its name: one that isn't built in has to be given to go on. -/
  generated : List (String × String)
  /-- The tasks, and those that wait for a child, as the scheduler has them. -/
  tasks : List Bap.Tasks.Entry
  waiters : List Bap.Tasks.Waiter
  /-- Of each process, each signal that it handles or ignores, with its handler, 1 for ignored. -/
  signals : List (Nat × Nat × Nat)
  /-- How much memory is mapped, of all address spaces, and how much of that isn't zeros, by pieces of 4096 bytes: about what going on
  from it takes of the host, which restoring takes as long as the first. -/
  mapped : Nat
  resident : Nat
  /-- Each thread, by id, with where it goes on and what it waits for. -/
  threads : List Bap.Emu.ThreadSummary

/-- The parts of a checkpoint: what `CheckpointInfo` says, with the image of its kernel, its emulator and the bytes of its models. -/
private def readCheckpoint (data : ByteArray) : IO (Machine.CheckpointInfo × Image × ByteArray × List (String × Nat × ByteArray)) := do
  if data.extract 0 checkpointMagic.size != checkpointMagic || data.size < checkpointMagic.size + 8 then
    throw <| IO.userError "not a checkpoint of a Linux machine"
  let body := data.extract 0 (data.size - 8)
  if Wire.digest body != Wire.ofFixedBytes data (data.size - 8) then
    throw <| IO.userError "a checkpoint that is damaged, or of another format"
  let (format, at_) ← IO.ofExcept (Wire.getNat body checkpointMagic.size)
  let (bap, at_) ← IO.ofExcept (Wire.getText body at_)
  -- Of another format or BAP, the rest may not be what this reads.
  if format != checkpointFormat then
    throw <| IO.userError s!"a checkpoint of format {format}, and this BAP reads {checkpointFormat}"
  if bap != bapRevision then
    throw <| IO.userError s!"a checkpoint of {bap}, and this is {bapRevision}"
  let (semantics, at_) ← IO.ofExcept (Wire.getNat body at_)
  let (target, at_) ← IO.ofExcept (Wire.getNat body at_)
  let (number, at_) ← IO.ofExcept (Wire.getNat body at_)
  let (bits, at_) ← IO.ofExcept (Wire.getNat body at_)
  let (big, at_) ← IO.ofExcept (Wire.getNat body at_)
  let (flags, at_) ← IO.ofExcept (Wire.getNat body at_)
  let some architecture := Architecture.ofElf number bits (big == 1) flags
    | throw <| IO.userError s!"a checkpoint of ELF machine {number}, which isn't one here"
  let (handled, at_) ← IO.ofExcept (Wire.getFlag body at_)
  let (image, at_) ← IO.ofExcept (Image.decode body at_)
  let (emulator, at_) ← IO.ofExcept (Wire.getBytes body at_)
  let (savedModels, at_) ← IO.ofExcept (Wire.getList getModel body at_)
  IO.ofExcept (Wire.expectEnd body at_)
  let libraries ← match savedModels.find? (·.1 == libraryModelId) with
    | some (_, _, bytes) =>
      let table ← IO.ofExcept (LoadedLibrary.decode bytes)
      let spaces := (table.toList.map (·.1)).toArray.qsort (· < ·) |>.toList
      pure (spaces.flatMap fun space => (table.getD space []).map (space, ·))
    | none => pure []
  let signals ← match savedModels.find? (·.1 == Signals.modelId) with
    | some (_, _, bytes) =>
      let table ← IO.ofExcept (Encoding.decode bytes)
      pure ((table.actions.toList.map fun ((group, signal), action) => (group, signal, action.handler)).toArray.qsort
        (fun left right => left.1 < right.1 || (left.1 == right.1 && left.2.1 < right.2.1))).toList
    | none => pure []
  let kinds : Std.HashMap Nat InodeImage := image.inodes.foldl (init := {}) fun table inode => table.insert inode.number inode
  let files := image.paths.filterMap fun (path, number) => match kinds.get? number with
    | some inode => if inode.kind == 0 then some (path, inode.data.size, (Wire.digest inode.data).toNat) else none
    | none => none
  let generated := image.paths.filterMap fun (path, number) => match kinds.get? number with
    | some inode => if inode.kind == 4 then (String.fromUTF8? inode.data).map (path, ·) else none
    | none => none
  let snapshot ← IO.ofExcept (snapshotOfFrame emulator)
  let spaces := snapshot.regions :: snapshot.processMemory.map (·.2)
  let mapped := spaces.foldl (fun total regions => regions.foldl (fun total region => total + region.data.size) total) 0
  let resident := spaces.foldl (fun total regions => regions.foldl (fun total region => total + Bap.Jit.resident region.data) total) 0
  let info : Machine.CheckpointInfo := {
    identity := { format, bap, semantics, target }, architecture, handled
    models := savedModels.map fun (id, version, _) => (id, version), libraries, files, generated
    tasks := snapshot.table.tasks, waiters := snapshot.table.waiters, signals, mapped, resident
    threads := snapshot.threadSummaries }
  pure (info, image, emulator, savedModels)

/-- What a checkpoint says of itself, without restoring anything of it. -/
def Machine.checkpointInfo (data : ByteArray) : IO Machine.CheckpointInfo := do
  pure (← readCheckpoint data).1

/-- Says what can't be restored of the models of a checkpoint, as going on without one or with another isn't going on as it would have. -/
private def modelConflict (saved : List (String × Nat × ByteArray)) (models : List RuntimeModel) : Option String :=
  -- Those that every machine has are no one's to give, and are of the versions that it has.
  let builtin := saved.filterMap fun (id, version, _) => (builtinModels.lookup id).map (id, version, ·)
  match builtin.find? fun (_, version, current) => version != current with
  | some (id, version, current) => some s!"a checkpoint with version {version} of model {id}, and this is version {current}"
  | none =>
  let saved := saved.filter fun entry => !(builtinModels.lookup entry.1).isSome
  match saved.find? (fun entry => !(models.any (·.id == entry.1))) with
  | some entry => some s!"a checkpoint with the state of model {entry.1}, which wasn't given"
  | none =>
    match models.find? (fun model => !(saved.any (·.1 == model.id))) with
    | some model => some s!"model {model.id} was given, and the checkpoint has nothing of it"
    | none =>
      (saved.findSome? fun entry =>
        (models.find? (·.id == entry.1)).bind fun model =>
          if model.version == entry.2.1 then none
          else some s!"a checkpoint with version {entry.2.1} of model {entry.1}, and this is version {model.version}")

/-- A new machine where a checkpoint was, which goes on as that one would. This is all it takes: nothing has to be running, or
even to be on the host, but what the bytes hold. `watch` is as in `start`. So is `handler`, as neither is a thing that can be in a file. What `Kernel.addGenerated` put in has its functions given again, by the normal paths that they were put in at, as a function can't be
in a file: a file without its function gives `EIO` when it is opened. `models` are attached again and given what they held.

A checkpoint that it can't go on from as that one would is refused: a damaged one, or one of another format, BAP or semantics, with a
model or a handler that isn't given, or of a program other than `expectedTarget`, the `targetDigest` of what is expected, or without the libraries of `expectedLibraries`, by the digests of their files. -/
def Machine.ofCheckpoint (data : ByteArray) (watch : Option (Nat → List Nat → IO Unit) := none)
    (generators : List (String × Generator) := []) (handler : Option SyscallHandler := none)
    (models : List RuntimeModel := []) (expectedTarget : Option Nat := none) (expectedLibraries : List Nat := []) : IO Machine := do
  let (info, image, emulator, savedModels) ← readCheckpoint data
  let saved := info.identity
  let here : Machine.Identity := { semantics := ← semanticsDigest, target := saved.target }
  if let some conflict := saved.conflict here expectedTarget then
    throw <| IO.userError conflict
  let architecture := info.architecture
  let target := saved.target
  if info.handled && handler.isNone then
    throw <| IO.userError "a checkpoint of a machine with a handler of system calls, which wasn't given"
  if let some conflict := modelConflict savedModels models then
    throw <| IO.userError conflict
  -- What it had loaded, in any process, by what the files were, before anything is made of it.
  let loaded := info.libraries.map (·.2.digest)
  let missing := expectedLibraries.filter (!loaded.contains ·)
  unless missing.isEmpty do
    throw <| IO.userError s!"a checkpoint without libraries of these digests, which were expected: {missing}"
  let kernel ← IO.ofExcept image.kernel
  let kernel := { kernel with generators := generators.foldl (fun table entry => table.insert entry.1 entry.2) {} }
  let emu ← emulatorOf architecture
  Bap.Emu.restore emu (← snapshotOfBytes emu emulator)
  let machine ← machineOf architecture emu kernel watch handler target models
  -- After what is attached, so that its hooks have the numbers that they had.
  setRunState emu (← runStateOfBytes emulator)
  for model in ← machine.models.get do
    if let some (_, _, bytes) := savedModels.find? (·.1 == model.id) then model.state.load bytes
  for heard in ← machine.restored.get do heard s!"checkpoint {Wire.ofFixedBytes data (data.size - 8)}"
  pure machine

/-- What would keep a checkpoint from going on here with these, without restoring anything: a model of another version or that isn't
given, a handler of system calls that isn't, a generated file whose generator isn't given or built in, a library of an expected digest
that isn't loaded, or another program than expected. Nothing is what `ofCheckpoint` would go on with. -/
def Machine.checkCheckpoint (data : ByteArray) (generators : List String := []) (handled : Bool := false)
    (models : List RuntimeModel := []) (expectedTarget : Option Nat := none) (expectedLibraries : List Nat := []) : IO (List String) := do
  let (info, _, _, savedModels) ← readCheckpoint data
  let here : Machine.Identity := { semantics := ← semanticsDigest, target := info.identity.target }
  let mut problems : List String := []
  if let some conflict := info.identity.conflict here expectedTarget then problems := problems ++ [conflict]
  if info.handled && !handled then problems := problems ++ ["a checkpoint of a machine with a handler of system calls, which isn't given"]
  if let some conflict := modelConflict savedModels models then problems := problems ++ [conflict]
  for (path, name) in info.generated do
    if !generators.contains path && (Proc.builtin name).isNone then
      problems := problems ++ [s!"{path} is made by {name}, which isn't given"]
  let loaded := info.libraries.map (·.2.digest)
  for digest in expectedLibraries do
    if !loaded.contains digest then problems := problems ++ [s!"no library of digest {digest} is loaded"]
  pure problems

/-- `ptrace` of the machine, for a hook or a handler that serves the system call of the thread that runs: what it gives is what that
gives back. It serves what the machine's own hook would, with the tracees and stops that the machine has. -/
def Machine.servePtrace (machine : Machine) (request pid address data : Nat) : IO SyscallAction :=
  machine.ptrace.servePtrace machine.emu request pid address data

/-- `wait4` of the machine, for what serves the system call of the thread that runs, as `Machine.servePtrace` is: a wait that has to
wait stops the thread, and is given its result when it goes on. -/
def Machine.serveWait (machine : Machine) (target status options usage : Nat) : IO SyscallAction :=
  machine.ptrace.serveWait machine.emu target status options usage

/-- What a wait says of the process that it reports, from its id here, which is the same until this is given: for a host that gives
the guest ids of its own. A wait that is answered at once and one that waited both say it, in what they return and in `si_pid`. It
isn't in a checkpoint: a machine that goes on from one is given it again. -/
def Machine.setWaitResultMapping (machine : Machine) (mapping : Nat → Nat) : IO Unit :=
  machine.ptrace.resultOf.set mapping

/-- The process tracing a thread, if one traces it with `ptrace`. -/
def Machine.tracerOf (machine : Machine) (tid : Nat) : IO (Option Nat) :=
  machine.ptrace.tracerOf tid

/-- What ended a process by a signal, or would have, as it happened: faults that nothing handled, handlers that couldn't be entered and
`sigreturn`s with nothing to go back to, apart. -/
def Machine.signalFailures (machine : Machine) : IO (List SignalFailure) := do
  pure (← machine.signals.failures.get).toList

/-- Whether a fault that a process ignores goes on past the instruction that faulted, rather than ending it as Linux does. -/
def Machine.setSkipIgnoredFaults (machine : Machine) (skip : Bool) : IO Unit :=
  machine.signals.skipIgnoredFaults.set skip

def Machine.saveFile (machine : Machine) (path : System.FilePath) : IO Unit := do
  writeAtomically path (← machine.checkpoint)

def Machine.loadFile (path : System.FilePath) (watch : Option (Nat → List Nat → IO Unit) := none)
    (generators : List (String × Generator) := []) (handler : Option SyscallHandler := none)
    (models : List RuntimeModel := []) (expectedTarget : Option Nat := none) (expectedLibraries : List Nat := []) : IO Machine := do
  Machine.ofCheckpoint (← IO.FS.readBinFile path) watch generators handler models expectedTarget expectedLibraries

/-- Changes the kernel of a machine, which may run, or says why it can't, as an error number of Linux. -/
private def Machine.changeKernel (machine : Machine) (what : String) (change : Kernel → Result Kernel) : IO Unit := do
  match change (← machine.kernel.get) with
  | .ok kernel => machine.kernel.set kernel
  | .error errno => throw <| IO.userError s!"{what}: error {errno} of Linux"

/-- Puts a file in the kernel of a machine, which may run, with the directories it needs: see `Kernel.putFile`. -/
def Machine.addFile (machine : Machine) (path : String) (data : ByteArray) (mode : Nat := 0o100644) : IO Unit :=
  machine.changeKernel s!"a file can't be put at {path}" (·.putFile path data mode)

/-- Makes a directory in the kernel of a machine, which may run, with the directories before it: see `Kernel.putDirectory`. -/
def Machine.addDirectory (machine : Machine) (path : String) (mode : Nat := 0o40755) : IO Unit :=
  machine.changeKernel s!"a directory can't be made at {path}" (·.putDirectory path mode)

/-- A directory of the host, which the machine sees at `guest` of its tree, which may be `/`: what a program looks for there comes in
from the host when it looks, once, and what it changes stays in the tree, as nothing of the host is written. Unlike the rest of a
run, what it finds is what the host has when it looks. A checkpoint has what came in, and a machine that goes on from one is given the
directory again. -/
def Machine.mountHost (machine : Machine) (host guest : String) : IO Unit := do
  let guest := Path.ofParts (Path.parts "/" guest)
  let host := (← IO.FS.realPath host).toString
  machine.hostMounts.modify (· ++ [(host, guest)])
  machine.kernel.modify (·.addDirectories guest)

/-- A file of the host for a kernel, before a run, other than what `Machine.mountHost` brings in when a program looks for it. -/
def Kernel.copyFromHost (kernel : Kernel) (path : String) (into : String := path) : IO Kernel := do
  let rec walk : Nat → Kernel → System.FilePath → String → IO Kernel
    | 0, kernel, _, _ => pure kernel
    | fuel + 1, kernel, source, target => do
      let info ← source.symlinkMetadata
      match info.type with
      | .symlink =>
        -- Lean can't read a link: it comes in as the file it points to, if that is one.
        match ← (do IO.FS.readBinFile (← IO.FS.realPath source)).toBaseIO with
        | .ok data => pure (kernel.addFile target data)
        | .error _ => pure kernel
      | .dir =>
        let mut kernel := kernel.addDirectories target
        for entry in ← source.readDir do
          kernel ← walk fuel kernel entry.path (target ++ "/" ++ entry.fileName)
        pure kernel
      -- What can't be read isn't there, as it would be for a program without the right to.
      | .file =>
        match ← (IO.FS.readBinFile source).toBaseIO with
        | .ok data => pure (kernel.addFile target data)
        | .error _ => pure kernel
      | _ => pure kernel
  walk 16 kernel path into

/-- A file or a directory of the host, with all that is in it, for the kernel of a machine, which may run: see `Kernel.copyFromHost`. -/
def Machine.copyFromHost (machine : Machine) (path : String) (into : String := path) : IO Unit := do
  machine.kernel.set (← (← machine.kernel.get).copyFromHost path into)

/-- What a dynamic program needs, for a kernel, before a run: the program, its interpreter and each library that it needs, from
the directories that libraries are in, with the links of their paths resolved to files. `root` is where the libraries of its
architecture are, which is the root of the host only if it is of the same one. They get the paths that they have under it. -/
def Kernel.copyProgramFromHost (kernel : Kernel) (path : String) (root : String := "") : IO Kernel := do
  let directories := ["/lib64", "/usr/lib64", "/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu", "/lib/aarch64-linux-gnu",
    "/usr/lib/aarch64-linux-gnu", "/lib/riscv64-linux-gnu", "/usr/lib/riscv64-linux-gnu", "/lib64/lp64d", "/usr/lib64/lp64d", "/lib/i386-linux-gnu", "/usr/lib/i386-linux-gnu", "/lib", "/usr/lib"]
  let copy (kernel : Kernel) (target : String) : IO (Kernel × ByteArray) := do
    let data ← IO.FS.readBinFile (root ++ target)
    pure (kernel.addFile target data, data)
  let data ← IO.FS.readBinFile path
  let kernel := kernel.addFile path data
  let mut kernel := kernel
  let mut pending := Elf.needed data
  let mut seen : List String := []
  match Elf.parse data with
  | .ok { interpreter := some name, .. } =>
    let (next, bytes) ← copy kernel name
    kernel := next
    pending := pending ++ Elf.needed bytes
  | _ => pure ()
  for _ in List.range 256 do
    match pending with
    | [] => break
    | name :: rest =>
      pending := rest
      if !seen.contains name then
        seen := name :: seen
        let found ← directories.findM? fun directory => System.FilePath.pathExists (root ++ directory ++ "/" ++ name)
        if let some directory := found then
          let (next, bytes) ← copy kernel (directory ++ "/" ++ name)
          kernel := next
          pending := pending ++ Elf.needed bytes
  pure kernel

end Bap.Linux
