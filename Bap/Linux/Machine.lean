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

/-- A model that a machine has, with what it holds. -/
structure AttachedModel where
  id : String
  version : Nat
  state : ModelState

/-- What is in the kernel, in the emulator and in the models at once. -/
structure Machine.Kept where
  emulator : Snapshot
  run : RunState
  kernel : Kernel
  models : List (String × ByteArray)

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
  /-- The directories of the host that it sees, each as the path of the host and that of the tree, and the paths under those that it
  has looked for there, which it doesn't again, with a directory whose entries it took ending in `/`: see `Machine.mountHost`. -/
  hostMounts : IO.Ref (List (String × String))
  hostSeen : IO.Ref (Std.HashSet String)
  /-- What AIO and io_uring have: see `Bap.Linux.Ring`. -/
  rings : IO.Ref Ring.State
  /-- How many calls that may let go of something there were since what nothing holds was let go of: see `Kernel.collect`. -/
  releases : IO.Ref Nat
  /-- What `Machine.malloc` has given out, by address space. -/
  heaps : IO.Ref (Std.HashMap Nat GuestHeap)
  /-- What `Machine.loadLibrary` has loaded, by address space. -/
  libraries : IO.Ref (Std.HashMap Nat (List LoadedLibrary))
  /-- What it goes back with, if it is kept. -/
  history : IO.Ref (Option Machine.History)
  /-- What hears that the machine was put back to what it was, by `restore`, `stepBack` or a checkpoint, with what put it back. -/
  restored : IO.Ref (List (String → IO Unit))
  /-- The directory that was last read, for the next piece of it: all the paths that it is of, which it is good for as long as those are the same object, its inode and what it has. -/
  listing : IO.Ref (Option (Std.HashMap String Nat × Nat × Array (Nat × Nat × String)))
  /-- The hook that serves each stub of a host function, by its address, so that a handler given again takes the place of the one
  before. -/
  hostHooks : IO.Ref (Std.HashMap Nat HookId)
  /-- Of each library that an import of was redirected, by where it is and its path: the slots of each name that it imports, as where
  each is from its base and what is added to what goes there, which reading its file once says. -/
  importSlots : IO.Ref (Std.HashMap (Nat × String) (Std.HashMap String (List (Nat × Nat))))

/-- A model of a runtime that isn't in the kernel or the emulator: pthreads served by hooks, a debugger, a managed language.
`id` is what a checkpoint knows it by, so that it stays the same, and `version` says what its bytes mean.

`attach` runs when a machine starts and again when one goes on from a checkpoint, as what it registers are functions, which can't be
in a file. It puts its hooks on `machine.emu`, in front of the kernel, and gives what holds its state. It should do nothing else to
the guest, whose memory is already what the checkpoint says when it runs again. -/
structure RuntimeModel where
  id : String
  version : Nat := 1
  attach : Machine → IO ModelState

/-- Attaches a model, as `start` and `Machine.ofCheckpoint` do those that they are given, or to a machine that runs already: what it
holds is in a checkpoint from then on, which then needs the model to go on from. Its id can't be one that the machine has. -/
def Machine.attachModel (machine : Machine) (model : RuntimeModel) : IO ModelState := do
  if (← machine.models.get).any (·.id == model.id) then
    throw <| IO.userError s!"two models of a runtime are called {model.id}"
  let state ← model.attach machine
  machine.models.modify (· ++ [{ id := model.id, version := model.version, state }])
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

/-- Bytes of a guest up to a zero, in as many pages as it takes. -/
private def readString (emu : Emu) (address : Nat) : IO String := do
  let rec go : Nat → Nat → ByteArray → IO ByteArray
    | 0, _, out => pure out
    | fuel + 1, from_, out => do
      let bytes ← read emu from_ (pageUp (from_ + 1) - from_)
      match bytes.data.findIdx? (· == 0) with
      | some index => pure (out ++ bytes.extract 0 index)
      | none => go fuel (from_ + bytes.size) (out ++ bytes)
  pure (textOf (← go 16 address ByteArray.empty))

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

/-- A successful result, with the bytes it leaves at an address the guest gave, if it gave one. -/
private def returning (emu : Emu) (address : Nat) (data : ByteArray) (value : Nat := 0) : IO SyscallAction := do
  try
    if address != 0 then writeGuest emu address data
    pure (.returnValue value)
  catch _ => pure (.returnValue (2 ^ 64 - Errno.efault))

private def errorOf (errno : Nat) : SyscallAction := .returnValue (2 ^ 64 - errno)

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

/-- The task that runs, if it is still in the table. -/
private def runningGroup (emu : Emu) : IO (Option Nat) := do
  pure (((← emu.taskTable.get).find? (← thread emu)).map (·.group))

/-- A mapping has what the file has, in the pages where it has something else. -/
private def refreshMapping (emu : Emu) (kernel : Kernel) (mapping : FileMapping) : IO Unit := do
  let wanted := kernel.inodeBytes mapping.inode mapping.offset mapping.size
  let memory ← peek emu mapping.start mapping.size
  if wanted != memory then
    for index in List.range ((mapping.size + 4095) / 4096) do
      let first := index * 4096
      let page := wanted.extract first (first + 4096)
      if page != memory.extract first (first + 4096) then
        poke emu (mapping.start + first) page (known := true)

/-- What a process wrote to its shared mappings goes to their files, which is how any other mapping or a `read` sees it. A running
process is the only one that can have written since it came to run, and whatever else it has mapped of a file is as the file was, so
that what differs from the file is what it wrote: it happens before any system call and when another process is to run. -/
private def flushShared (machine : Machine) (emu : Emu) : IO Unit := do
  let some group ← runningGroup emu | return
  let start ← machine.kernel.get
  let shared := (start.process group).mappings.filter (·.shared)
  if shared.isEmpty then return
  let mut changed := false
  for mapping in shared do
    if mapping.mayWrite then
      let size := start.inodeExtent mapping.inode mapping.offset mapping.size
      if size > 0 then
        let memory ← peek emu mapping.start size
        let before := start.inodeBytes mapping.inode mapping.offset size
        if memory != before then
          machine.kernel.modify (·.writeChanges mapping.inode mapping.offset before memory)
          changed := true
  -- Another mapping of the same file sees it.
  if changed then
    let flushed ← machine.kernel.get
    for mapping in shared do refreshMapping emu flushed mapping

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
    if mapping.shared &&
        kernel.inodeBytes mapping.inode mapping.offset mapping.size != before.inodeBytes mapping.inode mapping.offset mapping.size then
      refreshMapping emu kernel mapping

/-- Where a thread that waits on a pipe waits, which is no address space, of which there are as many as tasks. -/
private def pipeSpace : Nat := 2 ^ 61

/-- Everyone that waits on a pipe tries again, as something has changed, whichever it was. -/
private def wakePipeReaders (emu : Emu) : IO Unit := do
  let table ← emu.taskTable.get
  let waiting := (table.futexes.filter (·.space ≥ pipeSpace)).map (·.space) |>.eraseDups
  for space in waiting do
    let (table, woken) := (← emu.taskTable.get).futexWake space 0 (2 ^ 32 - 1) (2 ^ 32)
    emu.taskTable.set table
    for thread in woken do wakeThread emu thread

/-- `mmap`: of a file, here, of which a shared one writes back. What is anonymous is for `serveTaskCalls`. -/
private def serveFileMap (machine : Machine) (group address size bits flags fd offset : Nat) : IO SyscallAction := do
  let emu := machine.emu
  let fixed := flags &&& 0x10 != 0
  if size == 0 || offset % 4096 != 0 || flags &&& 3 == 0 || (fixed && address % 4096 != 0) then
    return errorOf Errno.einval
  let kernel ← machine.kernel.get
  match kernel.mappingSource group fd with
  | .error errno => pure (errorOf errno)
  | .ok (inode, canRead, canWrite) =>
    let shared := mapsShared flags
    if !canRead || (shared && bits &&& 2 != 0 && !canWrite) then
      return errorOf Errno.eacces
    -- `F_SEAL_WRITE` and `F_SEAL_FUTURE_WRITE`.
    if shared && bits &&& 2 != 0 && (kernel.inodes.get? inode).any (·.details.seals &&& 0x18 != 0) then
      return errorOf Errno.eperm
    match kernel.mappedBytes group fd offset (pageUp size) with
    | .error errno => pure (errorOf errno)
    | .ok data =>
      try
        let start ← placeMapping emu address fixed data bits
        machine.kernel.modify fun kernel =>
          (kernel.dropMappings group start (start + data.size)).addMapping group
            { start, size := data.size, inode, offset, shared, mayWrite := canWrite }
        pure (.returnValue start)
      catch _ => pure (errorOf Errno.enomem)

/-- `mmap` of memory that a child goes on sharing, which is a file that nothing else can open. -/
private def serveSharedMemory (machine : Machine) (group address size bits flags : Nat) : IO SyscallAction := do
  let fixed := flags &&& 0x10 != 0
  if size == 0 || (fixed && address % 4096 != 0) then
    return errorOf Errno.einval
  let pages := pageUp size
  try
    let start ← placeZeros machine.emu address fixed pages bits
    machine.kernel.modify fun kernel =>
      let (kernel, inode) := kernel.anonymousInode (Jit.zeros pages)
      (kernel.dropMappings group start (start + pages)).addMapping group
        { start, size := pages, inode, offset := 0, shared := true, mayWrite := true }
    pure (.returnValue start)
  catch _ => pure (errorOf Errno.enomem)

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
  clearMapped emu address pages
  for mapping in mappings do
    let first := max mapping.start address
    let stop := min (mapping.start + mapping.size) (address + pages)
    poke emu first (kernel.inodeBytes mapping.inode (mapping.offset + (first - mapping.start)) (stop - first)) (known := mapping.shared)
  pure (.returnValue 0)

/-- `mremap`, of one mapping as Linux has it: what is the same protection in one piece, and the same file throughout or none. It shrinks
in place, grows in place if nothing is in the way, and otherwise moves if it may, which takes a second mapping of a shared one if the old size is 0. -/
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
        let start ← placeMapping emu target fixed (kernel.inodeBytes mapping.inode offset newPages) (protectionBits region.protection)
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
  let behind := mappings.filter (·.overlaps old (old + oldPages))
  let mapping ← match behind with
    | [] => pure none
    | [mapping] =>
      if mapping.start ≤ old && old + oldPages ≤ mapping.start + mapping.size then pure (some mapping)
      else return errorOf Errno.efault
    | _ => return errorOf Errno.efault
  if keep && mapping.isSome then return errorOf Errno.einval
  let offset := match mapping with
    | some mapping => mapping.offset + (old - mapping.start)
    | none => 0
  let tail : ByteArray := if newPages ≤ oldPages then ByteArray.empty else
    match mapping with
    | some mapping => kernel.inodeBytes mapping.inode (offset + oldPages) (newPages - oldPages)
    | none => Jit.zeros (newPages - oldPages)
  let note (start : Nat) : IO Unit :=
    machine.kernel.modify fun kernel =>
      let kernel := (kernel.dropMappings group old (old + oldPages)).dropMappings group start (start + newPages)
      match mapping with
      | some mapping => kernel.addMapping group (placed start mapping offset)
      | none => kernel
  let free := !regions.any fun region => region.address < old + newPages && old + oldPages < region.address + region.data.size
  try
    if !fixed && !keep && free then
      map emu ⟨old + oldPages, tail, first.protection⟩
      note old
      return .returnValue old
    if !mayMove then return errorOf Errno.enomem
    let data := (← peek emu old (min oldPages newPages)) ++ tail
    let start ← placeMapping emu target fixed data (protectionBits first.protection)
    if keep then clearMapped emu old oldPages else unmap emu old oldPages
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

/-- The processes that are running. -/
private def liveProcesses (emu : Emu) : IO (List Nat) := do
  pure (((← emu.taskTable.get).tasks.filter fun task => task.status.isNone && task.tid == task.group).map (·.tid))

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
  let bootClock := (1700000000 : Nat) * 1000000000
  pure {
    pid := group
    parent := match table.find? group with
      | some task => task.parent
      | none => 0
    threads := (table.tasks.filter fun task => task.group == group && task.status.isNone).map (·.tid)
    command := process.command
    environment := process.environment
    program := process.program
    auxiliary := process.auxiliary
    big := architecture.big
    cwd := kernel.shownPath group process.cwd
    mounts := kernel.mounts.map fun mount => (kernel.shownPath group mount.target, mount.fstype, mount.device, mount.flags)
    ranges := regions.map fun region =>
      { start := region.address, size := region.data.size, readable := region.protection.readable
        writable := region.protection.writable, executable := region.protection.executable }
    breakStart := process.breakStart
    umask := process.umask
    breakEnd := process.breakEnd
    stackStart
    credentials := process.credentials
    pgid := kernel.pgidOf group
    sid := kernel.sidOf group
    stack := kernel.limitOf group 3
    files := kernel.limitOf group 7
    descriptors := process.descriptors.toList.filterMap fun (fd, entry) =>
      (kernel.openFiles.get? entry.openFile).map fun file => (fd, file.offset, file.flags)
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
registers as they were, as a read of a pipe does, or, of a signal, as `Timers.interrupted` says. -/
private def waitOn (machine : Machine) (emu : Emu) (number : Nat) : IO SyscallAction :=
  machine.timers.waitUntil emu (pipeSpace + number) 0 none true

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
  let cwd := (kernel.process group).cwd
  -- MIPS has the numbers of streams and datagrams the other way round, and `SOL_SOCKET` and the options elsewhere.
  let typeOf (type : Nat) : Nat := if mips && (type == 1 || type == 2) then 3 - type else type
  let solSocket := if mips then 0xffff else 1
  let option (generic mipsValue : Nat) : Nat := if mips then mipsValue else generic
  let peerCred := match architecture with
    | .mips .. => 18
    | .powerpc .. => 21
    | _ => 17
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
      | .error errno => pure (errorOf errno)
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
    match kernel.receive group fd total (flags &&& 2 != 0) alive with
    | .error errno => pure (errorOf errno)
    | .ok (_, none) =>
      if flags &&& 0x40 != 0 || kernel.nonblocking group fd then pure (errorOf Errno.eagain)
      else
        match kernel.socketOf group fd with
        | .ok (number, _) => waitOn machine emu number
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
    match ← socketName emu big (arg 1) (arg 2) with
    | .error errno => pure (errorOf errno)
    | .ok name =>
      match Kernel.Endpoint.ofName? name with
      | some endpoint => apply machine (·.bindInet group (arg 0) endpoint alive)
      | none => if family != 1 then pure (errorOf Errno.eafnosupport) else apply machine (·.bind group (arg 0) cwd name alive)
  | .listen => if family == 1 then apply machine (·.listen group (arg 0)) else apply machine (·.listenInet group (arg 0) alive)
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
            | .ok to => apply machine (·.connect group (arg 0) to alive)
      wakePipeReaders emu
      pure action
  | .accept | .accept4 =>
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
        let room := word header (5 * wordSize)
        let headerSize := wordSize + 8
        let fit := if control == 0 || room < headerSize then 0 else min received.rights.length ((room - headerSize) / 4)
        if fit < received.rights.length then flags := flags ||| 8
        let (next, fds) := (← machine.kernel.get).receiveRights group (received.rights.take fit) (arg 2 &&& 0x40000000 != 0)
        machine.kernel.set next
        let used := if fit == 0 then 0 else (headerSize + 4 * fit + wordSize - 1) / wordSize * wordSize
        if fit > 0 then
          let message := Abi.field big wordSize (headerSize + 4 * fit) ++ Abi.field big 4 solSocket ++ Abi.field big 4 1 ++
            fds.foldl (fun out fd => out ++ Abi.field big 4 fd) ByteArray.empty
          writeGuest emu control message
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
    | .ok _ => pure (.returnValue 0)
  | .getsockopt =>
    match kernel.socketOf group (arg 0) with
    | .error errno => pure (errorOf errno)
    | .ok (_, socket) =>
      let name := arg 2
      let value : Option ByteArray :=
        -- What TCP and IP are asked of they have nothing to say of.
        if arg 1 == 6 || arg 1 == 0 || arg 1 == 41 then (if socket.family != 1 then some (Abi.field big 4 0) else none)
        else if arg 1 != solSocket then none
        else if name == option 3 0x1008 then some (Abi.field big 4 (typeOf socket.type))
        else if name == option 4 0x1007 then some (Abi.field big 4 0)
        else if name == option 7 0x1001 || name == option 8 0x1002 then some (Abi.field big 4 212992)
        else if name == option 30 0x1009 then some (Abi.field big 4 (if socket.listening then 1 else 0))
        else if name == option 38 0x1028 then
          some (Abi.field big 4 (if socket.family == 1 then 0 else if socket.type == 1 then 6 else 17))
        else if name == option 39 0x1029 then some (Abi.field big 4 socket.family)
        else if name == peerCred then
          -- `struct ucred` of the other end: its process, and root.
          let owner := (socket.peer.bind kernel.socketAt).map (·.owner)
          some (Abi.field big 4 (owner.getD 0) ++ Abi.field big 4 0 ++ Abi.field big 4 0)
        -- The others that it can be asked, such as `SO_REUSEADDR` and `SO_KEEPALIVE`, are off.
        else some (Abi.field big 4 0)
      match value with
      | none => pure (errorOf Errno.enoprotoopt)
      | some bytes => if ← giveName emu big (arg 3) (arg 4) bytes then pure (.returnValue 0) else pure (errorOf Errno.efault)
  | _ => pure (errorOf Errno.enosys)

/-- The system calls of files, memory that files are mapped into, time and what a process asks of itself. -/
private partial def kernelCall (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO SyscallAction := do
    -- The ranges that these change may have a tag, as a program may give what it got from an allocator that tags them.
    let args := match call, args with
      | .munmap, address :: rest | .mprotect, address :: rest | .madvise, address :: rest => emu.config.untag address :: rest
      | _, _ => args
    let machine : Machine := { machine with emu }
    let architecture := machine.architecture
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
    let group := (← currentTask emu).group
    let kernel ← machine.kernel.get
    let cwd := (kernel.process group).cwd
    let poller : Poller := { architecture, kernel := machine.kernel, timers := machine.timers, signals := machine.signals
                             live := do pure (((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups)
                             wake := wakePipeReaders }
    -- `path` from an address, in the directory that the call says.
    let at_ (directory address : Nat) (action : String → String → IO SyscallAction) : IO SyscallAction := do
      match kernel.baseOf group directory (atCwd directory) with
      | .error errno => pure (errorOf errno)
      | .ok from_ =>
        match ← (readString emu address).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok path =>
          -- No name is none, rather than where the call is from; within the root of the process.
          if path.isEmpty then return errorOf Errno.enoent
          let (from_, path) := kernel.pathIn group from_ path
          action from_ path
    let here := 2 ^ 64 - 100
    let openAt (directory address flags mode : Nat) : IO SyscallAction :=
      at_ directory address fun from_ path => do
        let flags := architecture.openFlags flags
        if flags &&& 0x400000 != 0 then return ← applyNat machine (·.openTmpfile group from_ path flags mode)
        -- What makes a pseudo-terminal, and the controlling terminal.
        if let some action ← Tty.openDevice poller emu (Path.ofParts (Path.parts from_ path)) flags then return action
        let current ← machine.kernel.get
        match generatedAt current from_ path with
        | some (name, normal) =>
          if flags &&& 3 != 0 then pure (errorOf Errno.eacces)
          else
            match generatorOf current name with
            | none => pure (errorOf Errno.eio)
            | some generate =>
              let bytes := generate (← viewOf machine emu (processOfPath normal group))
              applyNat machine fun kernel => .ok (kernel.openBytes group bytes flags)
        | none =>
          let action ← applyNat machine (·.openPath group from_ path flags mode)
          -- A slave of a pseudo-terminal, which may be locked, or be what its process takes as its controlling terminal.
          match action with
          | .returnValue fd => if fd < 2 ^ 31 then pure ((← Tty.opened poller emu fd flags).getD action) else pure action
          | other => pure other
    let accessAt (directory address : Nat) : IO SyscallAction :=
      at_ directory address fun from_ path =>
        pure (match kernel.statPath from_ path with
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
        if current.pipeWaiting number > 0 || !current.pipeHeld number (← liveGroups) true then pure none
        else if current.nonblocking group fd then pure (some (errorOf (Errno.eagain)))
        else
          pure (some (← waitOn machine emu number))
    let readInto (fd address count : Nat) : IO SyscallAction := do
      let kernel ← machine.kernel.get
      match kernel.read group fd count with
      | .error errno => pure (errorOf errno)
      | .ok (next, bytes) =>
        machine.kernel.set next
        returning emu address bytes bytes.size
    let writeOut (fd address count : Nat) : IO SyscallAction := do
      let current ← machine.kernel.get
      let toPipe := current.pipeOf group fd
      if let some number := toPipe then
        if !current.pipeHeld number (← liveGroups) false then return errorOf Errno.epipe
      match ← (read emu address count).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok bytes =>
        let action ← applyNat machine (·.write group fd bytes)
        if toPipe.isSome then wakePipeReaders emu
        pure action
    let statAt (directory address out : Nat) (follow : Bool) : IO SyscallAction :=
      at_ directory address fun from_ path =>
        match kernel.statPath from_ path follow with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu out (architecture.stat value)
    let clock (out scale : Nat) : IO SyscallAction := do
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu out (Abi.time now scale big wordSize)
    -- Anonymous and private is for `serveTaskCalls`, once what it takes the place of isn't mapped.
    let rings : Ring.Rings := { poller, state := machine.rings, perform := kernelCall machine emu }
    let mapMemory (offset : Nat) : IO SyscallAction := do
      -- The rings of an io_uring.
      if arg 3 &&& architecture.mapAnonymous == 0 then
        if let some action ← Ring.map rings emu group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) offset then return action
      if arg 3 &&& architecture.mapAnonymous == 0 then
        serveFileMap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) offset
      else if mapsShared (arg 3) then
        serveSharedMemory machine group (arg 0) (arg 1) (arg 2) (arg 3)
      else
        if arg 3 &&& 0x10 != 0 then
          machine.kernel.modify (·.dropMappings group (arg 0) (arg 0 + pageUp (arg 1)))
        pure .default
    let vectors (fd address count : Nat) (action : Nat → Nat → Nat → IO SyscallAction) : IO SyscallAction := do
      let mut total := 0
      for index in List.range count do
        let entry ← read emu (address + 2 * wordSize * index) (2 * wordSize)
        let field (offset : Nat) : Nat :=
          (List.range wordSize).foldl (fun value at__ =>
            let byte := if big then wordSize - 1 - at__ else at__
            value + entry[offset + byte]!.toNat * 256 ^ at__) 0
        match ← action fd (field 0) (field wordSize) with
        | .returnValue value =>
          if value ≥ 2 ^ 63 then
            return if total > 0 then .returnValue total else .returnValue value
          total := total + value
          if value < field wordSize then return .returnValue total
        | other => return other
      pure (.returnValue total)
    -- A path in the directory of the second, from another call of `at_`.
    let inDirectory (directory address : Nat) (action : String → IO SyscallAction) : IO SyscallAction :=
      at_ directory address fun from_ path => action (if path.startsWith "/" then path else from_ ++ "/" ++ path)
    -- Of what `read` and `write` serve themselves: terminals, and the objects of `eventfd`, `timerfd`, `signalfd` and `inotify`.
    let isObject (fd : Nat) : Bool := match kernel.objectOf group fd with
      | .ok (_, _, { content := .eventfd .., .. }) | .ok (_, _, { content := .timerfd .., .. }) | .ok (_, _, { content := .signalfd _, .. })
      | .ok (_, _, { content := .ptyMaster _, .. }) | .ok (_, _, { content := .ptySlave _, .. }) | .ok (_, _, { content := .inotify .., .. }) => true
      | _ => false
    let number (address size : Nat) : IO Nat := do pure (numberAt (← read emu address size) 0 size big)
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
      match ← waitForPipe (arg 0) with
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
      pure action
    | .pipe | .pipe2 =>
      let flags := if call == .pipe2 then architecture.openFlags (arg 1) else 0
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
      -- AT_EMPTY_PATH says that the descriptor is what it is about.
      let path ← (readString emu (arg 1)).toBaseIO
      match path with
      | .ok "" =>
        if arg 3 &&& 0x1000 != 0 then
          match kernel.statDescriptor group (arg 0) with
          | .error errno => pure (errorOf errno)
          | .ok value => returning emu (arg 2) (architecture.stat value)
        else pure (errorOf Errno.enoent)
      | _ => statAt (arg 0) (arg 1) (arg 2) (arg 3 &&& 0x100 == 0)
    | .statfs | .statfs64 =>
      at_ here (arg 0) fun from_ path =>
        match kernel.statPath from_ path with
        | .error errno => pure (errorOf errno)
        | .ok _ =>
          let bytes := Abi.statfs (architecture.bits == 64) big mips
          if call == .statfs then returning emu (arg 1) bytes else returning emu (arg 2) (bytes.extract 0 (arg 1))
    | .fstatfs | .fstatfs64 =>
      match kernel.statDescriptor group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok _ =>
        let bytes := Abi.statfs (architecture.bits == 64) big mips
        if call == .fstatfs then returning emu (arg 1) bytes else returning emu (arg 2) (bytes.extract 0 (arg 1))
    | .execve => pure (errorOf Errno.enosys)
    | .sysinfo => returning emu (arg 0) (Abi.sysinfo (architecture.bits == 64) big (kernel.clock / 1000000000 - 1700000000) 1)
    | .statx =>
      let path ← (readString emu (arg 1)).toBaseIO
      let finish (result : Result Kernel.Stat) : IO SyscallAction :=
        match result with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu (arg 4) (Abi.statx value big)
      match path with
      | .ok "" =>
        if arg 2 &&& 0x1000 != 0 then finish (kernel.statDescriptor group (arg 0))
        else pure (errorOf Errno.enoent)
      | _ =>
        at_ (arg 0) (arg 1) fun from_ text => finish (kernel.statPath from_ text (arg 2 &&& 0x100 == 0))
    | .lseek =>
      let (negative, distance) := signed wide (arg 1)
      applyNat machine (·.seek group (arg 0) negative distance (arg 2))
    | .llseek =>
      let (negative, distance) := signed 64 (arg 1 * 2 ^ 32 + arg 2)
      match (← machine.kernel.get).seek group (arg 0) negative distance (arg 4) with
      | .error errno => pure (errorOf errno)
      | .ok (next, position) =>
        machine.kernel.set next
        returning emu (arg 3) (cell 8 position)
    | .pread =>
      match kernel.readFrom group (arg 0) (arg 2) (offset64 3) with
      | .error errno => pure (errorOf errno)
      | .ok bytes => returning emu (arg 1) bytes bytes.size
    | .pwrite =>
      match ← (read emu (arg 1) (arg 2)).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok bytes => applyNat machine (·.writeTo group (arg 0) bytes (offset64 3))
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
      else vectors (arg 0) (arg 1) (arg 2) writeOut
    | .access => accessAt here (arg 0)
    | .faccessat => accessAt (arg 0) (arg 1)
    | .dup => applyNat machine (·.dup group (arg 0))
    | .dup2 =>
      let action ← applyNat machine (·.dupTo group (arg 0) (arg 1))
      wakePipeReaders emu
      pure action
    | .dup3 =>
      if arg 0 == arg 1 then pure (errorOf Errno.einval)
      else applyNat machine (·.dupTo group (arg 0) (arg 1) (arg 2 &&& Kernel.oCloexec != 0))
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
      | none => pure (errorOf (match kernel.statDescriptor group (arg 0) with | .ok _ => Errno.enotty | .error errno => errno))
    | .getdents =>
      -- What a directory has takes going through all paths, and a program may read it a little at a time.
      let found : Result (Nat × Nat × List (Nat × Nat × String)) ← match kernel.openFileOf group (arg 0) with
        | .error errno => pure (.error errno)
        | .ok (id, file) =>
          let cached ← machine.listing.get
          match cached with
          | some (paths, number, all) =>
            if number == file.inode && sameObject paths kernel.paths then
              -- No entry is shorter than what its header takes.
              pure (.ok (id, file.offset, ((all.extract file.offset (file.offset + arg 2 / 24 + 1)).toList)))
            else
              pure (.error 0)
          | none => pure (.error 0)
      let found ← match found with
        | .error 0 =>
          match kernel.directoryListing group (arg 0), kernel.openFileOf group (arg 0) with
          | .ok all, .ok (id, file) =>
            machine.listing.set (some (kernel.paths, file.inode, all))
            pure (.ok (id, file.offset, ((all.extract file.offset (file.offset + arg 2 / 24 + 1)).toList)))
          | .error errno, _ | _, .error errno => pure (.error errno)
        | other => pure other
      match found with
      | .error errno => pure (errorOf errno)
      | .ok (id, first, entries) =>
        let (bytes, count) := Abi.dirents entries first (arg 2) big
        if count == 0 && !entries.isEmpty then
          pure (errorOf Errno.einval)
        else
          machine.kernel.set (kernel.advance id count)
          returning emu (arg 1) bytes bytes.size
    | .getcwd =>
      let text := (kernel.shownPath group cwd ++ "\x00").toUTF8
      if text.size > arg 1 then pure (errorOf Errno.erange)
      else returning emu (arg 0) text text.size
    | .chdir => at_ here (arg 0) fun _ path => apply machine (·.chdir group path)
    | .fchdir =>
      match kernel.directoryEntries group (arg 0), kernel.baseOf group (arg 0) false with
      | _, .ok path => apply machine (·.chdir group path)
      | .error errno, _ => pure (errorOf errno)
      | _, .error errno => pure (errorOf errno)
    | .mkdir => at_ here (arg 0) fun from_ path => apply machine (·.mkdir group from_ path (arg 1))
    | .mkdirat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.mkdir group from_ path (arg 2))
    | .rmdir => at_ here (arg 0) fun from_ path => apply machine (·.remove from_ path true)
    | .unlink => at_ here (arg 0) fun from_ path => apply machine (·.remove from_ path false)
    | .unlinkat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.remove from_ path (arg 2 &&& 0x200 != 0))
    | .rename =>
      inDirectory here (arg 0) fun source => inDirectory here (arg 1) fun target =>
        apply machine (·.rename "/" source target)
    | .renameat =>
      inDirectory (arg 0) (arg 1) fun source => inDirectory (arg 2) (arg 3) fun target =>
        apply machine (·.rename "/" source target)
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
        | .ok target => apply machine (·.symlink from_ target path)
    | .readlink | .readlinkat =>
      let (directory, address, out, room) := if call == .readlink then (here, arg 0, arg 1, arg 2) else (arg 0, arg 1, arg 2, arg 3)
      at_ directory address fun from_ path =>
        match kernel.readlink from_ path with
        | .error errno => pure (errorOf errno)
        | .ok target =>
          let bytes := target.toUTF8
          let bytes := bytes.extract 0 room
          returning emu out bytes bytes.size
    | .chmod => at_ here (arg 0) fun from_ path => apply machine (·.chmod from_ path (arg 1))
    | .fchmodat => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.chmod from_ path (arg 2))
    | .truncate => at_ here (arg 0) fun from_ path => apply machine (·.truncatePath from_ path (arg 1))
    | .ftruncate => apply machine (·.truncateDescriptor group (arg 0) (arg 1))
    | .truncate64 => at_ here (arg 0) fun from_ path => apply machine (·.truncatePath from_ path (pair (architecture.pairBase - 2)))
    | .ftruncate64 => apply machine (·.truncateDescriptor group (arg 0) (pair (architecture.pairBase - 2)))
    | .umask =>
      let process := kernel.process group
      machine.kernel.set (kernel.setProcess group { process with umask := arg 0 &&& 0o777 })
      pure (.returnValue process.umask)
    | .mmap => mapMemory (arg 5)
    | .mmap2 => mapMemory (arg 5 * 4096)
    | .munmap =>
      if arg 0 % 4096 != 0 || arg 1 == 0 then pure (errorOf Errno.einval)
      else
        machine.kernel.modify (·.dropMappings group (arg 0) (arg 0 + pageUp (arg 1)))
        pure .default
    | .mprotect =>
      let upper := arg 0 + pageUp (arg 1)
      if arg 2 &&& 2 != 0 && (kernel.process group).mappings.any (fun mapping => mapping.shared && !mapping.mayWrite && mapping.overlaps (arg 0) upper) then
        pure (errorOf Errno.eacces)
      else pure .default
    | .madvise =>
      -- The advice that there is, of a range that is mapped.
      let advice := arg 2
      if arg 0 % 4096 != 0 || !(advice ≤ 4 || (8 ≤ advice && advice ≤ 25) || advice == 100 || advice == 101) then
        pure (errorOf Errno.einval)
      else if !coversRange (← emu.regions.get) (arg 0) (arg 0 + pageUp (arg 1)) then pure (errorOf Errno.enomem)
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
    | .mremap => serveRemap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4)
    | .brk => serveBreak machine group (arg 0)
    | .gettimeofday => clock (arg 0) 1000
    | .time =>
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu (arg 0) (cell wordSize (now / 1000000000)) (now / 1000000000)
    | .clockGettime => clock (arg 1) 1
    | .clockGetres => returning emu (arg 1) (Abi.time 1 1 big wordSize)
    | .clockGettime64 =>
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu (arg 1) (Abi.time now 1 big 8)
    | .clockGetres64 => returning emu (arg 1) (Abi.time 1 1 big 8)
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
      -- A fixed sequence, as a run is the same each time.
      returning emu (arg 0) (Kernel.randomBytes 0 (arg 1)) (arg 1)
    | .sigaltstack => returning emu (arg 1) (ByteArray.mk (Array.replicate (3 * wordSize) 0))
    | .schedGetaffinity => returning emu (arg 2) (cell wordSize 1) wordSize
    | .succeeds => pure (.returnValue 0)
    -- Served by `Bap.Linux.Seccomp` before it comes here.
    | .seccomp => pure (errorOf Errno.enosys)
    | .nanosleep | .clockNanosleep | .clockNanosleep64 | .setitimer | .getitimer | .alarm | .timerCreate | .timerSettime
    | .timerSettime64 | .timerGettime | .timerGettime64 | .timerGetoverrun | .timerDelete =>
      pure ((← machine.timers.serve emu call args).getD (errorOf Errno.enosys))
    | .prctl =>
      -- What a program asks of tagged addresses, on AArch64: they are always taken here, where only a tag in the top byte is.
      if architecture == .aarch64 && arg 0 == 55 then
        pure (if arg 1 ≤ 1 && arg 2 == 0 && arg 3 == 0 && arg 4 == 0 then .returnValue 0 else errorOf Errno.einval)
      else if architecture == .aarch64 && arg 0 == 56 then
        pure (if arg 1 == 0 && arg 2 == 0 && arg 3 == 0 && arg 4 == 0 then .returnValue 1 else errorOf Errno.einval)
      else pure .default
    | .socket | .socketpair | .bind | .listen | .accept | .accept4 | .connect | .getsockname | .getpeername | .sendto | .recvfrom
    | .send | .recv | .setsockopt | .getsockopt | .shutdown | .sendmsg | .recvmsg => socketCall machine emu call args

/-- The argument of a call that is a path, if it has one, and whether it is relative to a descriptor. -/
private def pathArgument : Call → Option Nat
  | .open_ | .stat | .lstat | .access | .readlink | .chdir | .truncate | .truncate64 | .statfs | .statfs64 => some 0
  | .openat | .fstatat | .statx | .faccessat | .readlinkat => some 1
  | _ => none

/-- The paths that a call is given, by the index of each, and whether the argument before it is a directory that it is from. -/
private def pathArguments : Call → List (Nat × Bool)
  | .open_ | .stat | .lstat | .access | .readlink | .chdir | .truncate | .truncate64 | .statfs | .statfs64 | .execve | .mkdir | .rmdir
  | .unlink | .chmod | .chown | .lchown | .utimes | .utime | .setxattr | .lsetxattr | .getxattr | .lgetxattr | .listxattr
  | .llistxattr | .removexattr | .lremovexattr | .chroot | .umount2 => [(0, false)]
  | .openat | .fstatat | .statx | .faccessat | .readlinkat | .mkdirat | .unlinkat | .fchmodat | .fchownat | .utimensat
  | .utimensat64 | .futimesat => [(1, true)]
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
    if (← machine.hostSeen.get).contains guest || (← machine.kernel.get).paths.contains guest then return ← isDirectory
    machine.hostSeen.modify (·.insert guest)
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
  if (← machine.hostSeen.get).contains (guest ++ "/") then return
  machine.hostSeen.modify (·.insert (guest ++ "/"))
  if let .ok entries ← (System.FilePath.mk host).readDir.toBaseIO then
    for entry in entries do
      let _ ← bring (child guest entry.fileName) (child host entry.fileName)

/-- Makes `/proc` what it has to be for a call that may look at it, which only a path can tell. -/
private def refreshProc (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO Unit := do
  if let some index := pathArgument call then
    match ← (readString emu (args.getD index 0)).toBaseIO with
    | .error _ => pure ()
    | .ok path =>
      let group := (← currentTask emu).group
      let kernel ← machine.kernel.get
      let relative := !path.startsWith "/"
      -- What the second argument is relative to is the first, which may be in there.
      let base := if index == 1 && !atCwd (args.getD 0 0) then (kernel.baseOf group (args.getD 0 0) false).toOption.getD ""
        else (kernel.process group).cwd
      if path.startsWith "/proc" || (relative && base.startsWith "/proc") then
        let self ← thread emu
        let live ← liveProcesses emu
        let tasks := (← emu.taskTable.get).tasks.filter (·.status.isNone)
        machine.kernel.modify (Proc.refresh · group self live fun pid =>
          (tasks.filter (·.group == pid)).map (·.tid))

/-- `write`, on its own: nothing here holds on to the kernel, so that a program that writes a little at a time doesn't have what it wrote before copied each time. -/
private def writeDirect (machine : Machine) (emu : Emu) (group fd address count : Nat) : IO SyscallAction := do
  let current ← machine.kernel.get
  if let some errno := current.writeError group fd count then return errorOf errno
  let toPipe := current.pipeOf group fd
  if let some number := toPipe then
    let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
    if !current.pipeHeld number live false then return errorOf Errno.epipe
  match ← (read emu address count).toBaseIO with
  | .error _ => pure (errorOf Errno.efault)
  | .ok bytes =>
    machine.kernel.modify (·.writeKnown group fd bytes)
    if toPipe.isSome then wakePipeReaders emu
    pure (.returnValue bytes.size)

/-- `pwrite`, on its own, as `writeDirect` is. -/
private def writeDirectAt (machine : Machine) (emu : Emu) (group fd address count offset : Nat) : IO SyscallAction := do
  if let some errno := (← machine.kernel.get).writeAtError group fd count offset then return errorOf errno
  match ← (read emu address count).toBaseIO with
  | .error _ => pure (errorOf Errno.efault)
  | .ok bytes =>
    machine.kernel.modify (·.writeKnownAt group fd bytes offset)
    pure (.returnValue bytes.size)

/-- `writev`, by `writeDirect`. -/
private def writeVectorDirect (machine : Machine) (emu : Emu) (group fd address count : Nat) : IO SyscallAction := do
  let word := machine.architecture.bits / 8
  let big := machine.architecture.big
  let mut total := 0
  for index in List.range count do
    let entry ← read emu (address + 2 * word * index) (2 * word)
    let field (offset : Nat) : Nat :=
      (List.range word).foldl (fun value at_ =>
        let byte := if big then word - 1 - at_ else at_
        value + entry[offset + byte]!.toNat * 256 ^ at_) 0
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
descriptor first: `EMFILE`, and of `dup2` and `dup3` to one past it `EBADF`, and of `F_DUPFD` from one past it `EINVAL`. -/
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
    | .dup2 | .dup3 => if arg 1 % 2 ^ 32 < 2 ^ 31 && arg 1 % 2 ^ 32 ≥ limit then some (errorOf Errno.ebadf) else none
    | .fcntl =>
      if arg 1 != 0 && arg 1 != 1030 then none
      else if arg 2 % 2 ^ 32 ≥ limit then some (errorOf Errno.einval)
      else if free (arg 2 % 2 ^ 32) ≥ limit then some (errorOf Errno.emfile) else none
    | _ => none

private def serveKernelCalls (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu number args => do
    match machine.architecture.call number with
    -- What serveTaskCalls serves.
    | none => pure .default
    | some call =>
      machine.timers.entered emu
      let group := (← currentTask emu).group
      if let some refused ← descriptorLimit machine group call args then return ← handOver machine emu refused
      refreshProc machine emu call args
      -- What it names of the directories of the host that the machine sees.
      if !(← machine.hostMounts.get).isEmpty then
        let kernel ← machine.kernel.get
        let cwd := (kernel.process group).cwd
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
      let shared := ((← machine.kernel.get).process group).mappings.any (·.shared)
      -- A mapping of what is written has to hear of it. Otherwise a write is the only thing that a program does many of that gets longer with what it has done.
      let socket := (call == .write || call == .writev) && (← machine.kernel.get).isSocket group (args.getD 0 0)
      -- And what is written to an `eventfd` is counted, and to a terminal goes through it.
      let socket := socket || ((call == .write || call == .writev) && match (← machine.kernel.get).objectOf group (args.getD 0 0) with
        | .ok (_, _, { content := .eventfd .., .. }) | .ok (_, _, { content := .ptyMaster _, .. })
        | .ok (_, _, { content := .ptySlave _, .. }) => true
        | _ => false)
      -- And while `inotify` watches, what a write changes is found out from what it was before.
      let watching := !(← Notify.instancesOf machine.notifier (← machine.kernel.get)).isEmpty
      match call, shared || socket || watching with
      | .write, false => handOver machine emu (← writeDirect machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0))
      | .writev, false => handOver machine emu (← writeVectorDirect machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0))
      | .pwrite, false =>
        -- Its offset, which on 32 bits is in two arguments in the order of the guest.
        let architecture := machine.architecture
        let offset := if architecture.bits == 64 then args.getD 3 0 else
          let (low, high) := if architecture.big then (args.getD (architecture.pairBase + 1) 0, args.getD architecture.pairBase 0)
            else (args.getD architecture.pairBase 0, args.getD (architecture.pairBase + 1) 0)
          high * 2 ^ 32 + low
        handOver machine emu (← writeDirectAt machine emu group (args.getD 0 0) (args.getD 1 0) (args.getD 2 0) offset)
      | _, _ =>
        let before ← machine.kernel.get
        let action ← kernelCall machine emu call args
        -- A call that is over, rather than waiting to run again, has no site nor deadline left, which another at the same place,
        -- as `ipc` of i386 has all of its calls, would take as its own.
        if !(← Bap.Emu.stopped emu) then machine.timers.finish (← thread emu)
        refreshChanged machine emu before
        if [Call.close, .dup2, .dup3, .execve].contains call then released machine
        if watching then
          let live := ((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group) |>.eraseDups
          if ← Notify.after machine.notifier machine.kernel group call args before action live then wakePipeReaders emu
        handOver machine emu action

/-- What is left: nothing else serves it, and it isn't there. -/
private def serveRest (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu _ _ => handOver machine emu (errorOf Errno.enosys)

/-- A register of x86 of its width, from the name of its 16 bits. -/
private def wordOf (wide : Nat) (name : String) : Bap.Var :=
  ⟨(if wide == 64 then "R" else "E") ++ name, .imm wide, 0, false⟩

/-- An x86-64 of level 2, which is what the libc of current distributions asks for: SSE4.2 and POPCNT, without AVX, so that
libc doesn't pick the routines that need it. -/
private def serveCpu (emu : Emu) (kernel : IO.Ref Kernel) (wide : Nat) : IO Unit := do
  -- The registers, and how many of the vector ones there are.
  let a := wordOf wide "AX"
  let (b, c, d) := (wordOf wide "BX", wordOf wide "CX", wordOf wide "DX")
  let vectors := if wide == 64 then 16 else 8
  let _ ← onIntrinsic emu "cpuid" fun current _ => do
    let leaf := match Value.asBits (← reg current a) with
      | .ok value => value.2.toNat % 2 ^ 32
      | .error _ => 0
    let (eax, ebx, ecx, edx) : Nat × Nat × Nat × Nat := match leaf with
      -- AuthenticAMD: libc reads the caches of an Intel from leaves that this doesn't have.
      | 0 => (1, 0x68747541, 0x444d4163, 0x69746e65)
      -- SSE3, SSSE3, CMPXCHG16B, SSE4.1, SSE4.2, POPCNT
      | 1 => (0x800f00, 0, 0x00982201, 0x07888f9f)
      | 0x80000000 => (0x80000001, 0, 0, 0)
      -- LAHF, and SYSCALL, NX and long mode
      | 0x80000001 => (0, 0, 1, 0x20100800)
      | _ => (0, 0, 0, 0)
    -- In the registers: what follows the intrinsic in its code doesn't run after a hook has served it.
    for (var, value) in [(a, eax), (b, ebx), (c, ecx), (d, edx)] do
      setReg current var (bits wide value)
    pure .proceed
  -- What ld.so saves around resolving a function. The layout is that of the manual: the controls, MXCSR, ST and XMM. The rest of
  -- the x87 state, as what instruction faulted, isn't kept.
  let value (emu : Emu) (var : Bap.Var) : IO Nat := do
    match Value.asBits (← reg emu var) with
    | .ok bits => pure bits.2.toNat
    | .error _ => pure 0
  let target (emu : Emu) : IO Nat := value emu ⟨"intrinsic:x0", .imm wide, 0, false⟩
  let save (emu : Emu) : IO Unit := do
    let address ← target emu
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
      image := image ++ Abi.bytesOf 16 ((← value emu ⟨s!"ZMM{index}", .imm 512, 0, false⟩) % 2 ^ 128)
    writeGuest emu address (image ++ Abi.bytesOf (512 - image.size) 0)
  let load (emu : Emu) : IO Unit := do
    let address ← target emu
    let image ← read emu address 512
    let field (offset size : Nat) : Nat := (List.range size).foldl (fun out index => out + image[offset + index]!.toNat * 256 ^ index) 0
    setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 (field 0 2))
    setReg emu ⟨"FPU_STATUS", .imm 16, 0, false⟩ (bits 16 (field 2 2))
    let abridged := field 4 1
    setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 ((List.range 8).foldl (fun out index =>
      if (abridged >>> index) % 2 == 1 then out else out + 3 * 4 ^ index) 0))
    setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 (field 24 4))
    for index in List.range 8 do
      setReg emu ⟨s!"ST{index}", .imm 80, 0, false⟩ (bits 80 (field (32 + 16 * index) 10))
    for index in List.range vectors do
      let var : Bap.Var := ⟨s!"ZMM{index}", .imm 512, 0, false⟩
      let high := (← value emu var) / 2 ^ 128
      setReg emu var (bits 512 (high * 2 ^ 128 + field (160 + 16 * index) 16))
  for name in ["fxsave", "fxsave64"] do
    let _ ← onIntrinsic emu name fun current _ => do
      save current
      pure .proceed
  for name in ["fxrstor", "fxrstor64"] do
    let _ ← onIntrinsic emu name fun current _ => do
      load current
      pure .proceed
  -- It counts up, so that what measures with it sees time pass.
  let _ ← onIntrinsic emu "rdtsc" fun current _ => do
    let now := (← kernel.get).cycles
    kernel.modify fun kernel => { kernel with cycles := now + 1000 }
    setReg current a (bits wide (now % 2 ^ 32))
    setReg current d (bits wide (now / 2 ^ 32))
    pure .proceed
  pure ()

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
    for name in ["FPCR", "FPSR"] do
      setReg emu ⟨name, .imm 32, 0, false⟩ (bits 32 0)
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
    for name in ["CS", "DS", "ES", "FS", "GS", "SS"] do
      setReg emu ⟨name, .imm 16, 0, false⟩ (bits 16 0)
    setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 0x37f)
    setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 0xffff)
    setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 0x1f80)
  | .x86_64 => do
  for name in ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15",
      "FS_BASE", "GS_BASE"] do
    setReg emu (word name) (bits 64 0)
  for name in ["CF", "OF", "SF", "ZF", "AF", "PF", "DF", "IF"] do
    setReg emu ⟨name, .imm 1, 0, false⟩ (bits 1 0)
  for index in List.range 32 do
    for (name, width) in [(s!"XMM{index}", 128), (s!"YMM{index}", 256), (s!"ZMM{index}", 512)] do
      setReg emu ⟨name, .imm width, 0, false⟩ (bits width 0)
  for index in List.range 8 do
    setReg emu ⟨s!"ST{index}", .imm 80, 0, false⟩ (bits 80 0)
  setReg emu ⟨"FPU_CONTROL", .imm 16, 0, false⟩ (bits 16 0x37f)
  setReg emu ⟨"FPU_STATUS", .imm 16, 0, false⟩ (bits 16 0)
  setReg emu ⟨"FPU_TAG", .imm 16, 0, false⟩ (bits 16 0xffff)
  setReg emu ⟨"MXCSR", .imm 32, 0, false⟩ (bits 32 0x1f80)

/-- The segments of a file in pages at `base`, as the kernel maps them, with zeros after what is in the file. Returns where they
end. A page that two segments share has the bytes of both, and the protection of the first. -/
private def mapProgram (emu : Emu) (data : ByteArray) (program : Elf.Program) (base : Nat) : IO Nat := do
  let sorted := program.segments.toArray.qsort fun left right => left.address < right.address
  let mut mappedTo := 0
  for segment in sorted do
    let first := base + segment.address
    let start := max mappedTo (pageDown first)
    let stop := pageUp (first + segment.memorySize)
    if start < stop then
      let bytes := ByteArray.mk ((List.range (stop - start)).toArray.map fun offset =>
        let address := start + offset
        if first ≤ address && address < first + segment.fileSize then data.get! (segment.offset + address - first) else 0)
      map emu ⟨start, bytes, ⟨segment.flags &&& 4 != 0, segment.flags &&& 2 != 0, segment.flags &&& 1 != 0⟩⟩
      mappedTo := stop
  pure mappedTo

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

/-- The stack that the kernel hands over: where the arguments, the environment and the auxiliary vector are. -/
private def mapStack (emu : Emu) (architecture : Architecture) (arguments environment : List String) (auxiliary : List (Nat × Nat)) : IO Unit := do
  mapZeros emu (stackTop architecture - stackSize) stackSize ⟨true, true, false⟩
  let mut cursor := stackTop architecture - 16
  let wordSize := architecture.bits / 8
  let place (cursor : Nat) (text : ByteArray) : IO Nat := do
    let at_ := cursor - text.size
    write emu at_ text
    pure at_
  cursor ← place cursor (architecture.name ++ "\x00").toUTF8
  let platform := cursor
  cursor ← place cursor (ByteArray.mk ((List.range 16).map fun index => (index * 37 + 11).toUInt8).toArray)
  let random := cursor
  let mut argumentAddresses : List Nat := []
  for text in arguments.reverse do
    cursor ← place cursor (text ++ "\x00").toUTF8
    argumentAddresses := cursor :: argumentAddresses
  let mut environmentAddresses : List Nat := []
  for text in environment.reverse do
    cursor ← place cursor (text ++ "\x00").toUTF8
    environmentAddresses := cursor :: environmentAddresses
  let execfn := argumentAddresses.headD 0
  let vector := auxiliary ++ [(15, platform), (25, random), (31, execfn), (0, 0)]
  let cells := [argumentAddresses.length] ++ argumentAddresses ++ [0] ++ environmentAddresses ++ [0] ++
    vector.flatMap fun entry => [entry.1, entry.2]
  -- It is aligned to 16 where the program starts.
  let pointer := (cursor - wordSize * cells.length) / 16 * 16
  for (cell, index) in cells.zipIdx do
    write emu (pointer + wordSize * index) (Abi.field architecture.big wordSize cell)
  setReg emu ⟨(threadRegisters emu.config.syscallAbi).1, .imm architecture.bits, 0, false⟩ (bits architecture.bits pointer)

/-- A parsed program and what interprets it in an emulator that has nothing mapped: its registers, its memory, its stack and
where it starts. It gives where its heap starts and its auxiliary vector, as a type and a value by turns. -/
private def loadProgram (emu : Emu) (architecture : Architecture) (path : String) (data : ByteArray) (program : Elf.Program)
    (interpreter : Option (ByteArray × Elf.Program)) (arguments environment : List String) (base : Option Nat := none) : IO (Nat × List Nat) := do
  let base := if program.relocatable then base.getD (programBase architecture) else 0
  resetRegisters emu architecture
  let top ← mapProgram emu data program base
  let lowest := program.segments.foldl (fun lowest segment => min lowest segment.address) (2 ^ 63)
  let entry ← match interpreter with
    | some (bytes, loaded) =>
      let _ ← mapProgram emu bytes loaded (interpreterBase architecture)
      pure (interpreterBase architecture + loaded.entry)
    | none => pure (base + program.entry)
  -- ELFv1: where a program starts is a function descriptor, of the address of its code and its table of contents.
  let (bias, flags) := match interpreter with
    | some (_, loaded) => (interpreterBase architecture, loaded.flags)
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
    -- A 32-bit or a 64-bit machine, with floating point, AltiVec and VSX.
    | .powerpc wide _ => (if wide == 64 then 0xc0000000 else 0x80000000) + 0x18000080
  -- AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_BASE, AT_FLAGS, AT_ENTRY, the ids of root, AT_HWCAP, AT_CLKTCK, AT_SECURE, AT_HWCAP2
  let auxiliary := [(3, base + lowest + program.headerOffset), (4, program.headerSize), (5, program.headerCount), (6, 4096),
    (7, if interpreter.isSome then interpreterBase architecture else 0), (8, 0), (9, base + program.entry), (11, 0), (12, 0), (13, 0), (14, 0),
    (16, capabilities), (17, 100), (23, 0), (26, 0)]
  mapStack emu architecture (if arguments.isEmpty then [path] else arguments) environment auxiliary
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

/-- A program of a path of the kernel, as far as it can be told that it will run, and what its arguments come to: a script
is run by what its first line names, with the script after that, to a depth that Linux has too. -/
private def programOf (kernel : Kernel) (architecture : Architecture) : Nat → String → List String →
    Result (String × ByteArray × Elf.Program × Option (ByteArray × Elf.Program) × List String)
  | 0, _, _ => .error Errno.enoexec
  | depth + 1, path, arguments => do
    let data ← fileOf kernel path
    if data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33 then
      let first := (String.fromUTF8? (data.extract 2 (min data.size 256))).getD ""
      let line := ((first.splitOn "\n").headD "").trimAscii.toString
      -- All of the line after the name is one argument.
      match line.splitOn " " with
      | [""] => .error Errno.enoexec
      | name :: rest =>
        let given := (" ".intercalate rest).trimAscii.toString
        programOf kernel architecture depth name (name :: (if given.isEmpty then [] else [given]) ++ [path] ++ arguments.drop 1)
      | [] => .error Errno.enoexec
    else
      let some program := (Elf.parse data).toOption | .error Errno.enoexec
      if Architecture.ofElf program.machine program.bits program.big program.flags != some architecture then .error Errno.enoexec
      let interpreter ← match program.interpreter with
        | none => .ok none
        | some name => do
          let bytes ← fileOf kernel name
          let some loaded := (Elf.parse bytes).toOption | .error Errno.enoexec
          .ok (some (bytes, loaded))
      .ok (path, data, program, interpreter, arguments)

/-- What `execve` runs, of the directories of the host that the machine sees: the program, what a script names to run it, and the
interpreter of a program of ELF, as `programOf` looks for them. -/
private def programFromHost (machine : Machine) (path : String) : IO Unit := do
  if (← machine.hostMounts.get).isEmpty then return
  let mut path := path
  for _ in [0:4] do
    fromHost machine path
    let .ok data := fileOf (← machine.kernel.get) path | return
    if data.size ≥ 2 && data.get! 0 == 35 && data.get! 1 == 33 then
      let first := (String.fromUTF8? (data.extract 2 (min data.size 256))).getD ""
      path := ((((first.splitOn "\n").headD "").trimAscii.toString.splitOn " ").headD "")
    else
      if let some name := (Elf.parse data).toOption.bind (·.interpreter) then fromHost machine name
      return

/-- The strings of a list of pointers that a null ends, as `execve` is given them. -/
private def readStrings (emu : Emu) (architecture : Architecture) (address : Nat) : IO (List String) := do
  if address == 0 then return []
  let size := architecture.bits / 8
  let rec go : Nat → Nat → List String → IO (List String)
    | 0, _, found => pure found.reverse
    | fuel + 1, at_, found => do
      let bytes ← read emu at_ size
      let bytes := if architecture.big then bytes.toList else bytes.toList.reverse
      let pointer := bytes.foldl (fun value byte => value * 256 + byte.toNat) 0
      if pointer == 0 then pure found.reverse
      else go fuel (at_ + size) ((← readString emu pointer) :: found)
  go 65536 address []

/-- `execve`: nothing of the process changes until the program is known to run, and then all its memory and its threads other
than this one are gone, and its descriptors but for those that stay open over it. -/
private def execute (machine : Machine) (emu : Emu) (args : List Nat) : IO SyscallAction := do
  let architecture := machine.architecture
  let kernel ← machine.kernel.get
  let group := (← currentTask emu).group
  match ← (do pure (← readString emu (args.getD 0 0), ← readStrings emu architecture (args.getD 1 0),
      ← readStrings emu architecture (args.getD 2 0)) : IO _).toBaseIO with
  | .error _ => pure (errorOf Errno.efault)
  | .ok (path, arguments, environment) =>
    let (base, relative) := kernel.pathIn group (kernel.process group).cwd path
    let absolute := if relative.startsWith "/" then relative else base ++ "/" ++ relative
    programFromHost machine absolute
    let kernel ← machine.kernel.get
    match programOf kernel architecture 4 absolute (if arguments.isEmpty then [path] else arguments) with
    | .error errno => pure (errorOf errno)
    | .ok (name, data, program, interpreter, arguments) =>
      let table ← emu.taskTable.get
      let current ← thread emu
      for task in table.tasks do
        if task.group == group && task.tid != current && task.status.isNone then
          emu.taskTable.modify (·.exitTask task.tid 0 group)
          emu.threadsRef.modify (setThreadStopped · task.tid true)
      -- A child of `vfork` has its parent's memory, which the parent keeps: the program goes in memory of its own.
      let space := (← currentTask emu).space
      if table.tasks.any fun task => task.space == space && task.group != group && task.status.isNone then
        leaveSharedMemory emu
      for region in ← emu.regions.get do
        unmap emu region.address region.data.size
      let (top, auxiliary) ← loadProgram emu architecture name data program interpreter arguments environment
      emu.redirect.set (some (← pc emu))
      wakePipeReaders emu
      let process := kernel.process group
      machine.kernel.set (kernel.setProcess group { process with
        descriptors := process.descriptors.filter fun _ entry => !entry.closeOnExec
        breakStart := top, breakEnd := top, command := arguments, environment, program := name, auxiliary, mappings := [] })
      releaseVfork emu current
      machine.timers.executed group
      pure (.returnValue 0)

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
    if (name.splitOn "binary_80").length > 1 then field "FPU_CONTROL" 16 10 ["rne", "rtn", "rtp", "rtz", "rne", "rtn", "rtp", "rtz"]
    else field "MXCSR" 32 13 ["rne", "rtn", "rtp", "rtz", "rne", "rtn", "rtp", "rtz"]
  | .aarch64 => field "FPCR" 32 22 binaryModes
  | .arm => field "FPSCR" 32 22 binaryModes
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
  | .arm => let zero := test "FPSCR" 32 24; (zero, zero, test "FPSCR" 32 25)
  | .x86_64 | .i686 =>
    if (name.splitOn "binary_80").length > 1 then (false, false, false) else (test "MXCSR" 32 6, test "MXCSR" 32 15, false)
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
  let (zeroIn, zeroOut, defaultNaN) := floatControls architecture env name
  if !zeroIn && !zeroOut && !defaultNaN then (id, id) else
  let (source, target) := Bap.Float.formatsOf name
  let inputs (values : List Nat) : List Nat :=
    match source, zeroIn with
    | some format, true => values.map (Bap.Float.flush format)
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
  let rules := floatRules architecture
  let (register, width, invalid, divide, over, under, inexact) : String × Nat × Nat × Nat × Nat × Nat × Nat := match architecture with
    | .x86_64 | .i686 =>
      if (name.splitOn "binary_80").length > 1 then ("FPU_STATUS", 16, 0, 2, 3, 4, 5) else ("MXCSR", 32, 0, 2, 3, 4, 5)
    | .aarch64 => ("FPSR", 32, 0, 1, 2, 3, 4)
    | .arm => ("FPSCR", 32, 0, 1, 2, 3, 4)
    | .riscv64 | .riscv32 => ("FCSR", 32, 4, 3, 2, 1, 0)
    | .mips bits _ _ => ("FCSR", bits, 6, 5, 4, 3, 2)
    | .powerpc _ _ => ("FPSCR", 64, 29, 26, 28, 27, 25)
  let var : Bap.Var := ⟨register, .imm width, 0, false⟩
  match Bil.lookup env var with
  | .ok (.bits value) =>
    let old := value.toNat
    let (zeroIn, zeroOut, _) := floatControls architecture env name
    let x86 := architecture == .x86_64 || architecture == .i686
    let (source, target) := Bap.Float.formatsOf name
    let flushedIn := match source with
      | some format => inputs.any (Bap.Float.isDenormal format)
      | none => false
    let effective := match source, zeroIn with
      | some format, true => inputs.map (Bap.Float.flush format)
      | _, _ => inputs
    let raised := Bap.Float.raisedBy rules name effective result (old.testBit inexact && !zeroOut)
    -- What a denormal result would have been, had it not been a zero.
    let flushedOut := zeroOut && (match target, Bap.Float.evaluateWith rules name effective with
      | some format, some unflushed => Bap.Float.isDenormal format unflushed.2
      | _, _ => false)
    -- What underflows to a zero isn't inexact on ARM, as what is a zero is what it was to be.
    let raised := if flushedOut then { raised with underflow := true, inexact := x86 }
      else if zeroOut && !x86 && raised.underflow then { raised with inexact := false }
      else raised
    let flag (on : Bool) (bit : Nat) : Nat := if on then 1 <<< bit else 0
    let added := flag raised.invalid invalid ||| flag raised.divideByZero divide ||| flag raised.overflow over |||
      flag raised.underflow under ||| flag raised.inexact inexact |||
      (if x86 then flag raised.denormal 1 else flag (zeroIn && flushedIn) 7)
    if old ||| added == old then [] else [(var, .bits (BitVec.ofNat width (old ||| added)))]
  | _ => []

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
  emu.intrinsicName.set (roundedName architecture)
  emu.intrinsicRaises.set (raisedFlags architecture)
  emu.intrinsicControls.set (controlled architecture)
  emu.intrinsicServer.set (some (Bap.Float.evaluateWith (match architecture with
    | .x86_64 | .i686 => .x86
    | .aarch64 | .arm => .arm
    | .riscv64 | .riscv32 => .riscv
    | .mips _ _ true => .powerpc
    | .mips _ _ false => .mips
    | .powerpc _ _ => .powerpc)))
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

/-- The models that every machine has, with the versions of what they keep: of ptrace, 2 has the stops that tracees have yet to make
and those that stopped for their end, 3 the exits that tracers that aren't parents have yet to hear of, and 4 the steps that tracees have yet to make. -/
private def builtinModels : List (String × Nat) :=
  [(Signals.modelId, 1), (Ptrace.modelId, 4), (Seccomp.modelId, 1), (Timers.modelId, 1), (Ring.modelId, 1), (heapModelId, 1), (libraryModelId, 1),
    (traceModelId, 4)]

private def builtinVersion (id : String) : Nat := (builtinModels.lookup id).getD 1

/-- Where a word is to `futex` that is in the file of a shared mapping, which is no address space, of which there are as many as tasks. -/
private def sharedFutexSpace : Nat := Kernel.fileSpace

/-- What makes an emulator a machine: its kernel behind its system calls. None of it is in a checkpoint. -/
private def machineOf (architecture : Architecture) (emu : Emu) (kernel : Kernel) (watch : Option (Nat → List Nat → IO Unit))
    (handler : Option SyscallHandler) (target : Nat) (models : List RuntimeModel) : IO Machine := do
  let signals : Signals := { architecture, returnPage := stackTop architecture + 4096, table := ← IO.mkRef {}
                             failures := ← IO.mkRef #[], skipIgnoredFaults := ← IO.mkRef false
                             intercept := ← IO.mkRef fun _ _ _ => pure false, tracer := ← IO.mkRef fun _ => pure none
                             jobControl := ← IO.mkRef fun _ _ _ => pure (), interrupted := ← IO.mkRef fun _ _ _ _ => pure ()
                             sent := ← IO.mkRef fun _ => pure (), pgidOf := ← IO.mkRef pure, members := ← IO.mkRef fun _ => pure [] }
  let ptrace ← Ptrace.make architecture signals
  let kernelRef ← IO.mkRef kernel
  let timers ← Timers.make architecture kernelRef signals
  let machine : Machine := { architecture, emu, kernel := kernelRef, models := ← IO.mkRef [], target, handled := handler.isSome, signals, ptrace, timers, notifier := ← Notify.make, hostMounts := ← IO.mkRef [], hostSeen := ← IO.mkRef {}, rings := ← IO.mkRef {}, releases := ← IO.mkRef 0, heaps := ← IO.mkRef {}, libraries := ← IO.mkRef {}, history := ← IO.mkRef none, restored := ← IO.mkRef [], listing := ← IO.mkRef none, hostHooks := ← IO.mkRef {}, importSlots := ← IO.mkRef {} }
  if let some watch := watch then
    let _ ← onSyscall emu fun _ number args => do
      watch number args
      pure .default
  if let some handler := handler then
    let _ ← onSyscall emu handler
  -- What a process wrote to shared memory is in the file before anything can look at the file.
  let _ ← onSyscall emu fun emu _ _ => do
    flushShared machine emu
    pure .default
  emu.leavingSpace.set (some (flushShared machine emu))
  -- What was found of the instances of `inotify` is of the kernel that was.
  machine.restored.modify ((fun _ => Notify.forget machine.notifier) :: ·)
  -- And what was looked for on the host may not be in the kernel that was.
  machine.restored.modify ((fun _ => machine.hostSeen.set {}) :: ·)
  emu.enteredSpace.set (some (refreshShared machine emu))
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
  machine.models.modify (· ++ [{ id := Ptrace.modelId, version := builtinVersion Ptrace.modelId, state := { save := ptrace.save, load := ptrace.load emu } }])
  -- And what a thread may call, which ptrace asks of each call once a tracer saw it start.
  let seccomp ← Seccomp.attach architecture signals ptrace emu
  machine.models.modify (· ++ [{ id := Seccomp.modelId, version := builtinVersion Seccomp.modelId, state := seccomp.modelState emu }])
  -- Time goes on as instructions run, and to what happens next when nothing can.
  emu.now.set (some do pure (← kernelRef.get).clock)
  -- The thread that is current, which a timer or a deadline woke there, takes what came for it, as a switch to it would have it.
  let resumingCurrent (action : IO Bool) : IO Bool := do
    let waited ← Bap.Emu.stopped emu
    let changed ← action
    if waited && !(← Bap.Emu.stopped emu) then
      signals.switchedIn emu
      timers.resumed emu
    pure changed
  emu.idle.set (some (resumingCurrent (timers.idle emu)))
  -- A signal that comes has what waits to read one look again, and what it woke from a call that runs again hear of it.
  signals.sent.set wakePipeReaders
  signals.pgidOf.set fun group => do pure ((← kernelRef.get).pgidOf group)
  signals.members.set fun pgid => do
    let live := (((← emu.taskTable.get).tasks.filter (·.status.isNone)).map (·.group)).eraseDups
    pure (Identity.members (← kernelRef.get) live pgid)
  signals.interrupted.set (timers.interrupted)
  emu.betweenTurns.modify (· ++ [do let _ ← resumingCurrent (do timers.tick emu; pure true)])
  let timeState : ModelState := { save := timers.save, load := timers.load }
  machine.models.modify (· ++ [{ id := Timers.modelId, version := builtinVersion Timers.modelId, state := timeState }])
  -- And what AIO and io_uring have.
  machine.models.modify (· ++ [{ id := Ring.modelId, version := builtinVersion Ring.modelId
                                 state := { save := Ring.save machine.rings, load := Ring.load machine.rings } }])
  signals.serve emu
  -- A thread that a switch has run again has what was left of a sleep that a signal ended.
  let arrived ← emu.switchedIn.get
  emu.switchedIn.set (some do
    if let some arrived := arrived then arrived
    timers.resumed emu)
  -- A process that is over has closed what it had open.
  let heard ← emu.processExited.get
  emu.processExited.set (some fun group status => do
    if let some heard := heard then heard group status
    -- What `SEM_UNDO` did of it is taken back, its timers end, and what `inotify` it had is looked for again.
    kernelRef.modify (SysV.exited · group)
    timers.exited emu group
    Notify.forget machine.notifier
    released machine
    wakePipeReaders emu
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
    if machine.architecture.call number == some .execve then
      let action ← handOver machine emu (← execute { machine with emu } emu args)
      -- It is a new program if it is going there, and nothing else sends it anywhere in the middle of a system call.
      if (← emu.redirect.get).isSome then
        signals.executed (← currentTask emu).group (← thread emu)
        ptrace.executed emu
        -- What it had is gone with its memory.
        let space := (← currentTask emu).space
        machine.heaps.modify (·.erase space)
        machine.libraries.modify (·.erase space)
      pure action
    else pure .default
  let _ ← serveKernelCalls machine
  let _ ← serveTaskCalls emu
  let _ ← serveRest machine
  if architecture == .x86_64 || architecture == .i686 then serveCpu emu machine.kernel architecture.bits
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
  let (top, auxiliary) ← loadProgram emu architecture path data program interpreter arguments environment base
  let first := (← currentTask emu).group
  let kernel := kernel.withConsole first input
  let kernel := kernel.setProcess first { kernel.process first with
    breakStart := top, breakEnd := top, command := if arguments.isEmpty then [path] else arguments, environment, program := path, auxiliary }
  let kernel := Proc.install kernel.installDevices
  machineOf architecture emu kernel watch handler (targetDigest architecture data) models

/-- Runs `fuel` instructions at most in turns of the scheduler, in pieces that end where `every` says from where it starts, which is what it goes by when it runs them again. Each piece ends
with shared memory in its files and what was written gone to `output`, and then `after` sees how many instructions it ran and whether that was all of them. -/
private def Machine.runPieces (machine : Machine) (output : ByteArray → IO Unit) (quantum fuel every : Nat)
    (after : Nat → Bool → IO Unit) : IO ScheduleOutcome := do
  -- What it writes in a turn goes out when the turn ends, so that a long turn is what holds it up.
  let rec go : Nat → Nat → Nat → IO ScheduleOutcome
    | 0, _, _ => pure .outOfFuel
    | rounds + 1, left, since => do
      let turn := min left (min (64 * quantum) (every - since))
      let before ← machine.emu.executed.get
      let outcome ← runProcesses machine.emu quantum turn
      flushShared machine machine.emu
      let (kernel, written) := (← machine.kernel.get).takeOutput
      machine.kernel.set kernel
      if written.size > 0 then output written
      let ran := (← machine.emu.executed.get) - before
      after ran (outcome == .outOfFuel)
      match outcome with
      | .outOfFuel =>
        let since := if since + turn ≥ every then 0 else since + turn
        if left ≤ turn then pure .outOfFuel else go rounds (left - turn) since
      | other => pure other
  go (fuel + 1) fuel 0

private def Machine.modelBytes (machine : Machine) : IO (List (AttachedModel × ByteArray)) := do
  (← machine.models.get).mapM fun model => do pure (model, ← model.state.save)

/-- It is as whole as a checkpoint has to be: not in the middle of an instruction, or from a worker of a parallel round. -/
private def Machine.keep (machine : Machine) : IO Machine.Kept := do
  if (← machine.emu.serving.get) || machine.emu.engine.deferMemorySync then
    throw <| IO.userError "a machine can't be saved in the middle of an instruction, or by a worker of a parallel round: stop the thread, and save it once the run returns"
  pure {
    emulator := ← snapshot machine.emu
    run := ← runState machine.emu
    kernel := ← machine.kernel.get
    models := (← machine.modelBytes).map fun (model, bytes) => (model.id, bytes)
  }

private def Machine.restoreKept (machine : Machine) (kept : Machine.Kept) : IO Unit := do
  Bap.Emu.restore machine.emu kept.emulator
  -- Which breakpoints there are is up to who is debugging it now.
  setRunState machine.emu { kept.run with breakpoints := [] }
  machine.kernel.set kept.kernel
  for model in ← machine.models.get do
    if let some bytes := kept.models.lookup model.id then model.state.load bytes

/-- What the machine is, and where it is in what it keeps for `stepBack`, if it keeps that. -/
def Machine.save (machine : Machine) : IO Machine.Saved := do
  pure { toKept := ← machine.keep, history := ← machine.history.get }

/-- The machine is what it was saved as. If it keeps a history, that is the history it had then: where it was, and what it could step back to from there, and not what it ran
after. One that was saved before it kept any has nothing to step back to, as nothing says where it was. -/
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
  if target > at_ then
    let muted ← machine.emu.breakpointsMuted.get
    machine.emu.breakpointsMuted.set true
    try
      let _ ← machine.runPieces (fun _ => pure ()) quantum (target - at_) history.every fun _ _ => pure ()
    finally
      machine.emu.breakpointsMuted.set muted
  -- What came after is what may not happen again.
  machine.history.set (some { history with position := target, saved := history.saved.extract 0 (index + 1) })
  for heard in ← machine.restored.get do heard s!"Machine.stepBack {count}"

/-! Memory of a guest for who runs it. -/

/-- Runs this in the address space of a process, which is that of the thread that runs if it is of that process. Going there and back is
a switch of threads to the emulator, which takes what threads hold exclusively and what is left of a turn, and a look at memory isn't
to change what a guest does, so that those stay. It can't be done in the middle of an instruction. -/
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
  let width ← wordWidth emu
  let monitorVar := exclusiveMonitor width
  let monitorOf (id : ThreadId) : IO (Option Bap.Value) := do
    match ← (threadReg emu id monitorVar).toBaseIO with
    | .ok value => pure (some value)
    | .error _ => pure none
  let turn ← emu.turnUsed.get
  let homeMonitor ← monitorOf home
  let targetMonitor ← monitorOf target.tid
  let arrived ← emu.switchedIn.get
  emu.switchedIn.set none
  try
    switchThread emu target.tid
    try action
    finally switchThread emu home
  finally
    emu.switchedIn.set arrived
    if let some value := homeMonitor then setThreadReg emu home monitorVar value
    if let some value := targetMonitor then setThreadReg emu target.tid monitorVar value
    emu.turnUsed.set turn

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

/-- The most that one block can have: a mapping is held in memory of the host from the start. -/
def Machine.mallocLimit : Nat := 2 ^ 32

/-- The heap of the address space that runs, with what is no longer mapped gone from it. -/
private def Machine.currentHeap (machine : Machine) : IO (Nat × GuestHeap) := do
  let space := (← currentTask machine.emu).space
  let regions ← machine.emu.regions.get
  let heap := ((← machine.heaps.get).getD space {}).keepChunks fun chunk => coversRange regions chunk.1 (chunk.1 + chunk.2)
  pure (space, heap)

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
def checkpointFormat : Nat := 10

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
    tasks := snapshot.table.tasks, waiters := snapshot.table.waiters, signals, mapped, resident }
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
