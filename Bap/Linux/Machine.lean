import Bap.Emu.Tasks
import Bap.Emu.Checkpoint
import Bap.Linux.Calls
import Bap.Linux.Image
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

structure Machine where
  architecture : Architecture
  emu : Emu
  kernel : IO.Ref Kernel

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
  pure (String.fromUTF8? (← go 16 address ByteArray.empty) |>.getD "")

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

/-- `mmap`: of a file, here. What is anonymous is for `serveTaskCalls`. A writable shared mapping isn't written back. -/
private def serveFileMap (machine : Machine) (group address size bits flags fd offset : Nat) : IO SyscallAction := do
  let emu := machine.emu
  if flags &&& 3 == 1 && bits &&& 2 != 0 then
    return errorOf Errno.enosys
  match (← machine.kernel.get).mappedBytes group fd offset (pageUp size) with
  | .error errno => pure (errorOf errno)
  | .ok data =>
    try
      pure (.returnValue (← placeMapping emu address (flags &&& 0x10 != 0) data bits))
    catch _ => pure (errorOf Errno.enomem)

/-- `brk`: it grows by mapping zeros and doesn't give back what it had, as far as the program can tell. -/
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
        map machine.emu ⟨mappedTo, Bap.zeroBytes (needed - mappedTo), ⟨true, true, false⟩⟩
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
    cwd := process.cwd
    ranges := regions.map fun region =>
      { start := region.address, size := region.data.size, readable := region.protection.readable
        writable := region.protection.writable, executable := region.protection.executable }
    breakStart := process.breakStart
    breakEnd := process.breakEnd
    stackStart
    bits := architecture.bits
    machine := architecture.name
    clock := kernel.clock
    uptime := kernel.clock - bootClock
    processes := ← liveProcesses emu }

/-- The system calls of files, memory that files are mapped into, time and what a process asks of itself. -/
private def kernelCall (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO SyscallAction := do
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
    -- `path` from an address, in the directory that the call says.
    let at_ (directory address : Nat) (action : String → String → IO SyscallAction) : IO SyscallAction := do
      match kernel.baseOf group directory (atCwd directory) with
      | .error errno => pure (errorOf errno)
      | .ok from_ =>
        match ← (readString emu address).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok path => action from_ path
    let here := 2 ^ 64 - 100
    let openAt (directory address flags mode : Nat) : IO SyscallAction :=
      at_ directory address fun from_ path => do
        let flags := architecture.openFlags flags
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
        | none => applyNat machine (·.openPath group from_ path flags mode)
    let accessAt (directory address : Nat) : IO SyscallAction :=
      at_ directory address fun from_ path =>
        pure (match kernel.statPath from_ path with
          | .error errno => errorOf errno
          | .ok _ => .returnValue 0)
    let readInto (fd address count : Nat) : IO SyscallAction := do
      match kernel.read group fd count with
      | .error errno => pure (errorOf errno)
      | .ok (next, bytes) =>
        machine.kernel.set next
        returning emu address bytes bytes.size
    let writeOut (fd address count : Nat) : IO SyscallAction := do
      match ← (read emu address count).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok bytes => applyNat machine (·.write group fd bytes)
    let statAt (directory address out : Nat) (follow : Bool) : IO SyscallAction :=
      at_ directory address fun from_ path =>
        match kernel.statPath from_ path follow with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu out (architecture.stat value)
    let clock (out scale : Nat) : IO SyscallAction := do
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu out (Abi.time now scale big wordSize)
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
    match call with
    | .read => readInto (arg 0) (arg 1) (arg 2)
    | .write => writeOut (arg 0) (arg 1) (arg 2)
    | .open_ => openAt here (arg 0) (arg 1) (arg 2)
    | .openat => openAt (arg 0) (arg 1) (arg 2) (arg 3)
    | .close => apply machine (·.close group (arg 0))
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
    | .readv => vectors (arg 0) (arg 1) (arg 2) readInto
    | .writev => vectors (arg 0) (arg 1) (arg 2) writeOut
    | .access => accessAt here (arg 0)
    | .faccessat => accessAt (arg 0) (arg 1)
    | .dup => applyNat machine (·.dup group (arg 0))
    | .dup2 => applyNat machine (·.dupTo group (arg 0) (arg 1))
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
      | _ => pure (errorOf Errno.einval)
    | .ioctl =>
      -- No descriptor is a terminal.
      pure (errorOf (match kernel.statDescriptor group (arg 0) with | .ok _ => Errno.enotty | .error errno => errno))
    | .getdents =>
      match kernel.directoryEntries group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok (id, first, entries) =>
        let (bytes, count) := Abi.dirents entries first (arg 2) big
        if count == 0 && !entries.isEmpty then
          pure (errorOf Errno.einval)
        else
          machine.kernel.set (kernel.advance id count)
          returning emu (arg 1) bytes bytes.size
    | .getcwd =>
      let text := (cwd ++ "\x00").toUTF8
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
    | .mmap =>
      if arg 3 &&& architecture.mapAnonymous != 0 then pure .default
      else serveFileMap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5)
    | .mmap2 =>
      if arg 3 &&& architecture.mapAnonymous != 0 then pure .default
      else serveFileMap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5 * 4096)
    | .mremap => pure (errorOf Errno.enomem)
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
    | .getrlimit =>
      let unlimited := 2 ^ wide - 1
      let stack := if arg 0 == 3 then 8 * 1024 * 1024 else unlimited
      returning emu (arg 1) (cell wordSize stack ++ cell wordSize unlimited)
    | .prlimit =>
      let stack := if arg 1 == 3 then 8 * 1024 * 1024 else 2 ^ 64 - 1
      returning emu (arg 3) (cell 8 stack ++ cell 8 (2 ^ 64 - 1))
    | .getrandom =>
      -- A fixed sequence, as a run is the same each time.
      let bytes := ByteArray.mk ((List.range (arg 1)).map fun index => (index * 167 + 13).toUInt8).toArray
      returning emu (arg 0) bytes (arg 1)
    | .sigaltstack => returning emu (arg 1) (ByteArray.mk (Array.replicate (3 * wordSize) 0))
    | .schedGetaffinity => returning emu (arg 2) (cell wordSize 1) wordSize
    | .succeeds => pure (.returnValue 0)

/-- The argument of a call that is a path, if it has one, and whether it is relative to a descriptor. -/
private def pathArgument : Call → Option Nat
  | .open_ | .stat | .lstat | .access | .readlink | .chdir | .truncate | .truncate64 | .statfs | .statfs64 => some 0
  | .openat | .fstatat | .statx | .faccessat | .readlinkat => some 1
  | _ => none

/-- Makes `/proc` what it has to be for a call that may look at it, which only a path can tell. -/
private def refreshProc (machine : Machine) (emu : Emu) (call : Call) (args : List Nat) : IO Unit := do
  if let some index := pathArgument call then
    match ← (readString emu (args.getD index 0)).toBaseIO with
    | .error _ => pure ()
    | .ok path =>
      let group := (← currentTask emu).group
      let cwd := ((← machine.kernel.get).process group).cwd
      let relative := !path.startsWith "/"
      if path.startsWith "/proc" || (relative && (index == 1 || cwd.startsWith "/proc")) then
        let self ← thread emu
        let live ← liveProcesses emu
        let tasks := (← emu.taskTable.get).tasks.filter (·.status.isNone)
        machine.kernel.modify (Proc.refresh · group self live fun pid =>
          (tasks.filter (·.group == pid)).map (·.tid))

/-- What a call gives, as the guest has it. -/
private def handOver (machine : Machine) (emu : Emu) : SyscallAction → IO SyscallAction
  | .returnValue value =>
    if value ≥ 2 ^ 64 - 4096 then syscallReturn emu (.error (machine.architecture.errno (2 ^ 64 - value)))
    else syscallReturn emu (.ok value)
  | action => pure action

private def serveKernelCalls (machine : Machine) : IO HookId :=
  onSyscall machine.emu fun emu number args => do
    match machine.architecture.call number with
    -- What serveTaskCalls serves.
    | none => pure .default
    | some call =>
      refreshProc machine emu call args
      handOver machine emu (← kernelCall machine emu call args)

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

private def fileOf (kernel : Kernel) (path : String) : Result ByteArray := do
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
  map emu ⟨stackTop architecture - stackSize, Bap.zeroBytes stackSize, ⟨true, true, false⟩⟩
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
where it starts. It gives where its heap starts. -/
private def loadProgram (emu : Emu) (architecture : Architecture) (path : String) (data : ByteArray) (program : Elf.Program)
    (interpreter : Option (ByteArray × Elf.Program)) (arguments environment : List String) : IO Nat := do
  let base := if program.relocatable then programBase architecture else 0
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
  -- AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_BASE, AT_FLAGS, AT_ENTRY, the ids of root, AT_HWCAP, AT_CLKTCK, AT_SECURE
  let auxiliary := [(3, base + lowest + program.headerOffset), (4, program.headerSize), (5, program.headerCount), (6, 4096),
    (7, if interpreter.isSome then interpreterBase architecture else 0), (8, 0), (9, base + program.entry), (11, 0), (12, 0), (13, 0), (14, 0),
    (16, capabilities), (17, 100), (23, 0)]
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
  pure top

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
    let absolute := if path.startsWith "/" then path else (kernel.process group).cwd ++ "/" ++ path
    match programOf kernel architecture 4 absolute (if arguments.isEmpty then [path] else arguments) with
    | .error errno => pure (errorOf errno)
    | .ok (name, data, program, interpreter, arguments) =>
      let table ← emu.taskTable.get
      let current ← thread emu
      for task in table.tasks do
        if task.group == group && task.tid != current && task.status.isNone then
          emu.taskTable.modify (·.exitTask task.tid 0 group)
          emu.threadsRef.modify (setThreadStopped · task.tid true)
      for region in ← emu.regions.get do
        unmap emu region.address region.data.size
      let top ← loadProgram emu architecture name data program interpreter arguments environment
      emu.redirect.set (some (← pc emu))
      let process := kernel.process group
      machine.kernel.set (kernel.setProcess group { process with
        descriptors := process.descriptors.filter fun _ entry => !entry.closeOnExec
        breakStart := top, breakEnd := top, command := arguments, environment, program := name })
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

/-- An emulator of an architecture, as a Linux machine needs it, with nothing mapped. -/
private def emulatorOf (architecture : Architecture) : IO Emu := do
  -- A real program runs more code than the working set of a few thousand blocks that the default is for, and past it, each one
  -- would be lifted each time it runs. Most of its code runs at its start, a few times, and compiling that takes longer than
  -- running it: with this threshold, `ls` takes a third of the time, and a long loop no longer.
  let tuned (config : Config) : Config := { config with cacheLimit := 1048576, hotThreshold := 1024 }
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

/-- What makes an emulator a machine: its kernel behind its system calls. None of it is in a checkpoint. -/
private def machineOf (architecture : Architecture) (emu : Emu) (kernel : Kernel) (watch : Option (Nat → List Nat → IO Unit))
    (handler : Option SyscallHandler) : IO Machine := do
  let machine : Machine := { architecture, emu, kernel := ← IO.mkRef kernel }
  if let some watch := watch then
    let _ ← onSyscall emu fun _ number args => do
      watch number args
      pure .default
  if let some handler := handler then
    let _ ← onSyscall emu handler
  let _ ← onSyscall emu fun emu number args => do
    if machine.architecture.call number == some .execve then handOver machine emu (← execute { machine with emu } emu args)
    else pure .default
  let _ ← serveKernelCalls machine
  let _ ← serveTaskCalls emu
  let _ ← serveRest machine
  if architecture == .x86_64 || architecture == .i686 then serveCpu emu machine.kernel architecture.bits
  emu.processHooks.modify ((fun parent child => machine.kernel.modify (·.fork parent child)) :: ·)
  pure machine

/-- A machine at the start of `path`, which is in `kernel`. Its first process has the standard descriptors, on a console, with
`input` to read. `watch` sees each system call before it is served, and then `handler`, which may serve it in place of the kernel. -/
def start (kernel : Kernel) (path : String) (arguments : List String) (environment : List String := [])
    (input : ByteArray := ByteArray.empty) (watch : Option (Nat → List Nat → IO Unit) := none)
    (handler : Option SyscallHandler := none) : IO Machine := do
  let data ← IO.ofExcept ((fileOf kernel path).mapError fun errno => s!"{path}: error {errno}")
  let program ← IO.ofExcept (Elf.parse data)
  let some architecture := Architecture.ofElf program.machine program.bits program.big program.flags
    | throw <| IO.userError s!"{path}: no Linux machine for ELF machine {program.machine} of {program.bits} bits"
  let interpreter ← match program.interpreter with
    | none => pure none
    | some name =>
      let bytes ← IO.ofExcept ((fileOf kernel name).mapError fun errno => s!"{name}: error {errno}")
      pure (some (bytes, ← IO.ofExcept (Elf.parse bytes)))
  -- A real program runs more code than the working set of a few thousand blocks that the default is for, and past it, each one
  -- would be lifted each time it runs. Most of its code runs at its start, a few times, and compiling that takes longer than
  -- running it: with this threshold, `ls` takes a third of the time, and a long loop no longer.
  let emu ← emulatorOf architecture
  let top ← loadProgram emu architecture path data program interpreter arguments environment
  let first := (← currentTask emu).group
  let kernel := kernel.withConsole first input
  let kernel := kernel.setProcess first { kernel.process first with
    breakStart := top, breakEnd := top, command := if arguments.isEmpty then [path] else arguments, environment, program := path }
  let kernel := Proc.install kernel
  machineOf architecture emu kernel watch handler

/-- Runs it until nothing can run, with what it writes to the console going to `output` as it comes. -/
def Machine.run (machine : Machine) (output : ByteArray → IO Unit) (quantum : Nat := 100000) (fuel : Nat := 1000000000) :
    IO ScheduleOutcome := do
  -- What it writes in a turn goes out when the turn ends, so that a long turn is what holds it up.
  let rec go : Nat → Nat → IO ScheduleOutcome
    | 0, _ => pure .outOfFuel
    | rounds + 1, left => do
      let turn := min left (64 * quantum)
      let outcome ← runProcesses machine.emu quantum turn
      let (kernel, written) := (← machine.kernel.get).takeOutput
      machine.kernel.set kernel
      if written.size > 0 then output written
      match outcome with
      | .outOfFuel => if left ≤ turn then pure .outOfFuel else go rounds (left - turn)
      | other => pure other
  go (fuel + 1) fuel

/-- What is in the kernel and in the emulator at once, to go back to: it is all a value. -/
structure Machine.Saved where
  emulator : Snapshot
  kernel : Kernel

def Machine.save (machine : Machine) : IO Machine.Saved := do
  pure { emulator := ← snapshot machine.emu, kernel := ← machine.kernel.get }

def Machine.restore (machine : Machine) (saved : Machine.Saved) : IO Unit := do
  Bap.Emu.restore machine.emu saved.emulator
  machine.kernel.set saved.kernel

private def checkpointMagic : ByteArray := "BAPLINUX".toUTF8

/-- All that a machine is, as bytes: its architecture, its kernel with the files in it, and its emulator. What is compiled isn't in
them, and is compiled again as it runs. -/
def Machine.checkpoint (machine : Machine) : IO ByteArray := do
  let (number, bits, big, flags) := machine.architecture.elf
  let header := Wire.putNat (Wire.putNat (Wire.putNat (Wire.putNat checkpointMagic number) bits) (if big then 1 else 0)) flags
  pure (Image.encode header (← machine.kernel.get).image ++ (← checkpointBytes machine.emu))

/-- A new machine where a checkpoint was, which goes on as that one would. This is all it takes: nothing has to be running, or
even to be on the host, but what the bytes hold. A turn of a thread that a run stopped in starts again. `watch` is as in `start`.
So is `handler`, as neither is a thing that can be in a file. What `Kernel.addGenerated` put in has its functions given again, by the normal paths that they were put in at, as a function can't be
in a file: a file without its function gives `EIO` when it is opened. -/
def Machine.ofCheckpoint (data : ByteArray) (watch : Option (Nat → List Nat → IO Unit) := none)
    (generators : List (String × Generator) := []) (handler : Option SyscallHandler := none) : IO Machine := do
  if data.extract 0 checkpointMagic.size != checkpointMagic then
    throw <| IO.userError "not a checkpoint of a Linux machine"
  let (number, at_) ← IO.ofExcept (Wire.getNat data checkpointMagic.size)
  let (bits, at_) ← IO.ofExcept (Wire.getNat data at_)
  let (big, at_) ← IO.ofExcept (Wire.getNat data at_)
  let (flags, at_) ← IO.ofExcept (Wire.getNat data at_)
  let some architecture := Architecture.ofElf number bits (big == 1) flags
    | throw <| IO.userError s!"a checkpoint of ELF machine {number}, which isn't one here"
  let (image, at_) ← IO.ofExcept (Image.decode data at_)
  let kernel ← IO.ofExcept image.kernel
  let kernel := { kernel with generators := generators.foldl (fun table entry => table.insert entry.1 entry.2) {} }
  let emu ← emulatorOf architecture
  Bap.Emu.restore emu (← snapshotOfBytes emu (data.extract at_ data.size))
  machineOf architecture emu kernel watch handler

def Machine.saveFile (machine : Machine) (path : System.FilePath) : IO Unit := do
  IO.FS.writeBinFile path (← machine.checkpoint)

def Machine.loadFile (path : System.FilePath) (watch : Option (Nat → List Nat → IO Unit) := none)
    (generators : List (String × Generator) := []) (handler : Option SyscallHandler := none) : IO Machine := do
  Machine.ofCheckpoint (← IO.FS.readBinFile path) watch generators handler

/-- A file of the host for a kernel, before a run: this is the only way that anything gets from there to in here. -/
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
