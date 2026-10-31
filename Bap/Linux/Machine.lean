import Bap.Emu.Tasks
import Bap.Linux.Kernel
import Bap.Linux.Elf

/-! # A Linux machine

The virtual kernel of `Bap.Linux.Kernel` behind the system calls of the emulator, and what the kernel does to start a program:
its segments, and those of the interpreter that it asks for, in pages, and the stack that it starts on. No request ever
reaches the machine that this runs on: a program has what was put in its kernel. x86-64 only. -/

namespace Bap.Linux

open Bap.Emu
open Bap.Tasks (ScheduleOutcome)

private def word (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def bits (width value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)

structure Machine where
  emu : Emu
  kernel : IO.Ref Kernel

/-- A signed word of an argument, as whether it is negative and how far from zero it is. -/
private def signed (value : Nat) : Bool × Nat :=
  if value ≥ 2 ^ 63 then (true, 2 ^ 64 - value) else (false, value)

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
        map machine.emu ⟨mappedTo, ByteArray.mk (Array.replicate (needed - mappedTo) 0), ⟨true, true, false⟩⟩
      machine.kernel.set (kernel.setProcess group { process with breakEnd := wanted })
      pure (.returnValue wanted)
    catch _ => pure (.returnValue process.breakEnd)

private def base (machine : Machine) (group directory : Nat) : IO (Result String) := do
  pure ((← machine.kernel.get).baseOf group directory (atCwd directory))

/-- The system calls of files, memory that files are mapped into, time and what a process asks of itself. -/
private def kernelCall (machine : Machine) (emu : Emu) (number : Nat) (args : List Nat) : IO SyscallAction := do
    let machine : Machine := { machine with emu }
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
      at_ directory address fun from_ path => applyNat machine (·.openPath group from_ path flags mode)
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
        | .ok value => returning emu out (Abi.stat value)
    let clock (out scale : Nat) : IO SyscallAction := do
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu out (Abi.time now scale)
    let vectors (fd address count : Nat) (action : Nat → Nat → Nat → IO SyscallAction) : IO SyscallAction := do
      let mut total := 0
      for index in List.range count do
        let entry ← read emu (address + 16 * index) 16
        let field (offset : Nat) : Nat := (List.range 8).foldl (fun value at__ => value + entry[offset + at__]!.toNat * 256 ^ at__) 0
        match ← action fd (field 0) (field 8) with
        | .returnValue value =>
          if value ≥ 2 ^ 63 then
            return if total > 0 then .returnValue total else .returnValue value
          total := total + value
          if value < field 8 then return .returnValue total
        | other => return other
      pure (.returnValue total)
    match number with
    | 0 => readInto (arg 0) (arg 1) (arg 2)
    | 1 => writeOut (arg 0) (arg 1) (arg 2)
    | 2 => openAt here (arg 0) (arg 1) (arg 2)
    | 257 => openAt (arg 0) (arg 1) (arg 2) (arg 3)
    | 3 => apply machine (·.close group (arg 0))
    | 4 => statAt here (arg 0) (arg 1) true
    | 6 => statAt here (arg 0) (arg 1) false
    | 5 =>
      match kernel.statDescriptor group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok value => returning emu (arg 1) (Abi.stat value)
    | 262 =>
      -- AT_EMPTY_PATH says that the descriptor is what it is about.
      let path ← (readString emu (arg 1)).toBaseIO
      match path with
      | .ok "" =>
        if arg 3 &&& 0x1000 != 0 then
          match kernel.statDescriptor group (arg 0) with
          | .error errno => pure (errorOf errno)
          | .ok value => returning emu (arg 2) (Abi.stat value)
        else pure (errorOf Errno.enoent)
      | _ => statAt (arg 0) (arg 1) (arg 2) (arg 3 &&& 0x100 == 0)
    | 332 =>
      let path ← (readString emu (arg 1)).toBaseIO
      let finish (result : Result Kernel.Stat) : IO SyscallAction :=
        match result with
        | .error errno => pure (errorOf errno)
        | .ok value => returning emu (arg 4) (Abi.statx value)
      match path with
      | .ok "" =>
        if arg 2 &&& 0x1000 != 0 then finish (kernel.statDescriptor group (arg 0))
        else pure (errorOf Errno.enoent)
      | _ =>
        at_ (arg 0) (arg 1) fun from_ text => finish (kernel.statPath from_ text (arg 2 &&& 0x100 == 0))
    | 8 =>
      let (negative, distance) := signed (arg 1)
      applyNat machine (·.seek group (arg 0) negative distance (arg 2))
    | 17 =>
      match kernel.readFrom group (arg 0) (arg 2) (arg 3) with
      | .error errno => pure (errorOf errno)
      | .ok bytes => returning emu (arg 1) bytes bytes.size
    | 18 =>
      match ← (read emu (arg 1) (arg 2)).toBaseIO with
      | .error _ => pure (errorOf Errno.efault)
      | .ok bytes => applyNat machine (·.writeTo group (arg 0) bytes (arg 3))
    | 19 => vectors (arg 0) (arg 1) (arg 2) readInto
    | 20 => vectors (arg 0) (arg 1) (arg 2) writeOut
    | 21 => accessAt here (arg 0)
    | 269 | 439 => accessAt (arg 0) (arg 1)
    | 32 => applyNat machine (·.dup group (arg 0))
    | 33 => applyNat machine (·.dupTo group (arg 0) (arg 1))
    | 292 =>
      if arg 0 == arg 1 then pure (errorOf Errno.einval)
      else applyNat machine (·.dupTo group (arg 0) (arg 1) (arg 2 &&& Kernel.oCloexec != 0))
    | 72 =>
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
          | .ok value => .returnValue value)
      | 4 => apply machine (·.setFlags group (arg 0) (arg 2))
      | _ => pure (errorOf Errno.einval)
    | 16 =>
      -- No descriptor is a terminal.
      pure (errorOf (match kernel.statDescriptor group (arg 0) with | .ok _ => Errno.enotty | .error errno => errno))
    | 217 =>
      match kernel.directoryEntries group (arg 0) with
      | .error errno => pure (errorOf errno)
      | .ok (id, first, entries) =>
        let (bytes, count) := Abi.dirents entries first (arg 2)
        if count == 0 && !entries.isEmpty then
          pure (errorOf Errno.einval)
        else
          machine.kernel.set (kernel.advance id count)
          returning emu (arg 1) bytes bytes.size
    | 79 =>
      let text := (cwd ++ "\x00").toUTF8
      if text.size > arg 1 then pure (errorOf Errno.erange)
      else returning emu (arg 0) text text.size
    | 80 => at_ here (arg 0) fun _ path => apply machine (·.chdir group path)
    | 81 =>
      match kernel.directoryEntries group (arg 0), kernel.baseOf group (arg 0) false with
      | _, .ok path => apply machine (·.chdir group path)
      | .error errno, _ => pure (errorOf errno)
      | _, .error errno => pure (errorOf errno)
    | 83 => at_ here (arg 0) fun from_ path => apply machine (·.mkdir group from_ path (arg 1))
    | 258 => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.mkdir group from_ path (arg 2))
    | 84 => at_ here (arg 0) fun from_ path => apply machine (·.remove from_ path true)
    | 87 => at_ here (arg 0) fun from_ path => apply machine (·.remove from_ path false)
    | 263 => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.remove from_ path (arg 2 &&& 0x200 != 0))
    | 82 =>
      at_ here (arg 0) fun from_ source => do
        match ← (readString emu (arg 1)).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok target => apply machine (·.rename from_ source target)
    | 88 =>
      at_ here (arg 1) fun from_ path => do
        match ← (readString emu (arg 0)).toBaseIO with
        | .error _ => pure (errorOf Errno.efault)
        | .ok target => apply machine (·.symlink from_ target path)
    | 89 | 267 =>
      let (directory, address, out, room) := if number == 89 then (here, arg 0, arg 1, arg 2) else (arg 0, arg 1, arg 2, arg 3)
      at_ directory address fun from_ path =>
        match kernel.readlink from_ path with
        | .error errno => pure (errorOf errno)
        | .ok target =>
          let bytes := target.toUTF8
          let bytes := bytes.extract 0 room
          returning emu out bytes bytes.size
    | 90 => at_ here (arg 0) fun from_ path => apply machine (·.chmod from_ path (arg 1))
    | 268 => at_ (arg 0) (arg 1) fun from_ path => apply machine (·.chmod from_ path (arg 2))
    | 76 => at_ here (arg 0) fun from_ path => apply machine (·.truncatePath from_ path (arg 1))
    | 77 => apply machine (·.truncateDescriptor group (arg 0) (arg 1))
    | 74 | 75 => pure (.returnValue 0)
    | 91 | 92 | 93 | 94 | 260 | 280 => pure (.returnValue 0)
    | 95 =>
      let process := kernel.process group
      machine.kernel.set (kernel.setProcess group { process with umask := arg 0 &&& 0o777 })
      pure (.returnValue process.umask)
    | 9 =>
      if arg 3 &&& 0x20 != 0 then pure .default
      else serveFileMap machine group (arg 0) (arg 1) (arg 2) (arg 3) (arg 4) (arg 5)
    | 25 => pure (errorOf Errno.enomem)
    | 12 => serveBreak machine group (arg 0)
    | 96 => clock (arg 0) 1000
    | 201 =>
      let (next, now) := (← machine.kernel.get).tick
      machine.kernel.set next
      returning emu (arg 0) (Abi.bytesOf 8 (now / 1000000000)) (now / 1000000000)
    | 228 => clock (arg 1) 1
    | 229 => returning emu (arg 1) (Abi.time 1 1)
    | 35 | 230 => pure (.returnValue 0)
    | 63 => returning emu (arg 0) (Abi.utsname "bap")
    | 102 | 104 | 107 | 108 => pure (.returnValue 0)
    | 97 =>
      let stack := if arg 0 == 3 then 8 * 1024 * 1024 else 2 ^ 64 - 1
      returning emu (arg 1) (Abi.bytesOf 8 stack ++ Abi.bytesOf 8 (2 ^ 64 - 1))
    | 302 =>
      let stack := if arg 1 == 3 then 8 * 1024 * 1024 else 2 ^ 64 - 1
      returning emu (arg 3) (Abi.bytesOf 8 stack ++ Abi.bytesOf 8 (2 ^ 64 - 1))
    | 318 =>
      -- A fixed sequence, as a run is the same each time.
      let bytes := ByteArray.mk ((List.range (arg 1)).map fun index => (index * 167 + 13).toUInt8).toArray
      returning emu (arg 0) bytes (arg 1)
    | 131 => returning emu (arg 1) (ByteArray.mk (Array.replicate 24 0))
    | 204 => returning emu (arg 2) (ByteArray.mk #[1, 0, 0, 0, 0, 0, 0, 0]) 8
    -- What serveTaskCalls serves.
    | _ => pure .default

private def serveKernelCalls (machine : Machine) : IO HookId :=
  onSyscall machine.emu (kernelCall machine)

/-- What is left: nothing else serves it, and it isn't there. -/
private def serveRest (emu : Emu) : IO HookId :=
  onSyscall emu fun _ _ _ => pure (errorOf Errno.enosys)

/-- An x86-64 of level 2, which is what the libc of current distributions asks for: SSE4.2 and POPCNT, without AVX, so that
libc doesn't pick the routines that need it. -/
private def serveCpu (emu : Emu) : IO Unit := do
  let _ ← onIntrinsic emu "cpuid" fun current _ => do
    let leaf := match Value.asBits (← reg current (word "RAX")) with
      | .ok value => value.2.toNat % 2 ^ 32
      | .error _ => 0
    let (a, b, c, d) : Nat × Nat × Nat × Nat := match leaf with
      -- AuthenticAMD: libc reads the caches of an Intel from leaves that this doesn't have.
      | 0 => (1, 0x68747541, 0x444d4163, 0x69746e65)
      -- SSE3, SSSE3, CMPXCHG16B, SSE4.1, SSE4.2, POPCNT
      | 1 => (0x800f00, 0, 0x00982201, 0x07888f9f)
      | 0x80000000 => (0x80000001, 0, 0, 0)
      -- LAHF, and SYSCALL, NX and long mode
      | 0x80000001 => (0, 0, 1, 0x20100800)
      | _ => (0, 0, 0, 0)
    -- In the registers: what follows the intrinsic in its code doesn't run after a hook has served it.
    for (name, value) in [("RAX", a), ("RBX", b), ("RCX", c), ("RDX", d)] do
      setReg current (word name) (bits 64 value)
    pure .proceed
  -- What ld.so saves around resolving a function. The layout is that of the manual: the controls, MXCSR, ST and XMM. The rest of
  -- the x87 state, as what instruction faulted, isn't kept.
  let value (emu : Emu) (var : Bap.Var) : IO Nat := do
    match Value.asBits (← reg emu var) with
    | .ok bits => pure bits.2.toNat
    | .error _ => pure 0
  let target (emu : Emu) : IO Nat := value emu (word "intrinsic:x0")
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
    for index in List.range 16 do
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
    for index in List.range 16 do
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
  let counter ← IO.mkRef 1000000
  let _ ← onIntrinsic emu "rdtsc" fun current _ => do
    let now ← counter.get
    counter.set (now + 1000)
    setReg current (word "RAX") (bits 64 (now % 2 ^ 32))
    setReg current (word "RDX") (bits 64 (now / 2 ^ 32))
    pure .proceed
  pure ()

/-- Registers hold zeros at the start, as the kernel leaves them, but for the state of the floating point units. -/
private def resetRegisters (emu : Emu) : IO Unit := do
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

private def stackTop : Nat := 0x7ffffffff000
private def stackSize : Nat := 8 * 1024 * 1024
/-- Where a program goes that can go anywhere, and an interpreter. Those of Linux, without the randomness. -/
private def programBase : Nat := 0x555555554000
private def interpreterBase : Nat := 0x7ffff7fc0000

private def fileOf (kernel : Kernel) (path : String) : Result ByteArray := do
  let (_, found) ← kernel.resolve "/" path
  let some number := found | .error Errno.enoent
  match kernel.inodes.get? number with
  | some { content := .file data, .. } => .ok data
  | _ => .error Errno.einval

/-- The stack that the kernel hands over: where the arguments, the environment and the auxiliary vector are. -/
private def mapStack (emu : Emu) (arguments environment : List String) (auxiliary : List (Nat × Nat)) : IO Unit := do
  map emu ⟨stackTop - stackSize, ByteArray.mk (Array.replicate stackSize 0), ⟨true, true, false⟩⟩
  let mut cursor := stackTop - 16
  let place (cursor : Nat) (text : ByteArray) : IO Nat := do
    let at_ := cursor - text.size
    write emu at_ text
    pure at_
  cursor ← place cursor "x86_64\x00".toUTF8
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
  let pointer := (cursor - 8 * cells.length) / 16 * 16
  for (cell, index) in cells.zipIdx do
    write emu (pointer + 8 * index) (Abi.bytesOf 8 cell)
  setReg emu (word "RSP") (bits 64 pointer)

/-- A machine at the start of `path`, which is in `kernel`. Its first process has the standard descriptors, on a console, with
`input` to read. `watch` sees each system call before it is served. -/
def start (kernel : Kernel) (path : String) (arguments : List String) (environment : List String := [])
    (input : ByteArray := ByteArray.empty) (watch : Option (Nat → List Nat → IO Unit) := none) : IO Machine := do
  let data ← IO.ofExcept ((fileOf kernel path).mapError fun errno => s!"{path}: error {errno}")
  let program ← IO.ofExcept (Elf.parse data)
  let base := if program.relocatable then programBase else 0
  let interpreter ← match program.interpreter with
    | none => pure none
    | some name =>
      let bytes ← IO.ofExcept ((fileOf kernel name).mapError fun errno => s!"{name}: error {errno}")
      pure (some (bytes, ← IO.ofExcept (Elf.parse bytes)))
  -- A real program runs more code than the working set of a few thousand blocks that the default is for, and past it, each one
  -- would be lifted each time it runs. Most of its code runs at its start, a few times, and compiling that takes longer than
  -- running it: with this threshold, `ls` takes a third of the time, and a long loop no longer.
  let emu ← x86_64 (ByteArray.mk (Array.replicate 16 0x90)) 0x1000 0 fun config =>
    { config with cacheLimit := 1048576, hotThreshold := 1024 }
  unmap emu 0x1000 16
  resetRegisters emu
  let top ← mapProgram emu data program base
  let lowest := program.segments.foldl (fun lowest segment => min lowest segment.address) (2 ^ 63)
  let entry ← match interpreter with
    | some (bytes, loaded) =>
      let _ ← mapProgram emu bytes loaded interpreterBase
      pure (interpreterBase + loaded.entry)
    | none => pure (base + program.entry)
  -- AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_BASE, AT_FLAGS, AT_ENTRY, the ids of root, AT_HWCAP, AT_CLKTCK, AT_SECURE
  let auxiliary := [(3, base + lowest + program.headerOffset), (4, 56), (5, program.headerCount), (6, 4096),
    (7, if interpreter.isSome then interpreterBase else 0), (8, 0), (9, base + program.entry), (11, 0), (12, 0), (13, 0), (14, 0),
    (16, 0x07888f9f), (17, 100), (23, 0)]
  mapStack emu (if arguments.isEmpty then [path] else arguments) environment auxiliary
  setPc emu entry
  let first := (← currentTask emu).group
  let kernel := kernel.withConsole first input
  let kernel := kernel.setProcess first { kernel.process first with breakStart := top, breakEnd := top }
  let machine : Machine := { emu, kernel := ← IO.mkRef kernel }
  if let some watch := watch then
    let _ ← onSyscall emu fun _ number args => do
      watch number args
      pure .default
  let _ ← serveKernelCalls machine
  let _ ← serveTaskCalls emu
  let _ ← serveRest emu
  serveCpu emu
  emu.processHooks.modify ((fun parent child => machine.kernel.modify (·.fork parent child)) :: ·)
  pure machine

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
the directories that libraries are in, with the links of their paths resolved to files. -/
def Kernel.copyProgramFromHost (kernel : Kernel) (path : String) : IO Kernel := do
  let directories := ["/lib64", "/usr/lib64", "/lib/x86_64-linux-gnu", "/usr/lib/x86_64-linux-gnu", "/lib", "/usr/lib"]
  let copy (kernel : Kernel) (target : String) : IO (Kernel × ByteArray) := do
    let data ← IO.FS.readBinFile target
    pure (kernel.addFile target data, data)
  let (kernel, data) ← copy kernel path
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
        let found ← directories.findM? fun directory => System.FilePath.pathExists (directory ++ "/" ++ name)
        if let some directory := found then
          let (next, bytes) ← copy kernel (directory ++ "/" ++ name)
          kernel := next
          pending := pending ++ Elf.needed bytes
  pure kernel

end Bap.Linux
