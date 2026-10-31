import Bap.Emu.Tasks
import Bap.Image.Loader

/-! Running a static Linux executable: what the kernel does to start one, and the system calls that libc needs besides those
of tasks. x86-64 only, and only what a program needs to start, run threads and print. -/

namespace Bap.Emu

open Bap.Tasks

private def var64 (name : String) : Bap.Var := ⟨name, .imm 64, 0, false⟩
private def bits (width value : Nat) : Bap.Value := .bits (BitVec.ofNat width value)
private def word64 (value : Nat) : ByteArray :=
  ByteArray.mk ((List.range 8).map fun index => (value >>> (8 * index)).toUInt8).toArray

/-- Registers hold zeros at the start, as the kernel leaves them, but for the state of the floating point units. -/
private def resetRegisters (emu : Emu) : IO Unit := do
  for name in ["RAX", "RBX", "RCX", "RDX", "RSI", "RDI", "RBP", "RSP", "R8", "R9", "R10", "R11", "R12", "R13", "R14", "R15",
      "FS_BASE", "GS_BASE"] do
    setReg emu (var64 name) (bits 64 0)
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

/-- The segments in pages, as the kernel maps them: each page has the bytes of what is in it. -/
private def mapSegments (emu : Emu) (image : Image.Image) : IO Unit := do
  let sorted := (image.memory.entries.map (·.1)).toArray.qsort fun left right => left.addr < right.addr
  let mut mappedTo := 0
  for region in sorted do
    let start := max mappedTo (region.addr / 4096 * 4096)
    let stop := (region.addr + region.data.size + 4095) / 4096 * 4096
    let bytes := (List.range (stop - start)).toArray.map fun offset =>
      let address := start + offset
      if region.addr ≤ address && address < region.addr + region.data.size then region.data[address - region.addr]!
      else (0 : UInt8)
    map emu ⟨start, ByteArray.mk bytes, ⟨true, region.writable, region.executable⟩⟩
    mappedTo := stop

private def stackTop : Nat := 0x7ff000000000
private def stackSize : Nat := 0x100000
private def breakStart : Nat := 0x20000000
private def breakSize : Nat := 0x1000000

/-- The stack that the kernel hands over: the arguments, nothing in the environment, and the auxiliary vector. -/
private def mapStack (emu : Emu) (image : Image.Image) : IO Unit := do
  map emu ⟨stackTop - stackSize, ByteArray.mk (Array.replicate stackSize 0), ⟨true, true, false⟩⟩
  let base := image.segments.foldl (fun lowest segment => min lowest segment.addr) (2 ^ 63)
  let header (offset size : Nat) : Nat :=
    (List.range size).foldl (fun value index => value + image.data[offset + index]!.toNat * 256 ^ index) 0
  let name := stackTop - 0x200
  let random := stackTop - 0x100
  -- AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_ENTRY, the ids of root, AT_SECURE, AT_RANDOM and the end
  let auxiliary := [(3, base + header 32 8), (4, 56), (5, header 56 2), (6, 4096), (9, image.entryPoint), (11, 0), (12, 0),
    (13, 0), (14, 0), (23, 0), (25, random), (0, 0)]
  let pointer := stackTop - 0x4000
  let cells := [1, name, 0, 0] ++ auxiliary.flatMap fun entry => [entry.1, entry.2]
  for (cell, index) in cells.zipIdx do
    write emu (pointer + 8 * index) (word64 cell)
  write emu name "a.out\x00".toUTF8
  setReg emu (var64 "RSP") (bits 64 pointer)

/-- A plain x86-64: nothing beyond SSE2, so that libc picks its plain routines. -/
private def serveCpuid (emu : Emu) : IO HookId :=
  onIntrinsic emu "cpuid" fun current _ => do
    let leaf := match Value.asBits (← reg current (var64 "RAX")) with
      | .ok value => value.2.toNat % 2 ^ 32
      | .error _ => 0
    let (a, b, c, d) : Nat × Nat × Nat × Nat := match leaf with
      -- GenuineIntel
      | 0 => (1, 0x756e6547, 0x6c65746e, 0x49656e69)
      | 1 => (0x6f0, 0, 0, 0x07888f9f)
      | _ => (0, 0, 0, 0)
    setReg current ⟨"intrinsic:y0", .imm 128, 0, false⟩ (bits 128 (a + b * 2 ^ 32 + c * 2 ^ 64 + d * 2 ^ 96))
    pure .proceed

/-- What libc needs besides the calls of tasks: the program break, writing out, its limits and random bytes. All else says
it isn't there, which libc copes with where it can. -/
private def serveLibcCalls (emu : Emu) (output : ByteArray → IO Unit) : IO HookId := do
  let current ← IO.mkRef breakStart
  map emu ⟨breakStart, ByteArray.mk (Array.replicate breakSize 0), ⟨true, true, false⟩⟩
  onSyscall emu fun guest number args => do
    let arg (index : Nat) : Nat := args.getD index 0
    let writes (descriptor : Nat) (data : ByteArray) : IO Unit := do
      if descriptor == 1 || descriptor == 2 then output data
    match number with
    | 12 =>
      if breakStart ≤ arg 0 && arg 0 < breakStart + breakSize then current.set (arg 0)
      pure (.returnValue (← current.get))
    | 1 =>
      writes (arg 0) (← read guest (arg 1) (arg 2))
      pure (.returnValue (arg 2))
    | 20 =>
      let mut total := 0
      for index in List.range (arg 2) do
        let entry ← read guest (arg 1 + 16 * index) 16
        let field (offset : Nat) : Nat := (List.range 8).foldl (fun value at_ => value + entry[offset + at_]!.toNat * 256 ^ at_) 0
        writes (arg 0) (← read guest (field 0) (field 8))
        total := total + field 8
      pure (.returnValue total)
    | 302 =>
      if arg 3 != 0 then
        write guest (arg 3) (word64 (8 * 1024 * 1024))
        write guest (arg 3 + 8) (word64 (2 ^ 64 - 1))
      pure (.returnValue 0)
    | 318 =>
      write guest (arg 0) (ByteArray.mk (Array.replicate (arg 1) 7))
      pure (.returnValue (arg 1))
    | 267 => pure (.returnValue (2 ^ 64 - 38))
    | _ => pure .default

/-- Runs a static x86-64 Linux executable to its end, with what it writes going to `output`. -/
def runExecutable (path : String) (output : ByteArray → IO Unit) (quantum : Nat := 100000) (fuel : Nat := 100000000) :
    IO ScheduleOutcome := do
  let image ← Image.load path
  if image.arch != .x86_64 then
    throw <| IO.userError s!"{path} isn't for x86-64"
  let emu ← x86_64 (ByteArray.mk (Array.replicate 16 0x90)) 0x10000 image.entryPoint
  mapSegments emu image
  resetRegisters emu
  mapStack emu image
  let _ ← serveTaskCalls emu
  let _ ← serveLibcCalls emu output
  let _ ← serveCpuid emu
  runProcesses emu quantum fuel

end Bap.Emu
