import Bap.Linux.Kernel
import Bap.Linux.Elf

/-! What the virtual kernel says of itself. That it can't reach the machine it runs on needs no theorem: its operations are pure
functions of its state, which their types say. -/

namespace Bap.Linux

open Kernel

@[simp] private theorem process_setProcess_same (kernel : Kernel) (group : Nat) (value : Process) :
    (kernel.setProcess group value).process group = value := by
  simp [Kernel.process, Kernel.setProcess]

private theorem process_setProcess_other (kernel : Kernel) {group other : Nat} (value : Process) (h : group ≠ other) :
    (kernel.setProcess group value).process other = kernel.process other := by
  simp [Kernel.process, Kernel.setProcess, Std.HashMap.getD_insert, h]

/-- A descriptor that was closed is gone, so nothing can read it. -/
theorem read_after_close {kernel next : Kernel} {group fd : Nat} (h : kernel.close group fd = .ok next) (count : Nat) :
    next.read group fd count = .error Errno.ebadf := by
  simp only [Kernel.close] at h
  by_cases hopen : (kernel.process group).descriptors.contains fd = true
  · simp only [hopen, Bool.not_true, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq] at h
    subst h
    simp [Kernel.read, Kernel.openFileOf, bind, Except.bind]
  · simp [hopen, bind, Except.bind] at h

/-- A child starts with the descriptors, the directory and the break of its parent. -/
theorem fork_process (kernel : Kernel) (parent child : Nat) : (kernel.fork parent child).process child = kernel.process parent := by
  simp [Kernel.fork]

/-- What a child does to its own table leaves that of its parent alone. -/
theorem setProcess_isolated (kernel : Kernel) {child parent : Nat} (value : Process) (h : child ≠ parent) :
    (kernel.setProcess child value).process parent = kernel.process parent :=
  process_setProcess_other kernel value h

/-- Bytes of `Abi` have the size that they say. -/
@[simp] theorem bytesOf_size (size value : Nat) : (Abi.bytesOf size value).size = size := by
  simp [Abi.bytesOf, ByteArray.size]

/-- `struct stat` has its 144 bytes, whatever is in it. -/
theorem stat_size (value : Kernel.Stat) : (Abi.stat value).size = 144 := by
  simp [Abi.stat, ByteArray.size_append]

/-- `struct statx` has its 256 bytes, whatever is in it. -/
theorem statx_size (value : Kernel.Stat) : (Abi.statx value).size = 256 := by
  simp [Abi.statx, ByteArray.size_append]

/-- `struct timespec` has its 16 bytes. -/
theorem time_size (now scale : Nat) : (Abi.time now scale).size = 16 := by
  simp [Abi.time, ByteArray.size_append]

/-- A file has what was written where it was written, and no less than it had. -/
theorem writeAt_size (data : ByteArray) (offset : Nat) (bytes : ByteArray) (h : offset ≤ data.size) :
    (writeAt data offset bytes).size = max data.size (offset + bytes.size) := by
  have hnot : ¬ data.size < offset := by omega
  simp only [writeAt, hnot, ↓reduceIte, ByteArray.size_append, ByteArray.size_extract]
  omega

/-- What is not an ELF file doesn't start. -/
theorem parse_short (data : ByteArray) (h : data.size < 64) : ∃ error, Elf.parse data = .error error := by
  refine ⟨"not an ELF file", ?_⟩
  simp [Elf.parse, h, bind, Except.bind]

end Bap.Linux
