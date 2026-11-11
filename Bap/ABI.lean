import Bap.Image.Basic

namespace Bap.ABI

structure Convention where
  wordSize : Nat
  functionArguments : List Bap.Var
  result : Bap.Var
  syscallNumber : Bap.Var
  syscallArguments : List Bap.Var
  stackPointer : Bap.Var
  returnAddress : Option Bap.Var
  /-- From the stack pointer on entry to the first argument in memory: what the caller reserves below them. -/
  stackArgumentsStart : Nat := 0
  /-- What it is the convention of, which says how arguments of floating point and of more than a word go. -/
  arch : Image.Arch := .unknown
  /-- The registers that arguments of floating point go in, in order. -/
  floatArguments : List Bap.Var := []
  deriving Repr

inductive Location where
  | register (var : Bap.Var)
  | stack (offset : Nat)
  deriving DecidableEq, Repr

private def reg (name : String) (width : Nat) : Bap.Var := ⟨name, .imm width, 0, false⟩
private def regs (width : Nat) (names : List String) : List Bap.Var := names.map (reg · width)
private def numbered (name : String) (width first last : Nat) : List Bap.Var :=
  (List.range (last - first + 1)).map fun index => reg s!"{name}{first + index}" width

private def x86 : Convention := {
  wordSize := 32
  functionArguments := []
  result := reg "EAX" 32
  syscallNumber := reg "EAX" 32
  syscallArguments := regs 32 ["EBX", "ECX", "EDX", "ESI", "EDI", "EBP"]
  stackPointer := reg "ESP" 32
  returnAddress := none
  -- Past the return address.
  stackArgumentsStart := 4
  arch := .x86
}

private def x86_64 : Convention := {
  wordSize := 64
  functionArguments := regs 64 ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
  result := reg "RAX" 64
  syscallNumber := reg "RAX" 64
  syscallArguments := regs 64 ["RDI", "RSI", "RDX", "R10", "R8", "R9"]
  stackPointer := reg "RSP" 64
  returnAddress := none
  -- Past the return address.
  stackArgumentsStart := 8
  arch := .x86_64
  floatArguments := numbered "ZMM" 512 0 7
}

private def riscv (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "X" width 10 17
  result := reg "X10" width
  syscallNumber := reg "X17" width
  syscallArguments := numbered "X" width 10 15
  stackPointer := reg "X2" width
  returnAddress := some (reg "X1" width)
  arch := .riscv
  -- Of the D extension, as Linux's LP64D and ILP32D have it.
  floatArguments := numbered "F" 64 10 17
}

private def aarch64 : Convention := {
  wordSize := 64
  functionArguments := numbered "X" 64 0 7
  result := reg "X0" 64
  syscallNumber := reg "X8" 64
  syscallArguments := numbered "X" 64 0 5
  stackPointer := reg "SP" 64
  returnAddress := some (reg "X30" 64)
  arch := .aarch64
  floatArguments := numbered "Q" 128 0 7
}

/-- o32 passes four arguments in registers, n32 and n64 pass eight. Under o32 the caller also reserves a home for each
register argument, so the first argument in memory is 16 bytes above the stack pointer, as in the psABI and in LLVM's
`GetCalleeAllocdArgSizeInBytes`. Upstream's `mips_abi.ml` starts them at 0, which is not where they are. -/
private def mips (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "R" width 4 (if width = 32 then 7 else 11)
  result := reg "R2" width
  syscallNumber := reg "R2" width
  -- Of o32, only four are in registers, and the rest are on the stack of the caller, as `syscall(2)` has it.
  syscallArguments := numbered "R" width 4 (if width = 32 then 7 else 9)
  stackPointer := reg "R29" width
  returnAddress := some (reg "R31" width)
  stackArgumentsStart := if width = 32 then 16 else 0
  arch := .mips
  -- Of o32, the first two, if they are of floating point; of n32 and n64, the one of each argument's place.
  floatArguments := if width = 32 then [reg "F12" 64, reg "F14" 64] else numbered "F" 64 12 19
}

private def arm : Convention := {
  wordSize := 32
  functionArguments := numbered "R" 32 0 3
  result := reg "R0" 32
  syscallNumber := reg "R7" 32
  syscallArguments := numbered "R" 32 0 5
  stackPointer := reg "SP" 32
  returnAddress := some (reg "LR" 32)
  arch := .arm
  -- Of the VFP variant, as Linux's EABI of hard floating point has it: `D0` to `D7`, of which a `float` is half.
  floatArguments := numbered "D" 64 0 7
}

private def powerpc (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "R" width 3 10
  result := reg "R3" width
  syscallNumber := reg "R0" width
  syscallArguments := numbered "R" width 3 8
  stackPointer := reg "R1" width
  returnAddress := some (reg "LR" width)
  -- Past the back chain and the word where the callee saves LR, of SysV; and of ELFv2, as musl has it of both orders, past the header
  -- of 32 bytes and the save area of the eight arguments in registers.
  stackArgumentsStart := if width = 32 then 8 else 96
  arch := .powerpc
  floatArguments := numbered "F" 64 1 (if width = 32 then 8 else 13)
}

private def systemz : Convention := {
  wordSize := 64
  functionArguments := numbered "R" 64 2 6
  result := reg "R2" 64
  syscallNumber := reg "R1" 64
  syscallArguments := numbered "R" 64 2 7
  stackPointer := reg "R15" 64
  returnAddress := some (reg "R14" 64)
  -- Past the save area of the registers.
  stackArgumentsStart := 160
  arch := .systemz
  floatArguments := regs 64 ["F0", "F2", "F4", "F6"]
}

/-- The first ABI of 64-bit PowerPC, ELFv1, as glibc has it of big-endian, whose arguments in memory are past a header of 48 bytes and
the save area of the eight in registers; `convention` has ELFv2, as musl has it of both orders. -/
def powerpc64ElfV1 : Convention := { powerpc 64 with stackArgumentsStart := 112 }

/-- The convention of an architecture: of 64-bit PowerPC, ELFv2. -/
def convention (arch : Image.Arch) (wordSize : Nat := 64) : Option Convention :=
  match arch with
  | .x86 => some x86
  | .x86_64 => some x86_64
  | .riscv => some (riscv wordSize)
  | .aarch64 => some aarch64
  | .mips => some (mips wordSize)
  | .arm => some arm
  | .powerpc => some (powerpc wordSize)
  | .systemz => some systemz
  | .unknown => none

def argumentLocation (abi : Convention) (index : Nat) : Location :=
  match abi.functionArguments[index]? with
  | some var => .register var
  | none => .stack (abi.stackArgumentsStart + (index - abi.functionArguments.length) * (abi.wordSize / 8))

def alignStack (alignment : Nat) (address : Nat) : Nat :=
  if alignment = 0 then address else address / alignment * alignment

end Bap.ABI
