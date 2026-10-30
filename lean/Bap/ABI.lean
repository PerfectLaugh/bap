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
}

private def x86_64 : Convention := {
  wordSize := 64
  functionArguments := regs 64 ["RDI", "RSI", "RDX", "RCX", "R8", "R9"]
  result := reg "RAX" 64
  syscallNumber := reg "RAX" 64
  syscallArguments := regs 64 ["RDI", "RSI", "RDX", "R10", "R8", "R9"]
  stackPointer := reg "RSP" 64
  returnAddress := none
}

private def riscv (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "X" width 10 17
  result := reg "X10" width
  syscallNumber := reg "X17" width
  syscallArguments := numbered "X" width 10 15
  stackPointer := reg "X2" width
  returnAddress := some (reg "X1" width)
}

private def aarch64 : Convention := {
  wordSize := 64
  functionArguments := numbered "X" 64 0 7
  result := reg "X0" 64
  syscallNumber := reg "X8" 64
  syscallArguments := numbered "X" 64 0 5
  stackPointer := reg "SP" 64
  returnAddress := some (reg "X30" 64)
}

/-- o32 passes four arguments in registers, n32 and n64 pass eight. -/
private def mips (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "R" width 4 (if width = 32 then 7 else 11)
  result := reg "R2" width
  syscallNumber := reg "R2" width
  syscallArguments := numbered "R" width 4 9
  stackPointer := reg "R29" width
  returnAddress := some (reg "R31" width)
}

private def arm : Convention := {
  wordSize := 32
  functionArguments := numbered "R" 32 0 3
  result := reg "R0" 32
  syscallNumber := reg "R7" 32
  syscallArguments := numbered "R" 32 0 5
  stackPointer := reg "SP" 32
  returnAddress := some (reg "LR" 32)
}

private def powerpc (width : Nat) : Convention := {
  wordSize := width
  functionArguments := numbered "R" width 3 10
  result := reg "R3" width
  syscallNumber := reg "R0" width
  syscallArguments := numbered "R" width 3 8
  stackPointer := reg "R1" width
  returnAddress := some (reg "LR" width)
}

private def systemz : Convention := {
  wordSize := 64
  functionArguments := numbered "R" 64 2 6
  result := reg "R2" 64
  syscallNumber := reg "R1" 64
  syscallArguments := numbered "R" 64 2 7
  stackPointer := reg "R15" 64
  returnAddress := some (reg "R14" 64)
}

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
  | none => .stack ((index - abi.functionArguments.length) * (abi.wordSize / 8))

def alignStack (alignment : Nat) (address : Nat) : Nat :=
  if alignment = 0 then address else address / alignment * alignment

end Bap.ABI
