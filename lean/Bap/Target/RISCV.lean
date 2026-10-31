import Bap.Target.LLVMLift

namespace Bap.Target.RISCV

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeRISCVWith globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.riscvEnvironment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.riscvEnvironment
  pure { name := "riscv64-llvm-primus", decode := decodeWith globals base, sizeAt := LLVMLift.sizeAt "riscv64" base }

end Bap.Target.RISCV
