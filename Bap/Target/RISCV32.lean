import Bap.Target.LLVMLift

namespace Bap.Target.RISCV32

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeRISCV32With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.riscv32Environment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.riscv32Environment
  pure { name := "riscv32-llvm-primus", decode := decodeWith globals base, sizeAt := LLVMLift.sizeAt "riscv32" base }

end Bap.Target.RISCV32
