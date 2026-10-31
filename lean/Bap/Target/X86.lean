import Bap.Target.LLVMLift

namespace Bap.Target.X86

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeX86With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.x86Environment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.x86Environment
  pure { name := "x86-llvm-primus", decode := decodeWith globals base, sizeAt := LLVMLift.sizeAt "x86_64" base }

end Bap.Target.X86
