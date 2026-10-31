import Bap.Target.LLVMLift

namespace Bap.Target.Thumb

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeThumbWith globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.thumbEnvironment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.thumbEnvironment
  pure { name := "thumbv7-llvm-primus", decode := decodeWith globals base, sizeAt := LLVMLift.sizeAt "thumbv7" base }

end Bap.Target.Thumb
