import Bap.Target.MIPS

namespace Bap.Target.MIPS32

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeMIPS32With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.mips32Environment) base address data

/-- The decoder of big-endian MIPS32. -/
def disassembler (base : Nat := 0) : IO Disasm.Disassembler :=
  MIPS.disassembler base { bits := 32 }

end Bap.Target.MIPS32
