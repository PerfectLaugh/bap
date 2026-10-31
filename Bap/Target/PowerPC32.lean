import Bap.Target.PowerPC

namespace Bap.Target.PowerPC32

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodePowerPC32With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.powerpc32Environment) base address data

/-- The decoder of big-endian PowerPC32. -/
def disassembler (base : Nat := 0) : IO Disasm.Disassembler :=
  PowerPC.disassembler base { bits := 32, endian := .big }

end Bap.Target.PowerPC32
