import Bap.Target.LLVMLift

namespace Bap.Target.PowerPC

open LLVMLift (PowerPCVariant)

private def decodeWith (variant : PowerPCVariant) (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodePowerPCOf variant globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith {} (← LLVMLift.powerpcEnvironment) base address data

/-- The decoder of a variant of PowerPC. -/
def disassembler (base : Nat := 0) (variant : PowerPCVariant := {}) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.powerpcEnvironmentOf variant
  pure { name := s!"{variant.triple}-llvm-primus", decode := decodeWith variant globals base }

end Bap.Target.PowerPC
