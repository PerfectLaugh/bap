import Bap.Target.LLVMLift

namespace Bap.Target.MIPS

open LLVMLift (MipsVariant)

private def decodeWith (variant : MipsVariant) (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeMIPSOf variant globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith {} (← LLVMLift.mipsEnvironment) base address data

/-- The decoder of a variant of MIPS. -/
def disassembler (base : Nat := 0) (variant : MipsVariant := {}) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.mipsEnvironmentOf variant
  pure {
    name := s!"{variant.triple}-llvm-primus"
    decode := decodeWith variant globals base
    hasDelaySlot := LLVMLift.mipsHasDelaySlot
    annulsSlot := LLVMLift.mipsAnnulsSlot }

end Bap.Target.MIPS
