import Bap.Target.LLVMLift

namespace Bap.Target.MIPS

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeMIPSWith globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.mipsEnvironment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.mipsEnvironment
  pure {
    name := "mips64-llvm-primus"
    decode := decodeWith globals base
    hasDelaySlot := LLVMLift.mipsHasDelaySlot
    annulsSlot := LLVMLift.mipsAnnulsSlot }

end Bap.Target.MIPS
