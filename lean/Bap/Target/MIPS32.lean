import Bap.Target.LLVMLift

namespace Bap.Target.MIPS32

private def decodeWith (globals : Primus.Semantics.Environment) (base : Nat)
    (address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  try
    pure (.ok (← LLVMLift.decodeMIPS32With globals base address data))
  catch error =>
    pure (.error (toString error))

def decodeAt (base address : Nat) (data : ByteArray) : IO (Except String Disasm.Insn) := do
  decodeWith (← LLVMLift.mips32Environment) base address data

def disassembler (base : Nat := 0) : IO Disasm.Disassembler := do
  let globals ← LLVMLift.mips32Environment
  pure {
    name := "mips-llvm-primus"
    decode := decodeWith globals base
    hasDelaySlot := LLVMLift.mipsHasDelaySlot
    annulsSlot := LLVMLift.mipsAnnulsSlot }

end Bap.Target.MIPS32
