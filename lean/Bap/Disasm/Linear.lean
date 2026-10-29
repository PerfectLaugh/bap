import Bap.Disasm.Basic

namespace Bap.Disasm.Linear

private def sweepAux (disassembler : Disassembler) (data : ByteArray) (entry : Nat) :
    Nat → Nat → List Insn → List String → IO (List Insn × List String)
  | 0, _, instructions, errors => pure (instructions, errors)
  | fuel + 1, offset, instructions, errors =>
    if offset ≥ data.size then
      pure (instructions, errors)
    else do
      match ← disassembler.decode (entry + offset) data with
      | .error error => pure (instructions, errors ++ [error])
      | .ok insn =>
        if insn.size = 0 then
          pure (instructions, errors ++ ["decoder produced a zero-sized instruction"])
        else
          sweepAux disassembler data entry fuel (offset + insn.size) (instructions ++ [insn]) errors

def sweep (disassembler : Disassembler) (data : ByteArray) (entry : Nat := 0) : IO Disasm := do
  let (instructions, errors) ← sweepAux disassembler data entry (data.size + 1) 0 [] []
  pure { entry := entry, instructions := instructions, errors := errors }

end Bap.Disasm.Linear
