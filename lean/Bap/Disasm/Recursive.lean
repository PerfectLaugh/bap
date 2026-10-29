import Bap.Disasm.Basic

namespace Bap.Disasm.Recursive

private def scanAux (disassembler : Disassembler) (data : ByteArray) :
    Nat → List Nat → List Nat → List Insn → List (Nat × Nat) → List String →
      IO (List Insn × List (Nat × Nat) × List String)
  | 0, _, _, instructions, edges, errors => pure (instructions, edges, errors)
  | _fuel + 1, [], _, instructions, edges, errors => pure (instructions, edges, errors)
  | fuel + 1, address :: work, visited, instructions, edges, errors =>
    if address ∈ visited then
      scanAux disassembler data fuel work visited instructions edges errors
    else do
      match ← disassembler.decode address data with
      | .error error =>
        scanAux disassembler data fuel work (address :: visited) instructions edges (errors ++ [error])
      | .ok insn =>
        if insn.address != address || insn.size = 0 then
          scanAux disassembler data fuel work (address :: visited) instructions edges
            (errors ++ ["decoder returned an inconsistent instruction"])
        else
          let successors := insn.successors
          let edges := edges ++ successors.map (address, ·)
          scanAux disassembler data fuel (successors ++ work) (address :: visited)
            (instructions ++ [insn]) edges errors

def scan (disassembler : Disassembler) (data : ByteArray) (entry : Nat) : IO Disasm := do
  let (instructions, edges, errors) ← scanAux disassembler data (data.size + 1) [entry] [] [] [] []
  pure { entry := entry, instructions := instructions, edges := edges, errors := errors }

end Bap.Disasm.Recursive
