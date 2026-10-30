import Bap.Disasm.Basic

namespace Bap.Disasm.Recursive

/-- The error of a scan that stopped with reachable addresses left to decode. -/
def outOfFuel : String := "recursive disassembly ran out of fuel with addresses left to decode"

/-- Fuel counts decoded addresses only: popping an address that was already visited is free. -/
private def scanAux (disassembler : Disassembler) (data : ByteArray) :
    Nat → List Nat → List Nat → List Insn → List (Nat × Nat) → List String →
      IO (List Insn × List (Nat × Nat) × List String)
  | 0, work, visited, instructions, edges, errors =>
    if work.all (· ∈ visited) then
      pure (instructions, edges, errors)
    else
      pure (instructions, edges, errors ++ [outOfFuel])
  | fuel + 1, work, visited, instructions, edges, errors =>
    match work.dropWhile (· ∈ visited) with
    | [] => pure (instructions, edges, errors)
    | address :: work => do
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

/-- Every instruction starts at a byte of `data` and adds at most two addresses, some possibly out
of range, so a decoder that fails out of range visits no more than `3 * data.size + 1` addresses. -/
def scan (disassembler : Disassembler) (data : ByteArray) (entry : Nat) : IO Disasm := do
  let (instructions, edges, errors) ←
    scanAux disassembler data (3 * data.size + 1) [entry] [] [] [] []
  pure { entry := entry, instructions := instructions, edges := edges, errors := errors }

end Bap.Disasm.Recursive
