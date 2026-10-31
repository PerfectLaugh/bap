import Bap.Disasm.Basic

namespace Bap.Disasm.Recursive

/-- The error of a scan that stopped with reachable addresses left to decode. -/
def outOfFuel : String := "recursive disassembly ran out of fuel with addresses left to decode"

/-- The instructions with one more, unless an instruction of that address is already listed. -/
def addInsn (insn : Insn) (instructions : List Insn) : List Insn :=
  if instructions.any (·.address == insn.address) then instructions else instructions ++ [insn]

/-- The edges of an instruction. A delayed transfer goes through its slot, so the slot is followed
by the successors of the branch and not by its own fall-through. -/
def flowEdges (disassembler : Disassembler) (insn : Insn) : List (Nat × Nat) :=
  if disassembler.hasDelaySlot insn then
    (insn.address, insn.next) :: insn.successors.map (insn.next, ·)
  else
    insn.successors.map (insn.address, ·)

/-- Decodes the delay slot of a branch: the slot is listed but its own successors are not followed.
If something else reaches the slot address, the scan visits it as usual. -/
private def decodeSlot (disassembler : Disassembler) (data : ByteArray) (slot : Nat)
    (instructions : List Insn) (errors : List String) : IO (List Insn × List String) := do
  match ← disassembler.decode slot data with
  | .error error => pure (instructions, errors ++ [error])
  | .ok insn =>
    if insn.address != slot || insn.size = 0 then
      pure (instructions, errors ++ ["decoder returned an inconsistent instruction"])
    else
      pure (addInsn insn instructions, errors)

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
          let instructions := addInsn insn instructions
          let edges := edges ++ flowEdges disassembler insn
          let work := insn.successors ++ work
          if disassembler.hasDelaySlot insn then
            let (instructions, errors) ← decodeSlot disassembler data insn.next instructions errors
            scanAux disassembler data fuel work (address :: visited) instructions edges errors
          else
            scanAux disassembler data fuel work (address :: visited) instructions edges errors

/-- Every instruction starts at a byte of `data` and adds at most two addresses, some possibly out
of range, so a decoder that fails out of range visits no more than `3 * data.size + 1` addresses. -/
def scan (disassembler : Disassembler) (data : ByteArray) (entry : Nat) : IO Disasm := do
  let (instructions, edges, errors) ←
    scanAux disassembler data (3 * data.size + 1) [entry] [] [] [] []
  pure { entry := entry, instructions := instructions, edges := edges, errors := errors }

end Bap.Disasm.Recursive
