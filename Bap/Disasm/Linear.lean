import Bap.Disasm.Basic

namespace Bap.Disasm.Linear

private def sweepAux (disassembler : Disassembler) (data : ByteArray) (entry : Nat) :
    Nat → Nat → Array Insn → Array String → IO (Array Insn × Array String)
  | 0, _, instructions, errors => pure (instructions, errors)
  | fuel + 1, offset, instructions, errors =>
    if offset ≥ data.size then
      pure (instructions, errors)
    else do
      match ← disassembler.decode (entry + offset) data with
      | .error error => pure (instructions, errors.push error)
      | .ok insn =>
        if insn.size = 0 then
          pure (instructions, errors.push "decoder produced a zero-sized instruction")
        else
          sweepAux disassembler data entry fuel (offset + insn.size) (instructions.push insn) errors

def sweep (disassembler : Disassembler) (data : ByteArray) (entry : Nat := 0) : IO Disasm := do
  let (instructions, errors) ← sweepAux disassembler data entry (data.size + 1) 0 #[] #[]
  pure { entry := entry, instructions := instructions.toList, errors := errors.toList }

/-- What a tolerant sweep found at a place of the bytes, by its offset from their start: an instruction that decoded there, or bytes that
it went past, how many, and why nothing decoded there. -/
inductive Piece where
  | insn (offset : Nat) (insn : Insn)
  | skip (offset size : Nat) (error : String)
  deriving Repr

/-- Where a piece is and how many bytes it has. -/
def Piece.extent : Piece → Nat × Nat
  | .insn offset instruction => (offset, instruction.size)
  | .skip offset size _ => (offset, size)

/-- What a tolerant sweep found, in order: its pieces cover the bytes from the first to the last, each byte once, so that it says each
that it went past and never has two pieces at once. -/
structure Tolerant where
  entry : Nat
  pieces : List Piece
  deriving Repr

def Tolerant.instructions (tolerant : Tolerant) : List Insn :=
  tolerant.pieces.filterMap fun
    | .insn _ insn => some insn
    | .skip .. => none

/-- What it went past: where, how many bytes, and why. -/
def Tolerant.skipped (tolerant : Tolerant) : List (Nat × Nat × String) :=
  tolerant.pieces.filterMap fun | .skip offset size error => some (offset, size, error) | .insn .. => none

/-- How many bytes a tolerant sweep goes past where nothing decodes: `step`, but at least one and no more than there are. -/
def skipWidth (step size offset : Nat) : Nat := min (max step 1) (size - offset)

/-- The pieces from `offset` on, in front of those found before it, the last first. -/
private def tolerantAux (disassembler : Disassembler) (data : ByteArray) (entry step : Nat) :
    Nat → Nat → List Piece → IO (List Piece)
  | 0, _, pieces => pure pieces
  | fuel + 1, offset, pieces =>
    if offset ≥ data.size then pure pieces
    else
      disassembler.decode (entry + offset) data >>= fun result => match result with
      | .error error =>
        tolerantAux disassembler data entry step fuel (offset + skipWidth step data.size offset)
          (.skip offset (skipWidth step data.size offset) error :: pieces)
      | .ok insn =>
        if insn.size = 0 ∨ data.size < offset + insn.size then
          tolerantAux disassembler data entry step fuel (offset + skipWidth step data.size offset)
            (.skip offset (skipWidth step data.size offset)
              (if insn.size = 0 then "decoder produced a zero-sized instruction" else "an instruction past the end of the bytes") :: pieces)
        else
          tolerantAux disassembler data entry step fuel (offset + insn.size) (.insn offset insn :: pieces)

/-- A sweep that goes on where nothing decodes, past `step` bytes, and says so: what it gives covers the bytes, each once, by an instruction
that the decoder gave there or by bytes that it went past and why (`Bap.Proofs.Disasm.sweepTolerant_tiles`). -/
def sweepTolerant (disassembler : Disassembler) (data : ByteArray) (entry : Nat := 0) (step : Nat := 1) : IO Tolerant := do
  let pieces ← tolerantAux disassembler data entry step (data.size + 1) 0 []
  pure { entry, pieces := pieces.reverse }

end Bap.Disasm.Linear
