import Bap.Emu.Checkpoint

namespace Bap.Emu

private def byteAt (regions : List Region) (address : Nat) : Option UInt8 := do
  let region ← regions.find? fun region => region.contains address
  region.data[address - region.address]?

private def coalesce (changes : List Nat) : List (Nat × Nat) :=
  let sorted := changes.mergeSort (· ≤ ·)
  (sorted.foldl (init := []) fun ranges address =>
    match ranges with
    | (start, size) :: rest =>
      if start + size = address then (start, size + 1) :: rest
      else if start ≤ address && address < start + size then ranges
      else (address, 1) :: ranges
    | _ => (address, 1) :: ranges).reverse

/-- The address spans to compare: one per base address, as long as the longest region there. -/
def diffCandidates (regions : List Region) : List (Nat × Nat) :=
  regions.foldl (init := []) fun candidates region =>
    if candidates.any fun current => current.1 = region.address then
      candidates.map fun current =>
        if current.1 = region.address then (current.1, max current.2 region.data.size) else current
    else candidates ++ [(region.address, region.data.size)]

/-- Addresses whose byte differs between the two region tables, possibly repeated. -/
def changedAddresses (saved live : List Region) : List Nat :=
  (diffCandidates (saved ++ live)).foldl (init := []) fun changes candidate =>
    (List.range candidate.2).foldl (init := changes) fun changes offset =>
      let address := candidate.1 + offset
      if byteAt live address != byteAt saved address then address :: changes else changes

/-- Sorted `(start, size)` ranges of the bytes that differ between the two region tables. -/
def diffRanges (saved live : List Region) : List (Nat × Nat) :=
  coalesce (changedAddresses saved live)

def diff (emu : Emu) (saved : Snapshot) : IO (List (Nat × Nat)) := do
  refreshRegions emu
  pure (diffRanges saved.regions (← emu.regions.get))

def changedSince (emu : Emu) (path : String) : IO (List (Nat × Nat)) := do
  diff emu (← loadSnapshot emu path)

end Bap.Emu
