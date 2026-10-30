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
      if start + size = address then (start, size + 1) :: rest else (address, 1) :: ranges
    | _ => (address, 1) :: ranges).reverse

def diff (emu : Emu) (saved : Snapshot) : IO (List (Nat × Nat)) := do
  refreshRegions emu
  let regions ← emu.regions.get
  let candidates := (saved.regions ++ regions).foldl (init := []) fun candidates region =>
    if candidates.any fun current => current.address = region.address then candidates else candidates ++ [region]
  let changes := candidates.foldl (init := []) fun changes region =>
    (List.range region.data.size).foldl (init := changes) fun changes offset =>
      let address := region.address + offset
      if byteAt regions address != byteAt saved.regions address then address :: changes else changes
  pure (coalesce changes)

def changedSince (emu : Emu) (path : String) : IO (List (Nat × Nat)) := do
  diff emu (← loadSnapshot emu path)

end Bap.Emu
