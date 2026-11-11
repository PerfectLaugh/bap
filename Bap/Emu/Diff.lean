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

/-- Ranges, sorted, with those that touch or overlap made one. -/
private def mergeRanges (ranges : List (Nat × Nat)) : List (Nat × Nat) :=
  let sorted := ranges.mergeSort fun left right => left.1 ≤ right.1
  (sorted.foldl (init := []) fun merged (start, size) =>
    match merged with
    | (first, length) :: rest =>
      if start ≤ first + length then (first, max length (start + size - first)) :: rest
      else (start, size) :: merged
    | [] => [(start, size)]).reverse

/-- `diffRanges`, which looks at each byte, of what is looked at less of: of a region that is where one is in the other, of the same size,
the pages of 4 KiB where either has other than zeros and they differ, as the pieces of native code give them, which takes what they have
rather than how large they are; and of a region that nothing of the other is anywhere in, all of it. The rest is as `diffRanges` has it. -/
def diffRangesFast (saved live : List Region) : List (Nat × Nat) :=
  let overlaps (region : Region) (other : Region) : Bool :=
    region.address < other.address + other.data.size && other.address < region.address + region.data.size
  let paired := saved.filterMap fun old =>
    (live.find? fun new => new.address == old.address && new.data.size == old.data.size).map (old, ·)
  let isPaired (region : Region) : Bool := paired.any fun (old, new) => old.address == region.address &&
    (old.data.size == region.data.size || new.data.size == region.data.size)
  let pages : List (Region × Region) := paired.flatMap fun (old, new) =>
    let starts := ((Jit.pieces old.data).map (·.1) ++ (Jit.pieces new.data).map (·.1)).eraseDups
    starts.filterMap fun offset =>
      let before := old.data.extract offset (offset + Jit.pieceSize)
      let after := new.data.extract offset (offset + Jit.pieceSize)
      if before == after then none
      else some (⟨old.address + offset, before, old.protection⟩, ⟨new.address + offset, after, new.protection⟩)
  let restSaved := saved.filter fun region => !isPaired region
  let restLive := live.filter fun region => !isPaired region
  let alone (region : Region) (others : List Region) : Bool := !others.any (overlaps region)
  let whole := (restSaved.filter fun region => alone region live).map (fun region => (region.address, region.data.size)) ++
    (restLive.filter fun region => alone region saved).map (fun region => (region.address, region.data.size))
  let mixedSaved := restSaved.filter fun region => !alone region live
  let mixedLive := restLive.filter fun region => !alone region saved
  mergeRanges (whole ++ diffRanges (pages.map (·.1) ++ mixedSaved) (pages.map (·.2) ++ mixedLive))

/-- The bytes of a region of a memory, which take the host what the memory has of them: its pages, filled into zeros. -/
private def bytesOfMemory {width : Nat} (memory : Bap.Memory width) (address size : Nat) : ByteArray :=
  let page := Bap.Memory.pageSize
  let pieces := memory.pages.foldl (init := []) fun pieces index bytes =>
    let start := index * page
    if start + page ≤ address || address + size ≤ start then pieces
    else if start ≥ address then (start - address, bytes.extract 0 (address + size - start)) :: pieces
    else (0, bytes.extract (address - start) page) :: pieces
  Jit.fill size pieces

/-- What changed since a snapshot was made in the space that it has, which may not be the one that runs: of the bytes that it has of its memory, which are those of the native memory of a space, or
else those of its state, which `restore` goes back to, rather than what the regions had the last time they were given them. -/
def diff (emu : Emu) (saved : Snapshot) : IO (List (Nat × Nat)) := do
  let regions := match saved.processMemory.lookup (snapshotSpace saved) with
    | some regions => regions
    | none => match Bil.lookup saved.state.env emu.config.memory with
      | .ok (.memory memory) =>
        saved.regions.map fun region => { region with data := bytesOfMemory memory region.address region.data.size }
      | _ => saved.regions
  -- Of the space that it has, whichever runs now.
  pure (diffRangesFast regions (← liveRegionsOf emu (snapshotSpace saved)))

def changedSince (emu : Emu) (path : String) : IO (List (Nat × Nat)) := do
  diff emu (← loadSnapshot emu path)

end Bap.Emu
