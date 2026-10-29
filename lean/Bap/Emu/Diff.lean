import Bap.Emu.Checkpoint

namespace Bap.Emu

private def byteAt (config : Config) (state : Bil.State) (regions : List Region) (address : Nat) : Option UInt8 := do
  let _ ← regions.find? fun region => region.contains address
  match Bil.lookup state.env config.memory with
  | .ok (@Value.memory width memory) => some (Bap.Memory.readByte memory (BitVec.ofNat width address))
  | _ => none

private def addresses (left right : List Region) : List Nat :=
  (left ++ right).flatMap (fun region => List.range (region.address + region.data.size) |>.drop region.address) |>.eraseDups

private def coalesce (changes : List Nat) : List (Nat × Nat) :=
  let sorted := changes.mergeSort (· ≤ ·)
  (sorted.foldl (init := []) fun ranges address =>
    match ranges with
    | (start, size) :: rest =>
      if start + size = address then (start, size + 1) :: rest else (address, 1) :: ranges
    | _ => (address, 1) :: ranges).reverse

def diff (emu : Emu) (saved : Snapshot) : IO (List (Nat × Nat)) := do
  let state ← emu.state.get
  let regions ← emu.regions.get
  let changes := (addresses saved.regions regions).filter fun address =>
    byteAt emu.config state regions address != byteAt emu.config saved.state saved.regions address
  pure (coalesce changes)

def changedSince (emu : Emu) (path : String) : IO (List (Nat × Nat)) := do
  let input ← IO.FS.readFile path
  match Sexp.parse input with
  | .error error => throw <| IO.userError error
  | .ok input =>
    match decodeSnapshot input with
    | .error error => throw <| IO.userError error
    | .ok saved => diff emu saved

end Bap.Emu
