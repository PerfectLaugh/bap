import Bap.Primus.Memory

namespace Bap.Primus

structure CellChange where
  address : BitVec 64
  oldValue : Option UInt8
  newValue : Option UInt8
  deriving Repr

structure Delta where
  cells : List CellChange := []
  regions : List Region := []

namespace Delta

private def lookup (cells : List (BitVec 64 × UInt8)) (address : BitVec 64) : Option UInt8 :=
  match cells.find? fun cell => cell.1 = address with
  | some cell => some cell.2
  | none => none

def diff (old new : Memory) : Delta :=
  let changed := (Bap.Memory.cells new.cells).filterMap fun cell =>
    let oldValue := lookup (Bap.Memory.cells old.cells) cell.1
    if oldValue = some cell.2 then none else some ⟨cell.1, oldValue, some cell.2⟩
  let deleted := (Bap.Memory.cells old.cells).filterMap fun cell =>
    if (lookup (Bap.Memory.cells new.cells) cell.1).isSome then none else some ⟨cell.1, some cell.2, none⟩
  { cells := changed ++ deleted, regions := new.regions }

private def applyCell (cells : Bap.Memory 64) (change : CellChange) : Bap.Memory 64 :=
  match change.newValue with
  | some value => Bap.Memory.writeByte cells change.address value
  | none => Bap.Memory.writeByte cells change.address 0

def apply (delta : Delta) (old : Memory) : Memory :=
  { cells := delta.cells.foldl applyCell old.cells, regions := delta.regions }

end Delta
end Bap.Primus
