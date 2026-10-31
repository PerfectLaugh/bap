import Bap.Core.Memory

namespace Bap.Primus

structure Protection where
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

structure Region where
  lower : Nat
  upper : Nat
  protection : Protection
  deriving DecidableEq, Repr

namespace Region

def contains (region : Region) (address : Nat) : Bool :=
  region.lower ≤ address && address < region.upper

end Region

inductive MemoryError where
  | unmapped (address : Nat)
  | readonly (address : Nat)
  | notExecutable (address : Nat)
  | overlap (lower upper : Nat)
  | outOfRange (lower upper : Nat)
  deriving Repr

structure Memory where
  cells : Bap.Memory 64
  regions : List Region := []

namespace Memory

def empty : Memory := ⟨Bap.Memory.empty 64, []⟩

/-- Cells are addressed by 64-bit words, so the address space ends here. -/
def addressLimit : Nat := 2 ^ 64

def protection (memory : Memory) (address : Nat) : Option Protection :=
  if address ≥ addressLimit then none else
  match memory.regions.find? fun region => region.contains address with
  | some region => some region.protection
  | none => none

def isMapped (memory : Memory) (address : Nat) : Bool := (memory.protection address).isSome

def addRegion (memory : Memory) (region : Region) : Except MemoryError Memory := do
  if region.upper > addressLimit then
    .error (.outOfRange region.lower region.upper)
  else if memory.regions.any fun old => old.lower < region.upper && region.lower < old.upper then
    .error (.overlap region.lower region.upper)
  else
    .ok { memory with regions := region :: memory.regions }

def map (memory : Memory) (address : Nat) (data : ByteArray) (protection : Protection) :
    Except MemoryError Memory := do
  let memory ← addRegion memory ⟨address, address + data.size, protection⟩
  let cells := (List.range data.size).foldl (init := memory.cells) fun cells index =>
    Bap.Memory.writeByte cells (BitVec.ofNat 64 (address + index)) (data.get! index)
  .ok { memory with cells := cells }

def loadByte (memory : Memory) (address : Nat) : Except MemoryError UInt8 := do
  match memory.protection address with
  | none => .error (.unmapped address)
  | some protection =>
    if !protection.readable then
      .error (.unmapped address)
    else
      .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address))

def storeByte (memory : Memory) (address : Nat) (value : UInt8) : Except MemoryError Memory := do
  match memory.protection address with
  | none => .error (.unmapped address)
  | some protection =>
    if !protection.writable then
      .error (.readonly address)
    else
      .ok { memory with cells := Bap.Memory.writeByte memory.cells (BitVec.ofNat 64 address) value }

def load (memory : Memory) (address : Nat) (endian : Endian) (size : Nat) :
    Except MemoryError (BitVec (size * 8)) := do
  let _ ← (List.range size).mapM fun offset => loadByte memory (address + offset)
  .ok (Bap.Memory.read memory.cells (BitVec.ofNat 64 address) endian size)

def store (memory : Memory) (address : Nat) (value : BitVec width) (endian : Endian) (size : Nat) :
    Except MemoryError Memory := do
  let _ ← (List.range size).mapM fun offset =>
    match memory.protection (address + offset) with
    | none => .error (.unmapped (address + offset))
    | some protection =>
      if !protection.writable then .error (.readonly (address + offset)) else .ok ()
  match Bap.Memory.write memory.cells (BitVec.ofNat 64 address) value endian size with
  | .ok cells => .ok { memory with cells := cells }
  | .error _ => .error (.unmapped address)

def fetch (memory : Memory) (address : Nat) : Except MemoryError UInt8 := do
  match memory.protection address with
  | some protection =>
    if !protection.executable then .error (.notExecutable address)
    else .ok (Bap.Memory.readByte memory.cells (BitVec.ofNat 64 address))
  | none => .error (.unmapped address)

/-- The pieces of `region` after protecting the bytes from `lower` to `upper`: the bytes outside of the
range keep their protection. -/
def splitRegion (lower upper : Nat) (protection : Protection) (region : Region) : List Region :=
  let first := max lower region.lower
  let last := min upper region.upper
  if last ≤ first then [region]
  else
    (if region.lower < first then [{ region with upper := first }] else []) ++
      [{ lower := first, upper := last, protection }] ++
      (if last < region.upper then [{ region with lower := last }] else [])

/-- `mprotect`: only the mapped bytes in the range change protection. -/
def protect (memory : Memory) (lower upper : Nat) (protection : Protection) : Memory :=
  { memory with regions := memory.regions.flatMap (splitRegion lower upper protection) }

abbrev Snapshot := Memory

def snapshot (memory : Memory) : Snapshot := memory
def restore (snapshot : Snapshot) (_memory : Memory) : Snapshot := snapshot

@[simp] theorem restore_snapshot (memory : Memory) : restore (snapshot memory) memory = memory := by
  rfl

end Memory
end Bap.Primus
