import Bap.Linux.Wire
import Std.Data.HashMap

/-! An allocator of memory of a guest for who runs it, and not for the guest: what it knows is all here, so that nothing a guest does to
its memory can confuse it. It doesn't call the `malloc` of a program, which needn't have one that can be found, and calling it would run
the guest. It is pure, and only says what to map and what to unmap. -/

namespace Bap.Linux

structure GuestHeap where
  /-- What is mapped for it: where, and how much. -/
  chunks : List (Nat × Nat) := []
  /-- What is free, by ascending address, of which no two touch. -/
  free : List (Nat × Nat) := []
  /-- What is given out: where, and how much it really has. -/
  used : List (Nat × Nat) := []
  deriving DecidableEq, Repr

namespace GuestHeap

/-- What a block starts on and is a multiple of, as `malloc` has it, for anything that a target has. -/
def alignment : Nat := 16

/-- How much of a guest it asks for at a time, as a mapping for each block would soon be a lot of them. -/
def chunkSize : Nat := 64 * 1024

/-- What a request comes to. One of nothing still has an address of its own. -/
def blockSize (size : Nat) : Nat := (max size 1 + alignment - 1) / alignment * alignment

/-- How much to map for a request that nothing free can take. -/
def mappingFor (size : Nat) : Nat := max chunkSize ((blockSize size + 4095) / 4096 * 4096)

/-- Takes a block from what is free: the first that is enough, and what is left of it stays free. -/
def alloc (heap : GuestHeap) (size : Nat) : Option (Nat × GuestHeap) :=
  let wanted := blockSize size
  let rec take : List (Nat × Nat) → Option (Nat × List (Nat × Nat))
    | [] => none
    | (address, available) :: rest =>
      if available ≥ wanted then
        some (address, if available == wanted then rest else (address + wanted, available - wanted) :: rest)
      else
        match take rest with
        | some (found, remaining) => some (found, (address, available) :: remaining)
        | none => none
  match take heap.free with
  | some (address, free) => some (address, { heap with free, used := (address, wanted) :: heap.used })
  | none => none

/-- A range back among what is free, in its place, joined with what it touches, but for where a mapping starts: mappings can be next to
each other, and a block is within one, so that each of them can be all free and go. -/
def insertFree (starts : List Nat) (free : List (Nat × Nat)) (range : Nat × Nat) : List (Nat × Nat) :=
  let joins (at_ : Nat) : Bool := !starts.contains at_
  match free with
  | [] => [range]
  | head :: rest =>
    if range.1 + range.2 == head.1 && joins head.1 then (range.1, range.2 + head.2) :: rest
    else if range.1 < head.1 then range :: free
    else if head.1 + head.2 == range.1 && joins range.1 then
      match rest with
      | next :: others =>
        if range.1 + range.2 == next.1 && joins next.1 then (head.1, head.2 + range.2 + next.2) :: others
        else (head.1, head.2 + range.2) :: rest
      | [] => [(head.1, head.2 + range.2)]
    else head :: insertFree starts rest range

/-- A mapping made for this heap. -/
def addChunk (heap : GuestHeap) (address size : Nat) : GuestHeap :=
  let chunks := heap.chunks ++ [(address, size)]
  { heap with chunks, free := insertFree (chunks.map (·.1)) heap.free (address, size) }

/-- A block goes back, if it is one, and says which chunk has nothing left in it, which has gone from the heap and can be unmapped. -/
def release (heap : GuestHeap) (address : Nat) : Option (GuestHeap × Option (Nat × Nat)) :=
  match heap.used.find? (·.1 == address) with
  | none => none
  | some block =>
    let free := insertFree (heap.chunks.map (·.1)) heap.free block
    let used := heap.used.filter (·.1 != address)
    match heap.chunks.find? (fun chunk => free.contains chunk) with
    | some chunk =>
      some ({ chunks := heap.chunks.filter (· != chunk), free := free.filter (· != chunk), used }, some chunk)
    | none => some ({ heap with free, used }, none)

/-- How much a block that was given out really has. -/
def sizeOf (heap : GuestHeap) (address : Nat) : Option Nat :=
  (heap.used.find? (·.1 == address)).map (·.2)

/-- A block comes to this size where it is, if it can: what it no longer needs is free, and what it needs more of has to be free right
after it, in the same mapping. -/
def resize (heap : GuestHeap) (address size : Nat) : Option GuestHeap := do
  let held ← heap.sizeOf address
  let wanted := blockSize size
  let others := heap.used.filter (·.1 != address)
  let starts := heap.chunks.map (·.1)
  if wanted == held then
    pure heap
  else if wanted < held then
    pure { heap with
      used := (address, wanted) :: others
      free := insertFree starts heap.free (address + wanted, held - wanted) }
  else
    let after := address + held
    if starts.contains after then none
    else
      let (taken, rest) := heap.free.partition (·.1 == after)
      let range ← taken.head?
      let needed := wanted - held
      if range.2 < needed then none
      else
        let remaining := if range.2 == needed then rest
          else insertFree starts rest (after + needed, range.2 - needed)
        pure { heap with used := (address, wanted) :: others, free := remaining }

/-- Without what is in a chunk that isn't there any more, as a program can unmap what it likes, and going back can undo a mapping. -/
def keepChunks (heap : GuestHeap) (mapped : Nat × Nat → Bool) : GuestHeap :=
  let chunks := heap.chunks.filter mapped
  let within (range : Nat × Nat) : Bool :=
    chunks.any fun chunk => chunk.1 ≤ range.1 && range.1 + range.2 ≤ chunk.1 + chunk.2
  { chunks, free := heap.free.filter within, used := heap.used.filter within }

open Wire in
private def putRange (out : ByteArray) (range : Nat × Nat) : ByteArray := putNat (putNat out range.1) range.2

open Wire in
private def getRange : Decoder (Nat × Nat) := fun data at_ => do
  let (first, at_) ← getNat data at_
  let (second, at_) ← getNat data at_
  .ok ((first, second), at_)

open Wire in
private def putEntry (out : ByteArray) (entry : Nat × GuestHeap) : ByteArray :=
  let out := putNat out entry.1
  let out := putList putRange out entry.2.chunks
  let out := putList putRange out entry.2.free
  -- As it was given out or not isn't anything that a program can tell.
  putSorted putRange out entry.2.used

open Wire in
private def getEntry : Decoder (Nat × GuestHeap) := fun data at_ => do
  let (space, at_) ← getNat data at_
  let (chunks, at_) ← getList getRange data at_
  let (free, at_) ← getList getRange data at_
  let (used, at_) ← getList getRange data at_
  .ok ((space, { chunks, free, used }), at_)

open Wire in
/-- The heaps of a machine, by address space. -/
def encode (heaps : Std.HashMap Nat GuestHeap) : ByteArray :=
  putSorted putEntry ByteArray.empty heaps.toList

open Wire in
def decode (data : ByteArray) : Except String (Std.HashMap Nat GuestHeap) := do
  let (entries, at_) ← getList getEntry data 0
  expectEnd data at_
  .ok (Std.HashMap.ofList entries)

end GuestHeap

end Bap.Linux
