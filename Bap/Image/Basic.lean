import Bap.Core.Types

namespace Bap.Image

inductive Arch where
  | x86
  | x86_64
  | arm
  | aarch64
  | mips
  | powerpc
  | riscv
  | systemz
  | unknown
  deriving DecidableEq, Repr

structure Section where
  name : String
  addr : Nat
  offset : Nat
  size : Nat
  flags : Nat
  kind : Nat
  deriving DecidableEq, Repr

structure Segment where
  name : String
  addr : Nat
  size : Nat
  readable : Bool
  writable : Bool
  executable : Bool
  deriving DecidableEq, Repr

structure Symbol where
  name : String
  addr : Nat
  size : Nat
  isFunction : Bool
  isDebug : Bool
  /-- An ARM function that runs in Thumb state: bit 0 of the value of its symbol, which `addr` doesn't have. -/
  thumb : Bool := false
  deriving DecidableEq, Repr

/-- The least multiple of `alignment` at or above `value`; an alignment of 0 or 1 asks for nothing. -/
def alignUp (value alignment : Nat) : Nat :=
  if alignment ≤ 1 then value else (value + alignment - 1) / alignment * alignment

/-- The section of a 1-based COFF, PE or Mach-O section number; number 0 means no section. -/
def sectionOfNumber (sections : List Section) : Nat → Option Section
  | 0 => none
  | number + 1 => sections[number]?

structure MemRegion where
  addr : Nat
  data : ByteArray
  readable : Bool := true
  writable : Bool := false
  executable : Bool := false
  deriving DecidableEq

namespace MemRegion

def size (region : MemRegion) : Nat := region.data.size
def maxAddr (region : MemRegion) : Nat := region.addr + region.size
def contains (region : MemRegion) (address : Nat) : Bool :=
  region.addr ≤ address && address < region.maxAddr

def readByte (region : MemRegion) (address : Nat) : Option UInt8 :=
  if region.contains address then some (region.data.get! (address - region.addr)) else none

@[simp] theorem contains_offset (region : MemRegion) (offset : Nat) (h : offset < region.size) :
    region.contains (region.addr + offset) = true := by
  simp [contains, maxAddr]
  omega

end MemRegion

structure MemoryMap (α : Type) where
  entries : List (MemRegion × α) := []

namespace MemoryMap

def empty : MemoryMap α := ⟨[]⟩
def add (region : MemRegion) (value : α) (map : MemoryMap α) : MemoryMap α :=
  ⟨ (region, value) :: map.entries ⟩

def lookup (map : MemoryMap α) (address : Nat) : List (MemRegion × α) :=
  map.entries.filter fun entry => entry.1.contains address

def contains (map : MemoryMap α) (address : Nat) : Bool := !(map.lookup address).isEmpty

def intersections (map : MemoryMap α) (region : MemRegion) : List (MemRegion × α) :=
  map.entries.filter fun entry => entry.1.addr < region.maxAddr && region.addr < entry.1.maxAddr

def removeIntersections (map : MemoryMap α) (region : MemRegion) : MemoryMap α :=
  ⟨ map.entries.filter fun entry => entry.1.maxAddr ≤ region.addr || region.maxAddr ≤ entry.1.addr ⟩

def mapValues (f : α → β) (map : MemoryMap α) : MemoryMap β :=
  ⟨ map.entries.map fun entry => (entry.1, f entry.2) ⟩

def readByte (map : MemoryMap α) (address : Nat) : Option UInt8 :=
  match map.lookup address with
  | (region, _) :: _ => region.readByte address
  | [] => none

end MemoryMap

structure Image where
  arch : Arch
  addrWidth : Nat
  endian : Endian
  entryPoint : Nat
  data : ByteArray
  sections : List Section := []
  segments : List Segment := []
  symbols : List Symbol := []
  memory : MemoryMap Unit := {}

/-- At most this many bytes of zeros past what a file has, of all its regions together: a header can say anything. -/
def zeroLimit : Nat := 2 ^ 32

/-- At most this many bytes of a file in all its regions together: each region is made of its own bytes, whatever of the file it is
of, and every header may say that it is of all of the file. Twice what the file has, and a megabyte, is more than regions that
share some of it take. -/
def fileLimit (data : ByteArray) : Nat := 2 * data.size + 2 ^ 20

/-- What the regions of a file take, all together: bytes of the file, each as often as a region has it, and zeros past them. -/
structure Extent where
  file : Nat := 0
  zeros : Nat := 0
  deriving DecidableEq, Repr

/-- With a region of `size` bytes, the first `fileSize` of them of the file. -/
def Extent.add (extent : Extent) (size fileSize : Nat) : Extent :=
  ⟨extent.file + min size fileSize, extent.zeros + (size - fileSize)⟩

/-- Whether regions take more than a host gives a file: more of it than `fileLimit`, or more zeros than `zeroLimit`. -/
def exceeds (data : ByteArray) (extent : Extent) : Bool :=
  extent.file > fileLimit data || extent.zeros > zeroLimit

/-- What a decoder says of a file whose regions `exceeds` is of. -/
def tooLarge : String := "the regions of the file are too large"

/-- At most this many bytes of names, of all the symbols or the sections of a file together, each as often as one of them has it:
every entry of a table may name a string as long as its string table, so that a file would cost the product of the two. What
`fileLimit` gives is more than names that share some of a table take. -/
def namesLimit (data : ByteArray) : Nat := fileLimit data

/-- What a decoder says of a file whose names take more than `namesLimit`. -/
def namesTooLarge : String := "the names of the file are too large"

/-- What the names read so far take with `bytes` more, which is an error past `namesLimit`. -/
def countNames (data : ByteArray) (used bytes : Nat) : Except String Nat :=
  if used + bytes > namesLimit data then .error namesTooLarge else .ok (used + bytes)

/-- What the names read so far take with another. -/
def countName (data : ByteArray) (used : Nat) (name : String) : Except String Nat :=
  countNames data used (name.utf8ByteSize + 1)

/-- What a name takes: its bytes and its zero. -/
def nameCost (name : String) : Nat := name.utf8ByteSize + 1

/-- `mapM` of what reads a name each, after names of `used` bytes: an error once they take more than `namesLimit`, with what they
take. What each took is `cost` of what was read of it. -/
def mapNamedM {α β : Type} (data : ByteArray) (cost : β → Nat) (read : α → Except String β) (items : List α)
    (used : Nat := 0) : Except String (List β × Nat) := do
  let (found, used) ← items.foldlM (init := ((#[] : Array β), used)) fun (found, used) item => do
    let value ← read item
    pure (found.push value, ← countNames data used (cost value))
  pure (found.toList, used)

structure Summary where
  arch : Arch
  addrWidth : Nat
  endian : Endian
  entryPoint : Nat
  sectionCount : Nat
  segmentCount : Nat
  symbolCount : Nat
  deriving Repr

def Image.summary (image : Image) : Summary := {
  arch := image.arch
  addrWidth := image.addrWidth
  endian := image.endian
  entryPoint := image.entryPoint
  sectionCount := image.sections.length
  segmentCount := image.segments.length
  symbolCount := image.symbols.length
}

end Bap.Image
