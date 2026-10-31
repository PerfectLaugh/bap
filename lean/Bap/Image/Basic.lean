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
